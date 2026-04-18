use std::{fmt, fs, io, sync::atomic::AtomicBool};

use camino::{Utf8Path, Utf8PathBuf};
use gix::bstr::ByteSlice as _;
use sha2::{Digest, Sha256};
use url::Url;

use crate::{ResolutionHandler, Resolver};

const FULL_CHECKOUT_MARKER: &str = "fe-resolver-full-checkout";
const SPARSE_CHECKOUT_MARKER: &str = "fe-resolver-sparse-checkout";

#[cfg(unix)]
use std::os::unix::io::AsRawFd as _;

#[cfg(windows)]
use std::os::windows::io::AsRawHandle as _;

#[cfg(windows)]
use windows_sys::Win32::Foundation::HANDLE;

#[cfg(windows)]
use windows_sys::Win32::Storage::FileSystem::{LOCKFILE_EXCLUSIVE_LOCK, LockFileEx};

#[cfg(windows)]
use windows_sys::Win32::System::IO::OVERLAPPED;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GitDescription {
    pub source: Url,
    pub rev: String,
    pub path: Option<Utf8PathBuf>,
}

impl GitDescription {
    pub fn new(source: Url, rev: impl Into<String>) -> Self {
        Self {
            source,
            rev: rev.into(),
            path: None,
        }
    }

    pub fn with_path(mut self, path: impl Into<Utf8PathBuf>) -> Self {
        self.path = Some(path.into());
        self
    }
}

impl fmt::Display for GitDescription {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.path {
            Some(path) => write!(f, "{}#{} ({})", self.source, self.rev, path),
            None => write!(f, "{}#{}", self.source, self.rev),
        }
    }
}

#[derive(Debug, Clone)]
pub struct GitResource {
    pub reused_checkout: bool,
    pub checkout_path: Utf8PathBuf,
}

#[derive(Debug)]
pub struct GitResolver {
    pub checkout_root: Utf8PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CheckoutCoverage {
    Full,
    Sparse(Utf8PathBuf),
}

impl CheckoutCoverage {
    fn from_requested_path(path: Option<&Utf8Path>) -> Result<Self, String> {
        match path {
            Some(path) => {
                let normalized = normalize_relative_path(path)?;
                if normalized.as_str().is_empty() {
                    Ok(Self::Full)
                } else {
                    Ok(Self::Sparse(normalized))
                }
            }
            None => Ok(Self::Full),
        }
    }

    fn from_repo(repo: &gix::Repository) -> Option<Self> {
        if repo.git_dir().join(FULL_CHECKOUT_MARKER).is_file() {
            return Some(Self::Full);
        }

        read_sparse_checkout_marker(repo).map(|root| Self::Sparse(Utf8PathBuf::from(root)))
    }

    fn sparse_path(&self) -> Option<&Utf8Path> {
        match self {
            Self::Full => None,
            Self::Sparse(path) => Some(path.as_path()),
        }
    }

    fn covers(&self, requested: &Self) -> bool {
        match (self, requested) {
            (Self::Full, _) => true,
            (Self::Sparse(_), Self::Full) => false,
            (Self::Sparse(current), Self::Sparse(requested)) => requested.starts_with(current),
        }
    }

    fn merge(&self, requested: &Self) -> Self {
        if self.covers(requested) {
            return self.clone();
        }
        if requested.covers(self) {
            return requested.clone();
        }

        match (self, requested) {
            (Self::Full, _) | (_, Self::Full) => Self::Full,
            (Self::Sparse(current), Self::Sparse(requested)) => {
                common_relative_root(current.as_path(), requested.as_path())
                    .map(Self::Sparse)
                    .unwrap_or(Self::Full)
            }
        }
    }
}

impl GitResolver {
    pub fn new(checkout_root: impl Into<Utf8PathBuf>) -> Self {
        Self {
            checkout_root: checkout_root.into(),
        }
    }

    pub fn has_valid_cached_checkout(&self, description: &GitDescription) -> bool {
        let checkout_path = self.checkout_path(description);
        if !checkout_path.exists() {
            return false;
        }
        let repo = match gix::open(checkout_path.as_std_path().to_path_buf()) {
            Ok(repo) => repo,
            Err(_) => return false,
        };
        let oid = match gix::ObjectId::from_hex(description.rev.as_bytes()) {
            Ok(oid) => oid,
            Err(_) => return false,
        };
        if !repo.has_object(oid) {
            return false;
        }

        match &description.path {
            Some(path) => {
                let normalized = match normalize_relative_path(path) {
                    Ok(normalized) => normalized,
                    Err(_) => return false,
                };
                if normalized.as_str().is_empty() {
                    return repo.git_dir().join(FULL_CHECKOUT_MARKER).is_file();
                }
                if !checkout_path.join(&normalized).is_dir() {
                    return false;
                }
                if repo.git_dir().join(FULL_CHECKOUT_MARKER).is_file() {
                    return true;
                }

                let Some(requested_root) = sparse_checkout_root_from_normalized(&normalized) else {
                    return false;
                };
                let Some(materialized_root) = read_sparse_checkout_marker(&repo) else {
                    return false;
                };

                requested_root == materialized_root
                    || requested_root.starts_with(&format!("{materialized_root}/"))
            }
            None => repo.git_dir().join(FULL_CHECKOUT_MARKER).is_file(),
        }
    }

    pub fn checkout_path(&self, description: &GitDescription) -> Utf8PathBuf {
        let mut hasher = Sha256::new();
        hasher.update(description.source.as_str().as_bytes());
        hasher.update(b"@");
        hasher.update(description.rev.as_bytes());
        let digest = hasher.finalize();
        let mut encoded = String::with_capacity(digest.len() * 2);
        for byte in digest {
            encoded.push_str(&format!("{byte:02x}"));
        }
        self.checkout_root.join(encoded)
    }

    pub fn ensure_checkout_resource(
        &self,
        description: &GitDescription,
    ) -> Result<GitResource, GitResolutionError> {
        self.ensure_checkout_root()?;
        let checkout_path = self.checkout_path(description);
        let status = self.ensure_checkout(description, &checkout_path)?;
        Ok(GitResource {
            reused_checkout: matches!(status, CheckoutStatus::Existing),
            checkout_path,
        })
    }

    fn ensure_checkout_root(&self) -> Result<(), GitResolutionError> {
        if !self.checkout_root.exists() {
            fs::create_dir_all(self.checkout_root.as_std_path()).map_err(|source| {
                GitResolutionError::PrepareCheckoutDirectory {
                    path: self.checkout_root.clone(),
                    source,
                }
            })?;
        }
        Ok(())
    }

    fn ensure_checkout(
        &self,
        description: &GitDescription,
        checkout_path: &Utf8Path,
    ) -> Result<CheckoutStatus, GitResolutionError> {
        let oid = gix::ObjectId::from_hex(description.rev.as_bytes()).map_err(|error| {
            GitResolutionError::InvalidRevision {
                rev: description.rev.clone(),
                error,
            }
        })?;
        let requested_coverage = CheckoutCoverage::from_requested_path(description.path.as_deref())
            .map_err(|error| GitResolutionError::Checkout {
                rev: oid.to_string(),
                error,
            })?;

        let _checkout_lock = CheckoutLock::acquire(checkout_path, &oid)?;

        if checkout_path.exists() {
            let mut repo = match gix::open(checkout_path.as_std_path().to_path_buf()) {
                Ok(repo) => repo,
                // If the cache is incomplete/corrupt, re-clone from scratch.
                Err(_) => {
                    if checkout_path.is_dir() {
                        fs::remove_dir_all(checkout_path.as_std_path()).map_err(|source| {
                            GitResolutionError::CleanupCheckoutDirectory {
                                path: checkout_path.to_owned(),
                                source,
                            }
                        })?;
                    } else {
                        fs::remove_file(checkout_path.as_std_path()).map_err(|source| {
                            GitResolutionError::CleanupCheckoutDirectory {
                                path: checkout_path.to_owned(),
                                source,
                            }
                        })?;
                    }
                    let mut repo = self.clone_repository(description, checkout_path)?;
                    self.checkout_revision(
                        &mut repo,
                        checkout_path,
                        &oid,
                        requested_coverage.sparse_path(),
                        /* destination_is_initially_empty */ true,
                    )?;
                    self.write_checkout_coverage_marker(
                        &repo,
                        requested_coverage.sparse_path(),
                        &oid,
                    )?;
                    return Ok(CheckoutStatus::Fresh);
                }
            };

            // If the cache is incomplete/corrupt, re-clone from scratch.
            if !repo.has_object(oid) {
                drop(repo);
                fs::remove_dir_all(checkout_path.as_std_path()).map_err(|source| {
                    GitResolutionError::CleanupCheckoutDirectory {
                        path: checkout_path.to_owned(),
                        source,
                    }
                })?;
                let mut repo = self.clone_repository(description, checkout_path)?;
                self.checkout_revision(
                    &mut repo,
                    checkout_path,
                    &oid,
                    requested_coverage.sparse_path(),
                    /* destination_is_initially_empty */ true,
                )?;
                self.write_checkout_coverage_marker(&repo, requested_coverage.sparse_path(), &oid)?;
                return Ok(CheckoutStatus::Fresh);
            }

            let current_coverage = CheckoutCoverage::from_repo(&repo);
            if self.has_valid_cached_checkout(description) {
                return Ok(CheckoutStatus::Existing);
            }

            let target_coverage = current_coverage
                .as_ref()
                .map(|current| current.merge(&requested_coverage))
                .unwrap_or_else(|| requested_coverage.clone());
            let destination_is_initially_empty = false;
            self.checkout_revision(
                &mut repo,
                checkout_path,
                &oid,
                target_coverage.sparse_path(),
                destination_is_initially_empty,
            )?;
            self.write_checkout_coverage_marker(&repo, target_coverage.sparse_path(), &oid)?;
            return Ok(CheckoutStatus::Existing);
        }

        if let Some(parent) = checkout_path.parent() {
            fs::create_dir_all(parent.as_std_path()).map_err(|source| {
                GitResolutionError::PrepareCheckoutDirectory {
                    path: parent.to_owned(),
                    source,
                }
            })?;
        }

        let mut repo = self.clone_repository(description, checkout_path)?;
        self.checkout_revision(
            &mut repo,
            checkout_path,
            &oid,
            requested_coverage.sparse_path(),
            /* destination_is_initially_empty */ true,
        )?;
        self.write_checkout_coverage_marker(&repo, requested_coverage.sparse_path(), &oid)?;
        Ok(CheckoutStatus::Fresh)
    }

    fn checkout_revision(
        &self,
        repo: &mut gix::Repository,
        checkout_path: &Utf8Path,
        oid: &gix::ObjectId,
        sparse_path: Option<&Utf8Path>,
        destination_is_initially_empty: bool,
    ) -> Result<(), GitResolutionError> {
        let commit =
            repo.find_commit(*oid)
                .map_err(|error| GitResolutionError::RevisionLookup {
                    rev: oid.to_string(),
                    error,
                })?;
        let tree_id = commit
            .tree_id()
            .map_err(|error| GitResolutionError::Checkout {
                rev: oid.to_string(),
                error: error.to_string(),
            })?;
        let mut index =
            repo.index_from_tree(&tree_id)
                .map_err(|error| GitResolutionError::Checkout {
                    rev: oid.to_string(),
                    error: error.to_string(),
                })?;

        if let Some(sparse_path) = sparse_path {
            let preserved_configs = sparse_checkout_ancestor_config_paths(sparse_path)
                .map_err(|message| GitResolutionError::Checkout {
                    rev: oid.to_string(),
                    error: message,
                })?
                .into_iter()
                .map(String::into_bytes)
                .collect::<Vec<_>>();
            if let Some(prefix) = sparse_checkout_prefix(sparse_path).map_err(|message| {
                GitResolutionError::Checkout {
                    rev: oid.to_string(),
                    error: message,
                }
            })? {
                let prefix = prefix.as_bytes().as_bstr();
                index.remove_entries(|_idx, path, _entry| {
                    !path.starts_with(prefix)
                        && !preserved_configs
                            .iter()
                            .any(|config_path| path == config_path.as_slice().as_bstr())
                });
            }
        } else {
            // Full checkouts are handled by leaving the index intact.
            let _ = checkout_path;
        }

        let workdir = repo.workdir().ok_or_else(|| GitResolutionError::Checkout {
            rev: oid.to_string(),
            error: "Bare repositories cannot be checked out".to_string(),
        })?;

        let objects =
            repo.objects
                .clone()
                .into_arc()
                .map_err(|error| GitResolutionError::Checkout {
                    rev: oid.to_string(),
                    error: error.to_string(),
                })?;

        let mut opts = repo
            .checkout_options(gix::worktree::stack::state::attributes::Source::IdMapping)
            .map_err(|error| GitResolutionError::Checkout {
                rev: oid.to_string(),
                error: error.to_string(),
            })?;
        opts.destination_is_initially_empty = destination_is_initially_empty;
        opts.overwrite_existing = true;

        let progress = gix::progress::Discard;
        let should_interrupt = AtomicBool::new(false);
        gix::worktree::state::checkout(
            &mut index,
            workdir,
            objects,
            &progress,
            &progress,
            &should_interrupt,
            opts,
        )
        .map_err(|error| GitResolutionError::Checkout {
            rev: oid.to_string(),
            error: error.to_string(),
        })?;

        index
            .write(Default::default())
            .map_err(|error| GitResolutionError::Checkout {
                rev: oid.to_string(),
                error: error.to_string(),
            })?;

        Ok(())
    }

    fn clone_repository(
        &self,
        description: &GitDescription,
        checkout_path: &Utf8Path,
    ) -> Result<gix::Repository, GitResolutionError> {
        let mut prepare = gix::clone::PrepareFetch::new(
            description.source.as_str(),
            checkout_path.as_std_path(),
            gix::create::Kind::WithWorktree,
            gix::create::Options::default(),
            gix::open::Options::default(),
        )
        .map_err(|error| GitResolutionError::CloneRepository {
            source: description.source.clone(),
            error: error.to_string(),
        })?;

        let progress = gix::progress::Discard;
        let should_interrupt = AtomicBool::new(false);
        let (repo, _outcome) =
            prepare
                .fetch_only(progress, &should_interrupt)
                .map_err(|error| GitResolutionError::CloneRepository {
                    source: description.source.clone(),
                    error: error.to_string(),
                })?;
        Ok(repo)
    }

    fn write_checkout_coverage_marker(
        &self,
        repo: &gix::Repository,
        sparse_path: Option<&Utf8Path>,
        oid: &gix::ObjectId,
    ) -> Result<(), GitResolutionError> {
        let full_marker = repo.git_dir().join(FULL_CHECKOUT_MARKER);
        let sparse_marker = repo.git_dir().join(SPARSE_CHECKOUT_MARKER);

        let sparse_root = sparse_path
            .map(sparse_checkout_root)
            .transpose()
            .map_err(|error| GitResolutionError::Checkout {
                rev: oid.to_string(),
                error,
            })?
            .flatten();

        match sparse_root {
            Some(root) => {
                remove_marker_if_exists(&full_marker).map_err(|source| {
                    GitResolutionError::PrepareCheckoutDirectory {
                        path: utf8_path_buf(&full_marker, &self.checkout_root),
                        source,
                    }
                })?;
                fs::write(&sparse_marker, root.as_bytes()).map_err(|source| {
                    GitResolutionError::PrepareCheckoutDirectory {
                        path: utf8_path_buf(&sparse_marker, &self.checkout_root),
                        source,
                    }
                })?;
            }
            None => {
                remove_marker_if_exists(&sparse_marker).map_err(|source| {
                    GitResolutionError::PrepareCheckoutDirectory {
                        path: utf8_path_buf(&sparse_marker, &self.checkout_root),
                        source,
                    }
                })?;
                fs::write(&full_marker, b"").map_err(|source| {
                    GitResolutionError::PrepareCheckoutDirectory {
                        path: utf8_path_buf(&full_marker, &self.checkout_root),
                        source,
                    }
                })?;
            }
        }

        Ok(())
    }
}

#[derive(Debug)]
struct CheckoutLock {
    _file: fs::File,
}

impl CheckoutLock {
    fn acquire(checkout_path: &Utf8Path, oid: &gix::ObjectId) -> Result<Self, GitResolutionError> {
        let lock_path = checkout_path.with_extension("lock");
        let file = fs::OpenOptions::new()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(lock_path.as_std_path())
            .map_err(|source| GitResolutionError::PrepareCheckoutDirectory {
                path: lock_path.clone(),
                source,
            })?;

        lock_file_exclusive(&file).map_err(|error| GitResolutionError::Checkout {
            rev: oid.to_string(),
            error: format!("Failed to acquire checkout lock {lock_path}: {error}"),
        })?;

        Ok(Self { _file: file })
    }
}

#[cfg(unix)]
fn lock_file_exclusive(file: &fs::File) -> io::Result<()> {
    let fd = file.as_raw_fd();
    let res = unsafe { libc::flock(fd, libc::LOCK_EX) };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(windows)]
fn lock_file_exclusive(file: &fs::File) -> io::Result<()> {
    let handle = file.as_raw_handle() as HANDLE;
    let mut overlapped: OVERLAPPED = unsafe { std::mem::zeroed() };
    let res = unsafe { LockFileEx(handle, LOCKFILE_EXCLUSIVE_LOCK, 0, 1, 0, &mut overlapped) };
    if res == 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

enum CheckoutStatus {
    Fresh,
    Existing,
}

#[derive(Debug, Clone)]
pub enum GitResolutionEvent {
    CheckoutStart {
        description: GitDescription,
    },
    CheckoutComplete {
        description: GitDescription,
        checkout_path: Utf8PathBuf,
        reused_checkout: bool,
    },
}

impl Resolver for GitResolver {
    type Description = GitDescription;
    type Resource = GitResource;
    type Error = GitResolutionError;
    type Diagnostic = GitResolutionDiagnostic;
    type Event = GitResolutionEvent;

    fn resolve<H>(
        &mut self,
        handler: &mut H,
        description: &Self::Description,
    ) -> Result<H::Item, Self::Error>
    where
        H: ResolutionHandler<Self>,
    {
        handler.on_resolution_event(GitResolutionEvent::CheckoutStart {
            description: description.clone(),
        });
        let resource = self.ensure_checkout_resource(description)?;
        handler.on_resolution_event(GitResolutionEvent::CheckoutComplete {
            description: description.clone(),
            checkout_path: resource.checkout_path.clone(),
            reused_checkout: resource.reused_checkout,
        });
        Ok(handler.handle_resolution(description, resource))
    }
}

#[derive(Debug)]
pub enum GitResolutionError {
    PrepareCheckoutDirectory {
        path: Utf8PathBuf,
        source: io::Error,
    },
    CleanupCheckoutDirectory {
        path: Utf8PathBuf,
        source: io::Error,
    },
    CloneRepository {
        source: Url,
        error: String,
    },
    OpenRepository {
        path: Utf8PathBuf,
        error: Box<gix::open::Error>,
    },
    InvalidRevision {
        rev: String,
        error: gix::hash::decode::Error,
    },
    RevisionLookup {
        rev: String,
        error: gix::object::find::existing::with_conversion::Error,
    },
    Checkout {
        rev: String,
        error: String,
    },
}

impl fmt::Display for GitResolutionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GitResolutionError::PrepareCheckoutDirectory { path, source } => {
                write!(f, "Failed to prepare checkout directory {}: {source}", path)
            }
            GitResolutionError::CleanupCheckoutDirectory { path, source } => {
                write!(f, "Failed to clean checkout directory {}: {source}", path)
            }
            GitResolutionError::CloneRepository { source, error } => {
                write!(f, "Failed to clone repository {source}: {error}")
            }
            GitResolutionError::OpenRepository { path, error } => {
                write!(f, "Failed to open existing checkout at {}: {error}", path)
            }
            GitResolutionError::InvalidRevision { rev, error } => write!(
                f,
                "Revision '{rev}' is not a valid commit identifier: {error}"
            ),
            GitResolutionError::RevisionLookup { rev, error } => {
                write!(
                    f,
                    "Revision '{rev}' was not found in the repository: {error}"
                )
            }
            GitResolutionError::Checkout { rev, error } => {
                write!(f, "Failed to checkout revision '{rev}': {error}")
            }
        }
    }
}

impl std::error::Error for GitResolutionError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            GitResolutionError::PrepareCheckoutDirectory { source, .. } => Some(source),
            GitResolutionError::CleanupCheckoutDirectory { source, .. } => Some(source),
            GitResolutionError::CloneRepository { .. } => None,
            GitResolutionError::OpenRepository { error, .. } => Some(error),
            GitResolutionError::InvalidRevision { error, .. } => Some(error),
            GitResolutionError::RevisionLookup { error, .. } => Some(error),
            GitResolutionError::Checkout { .. } => None,
        }
    }
}

#[derive(Debug)]
pub enum GitResolutionDiagnostic {}

impl fmt::Display for GitResolutionDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let _ = f;
        unreachable!("GitResolutionDiagnostic has no variants")
    }
}

fn normalize_relative_path(path: &Utf8Path) -> Result<Utf8PathBuf, String> {
    let mut normalized = Vec::new();
    for component in path.components() {
        match component {
            camino::Utf8Component::CurDir => {}
            camino::Utf8Component::ParentDir => {
                if normalized.pop().is_none() {
                    return Err("sparse checkout path escapes repository root".to_string());
                }
            }
            camino::Utf8Component::RootDir | camino::Utf8Component::Prefix(_) => {
                return Err("sparse checkout path must be relative".to_string());
            }
            camino::Utf8Component::Normal(segment) => normalized.push(segment),
        }
    }
    Ok(Utf8PathBuf::from(normalized.join("/")))
}

fn common_relative_root(a: &Utf8Path, b: &Utf8Path) -> Option<Utf8PathBuf> {
    let mut root = Utf8PathBuf::new();
    for (left, right) in a.iter().zip(b.iter()) {
        if left != right {
            break;
        }
        root.push(left);
    }
    (!root.as_str().is_empty()).then_some(root)
}

fn repo_relative_path_string(path: &Utf8Path) -> String {
    path.iter().collect::<Vec<_>>().join("/")
}

fn sparse_checkout_ancestor_config_paths(path: &Utf8Path) -> Result<Vec<String>, String> {
    let normalized = normalize_relative_path(path)?;
    let mut configs = vec!["fe.toml".to_string()];
    let mut ancestor = Utf8PathBuf::new();
    let mut components = normalized.iter().peekable();
    while let Some(component) = components.next() {
        if components.peek().is_none() {
            break;
        }
        ancestor.push(component);
        configs.push(format!(
            "{}/fe.toml",
            repo_relative_path_string(ancestor.as_path())
        ));
    }
    Ok(configs)
}

fn sparse_checkout_root(path: &Utf8Path) -> Result<Option<String>, String> {
    let normalized = normalize_relative_path(path)?;
    Ok(sparse_checkout_root_from_normalized(&normalized))
}

fn sparse_checkout_root_from_normalized(path: &Utf8Path) -> Option<String> {
    (!path.as_str().is_empty()).then(|| repo_relative_path_string(path))
}

fn sparse_checkout_prefix(path: &Utf8Path) -> Result<Option<String>, String> {
    let Some(mut prefix) = sparse_checkout_root(path)? else {
        return Ok(None);
    };
    prefix.push('/');
    Ok(Some(prefix))
}

fn read_sparse_checkout_marker(repo: &gix::Repository) -> Option<String> {
    let marker = repo.git_dir().join(SPARSE_CHECKOUT_MARKER);
    let root = fs::read_to_string(marker).ok()?;
    let root = root.trim();
    (!root.is_empty()).then(|| root.to_owned())
}

fn remove_marker_if_exists(path: &std::path::Path) -> io::Result<()> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(error),
    }
}

fn utf8_path_buf(path: &std::path::Path, fallback: &Utf8Path) -> Utf8PathBuf {
    Utf8PathBuf::from_path_buf(path.to_path_buf()).unwrap_or_else(|_| fallback.to_owned())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ResolutionHandler, Resolver};
    use std::process::Command;

    struct EchoHandler;

    impl ResolutionHandler<GitResolver> for EchoHandler {
        type Item = GitResource;

        fn handle_resolution(
            &mut self,
            _description: &GitDescription,
            resource: GitResource,
        ) -> Self::Item {
            resource
        }
    }

    fn git(repo: &Utf8Path, args: &[&str]) {
        let status = Command::new("git")
            .arg("-C")
            .arg(repo.as_std_path())
            .args(args)
            .status()
            .expect("git command");
        assert!(status.success(), "git command failed: {:?}", args);
    }

    fn git_output(repo: &Utf8Path, args: &[&str]) -> String {
        let output = Command::new("git")
            .arg("-C")
            .arg(repo.as_std_path())
            .args(args)
            .output()
            .expect("git output");
        assert!(output.status.success(), "git output failed: {:?}", args);
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }

    fn git_commit(repo: &Utf8Path, message: &str) -> String {
        git(repo, &["add", "."]);
        git(repo, &["commit", "-m", message]);
        git_output(repo, &["rev-parse", "HEAD"])
    }

    #[test]
    fn full_checkout_creates_marker_and_materializes_root() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);
        let description = GitDescription::new(source, rev);
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &description)
            .expect("resolve");

        assert!(resource.checkout_path.join("root.txt").is_file());
        assert!(resolver.has_valid_cached_checkout(&description));
    }

    #[test]
    fn sparse_checkout_only_materializes_requested_subdir_until_full_requested() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("ingots/core").as_std_path()).unwrap();
        fs::write(
            remote_repo.join("ingots/core/fe.toml").as_std_path(),
            "[ingot]\nname=\"core\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let sparse = GitDescription::new(source.clone(), rev.clone()).with_path("ingots/core");
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &sparse)
            .expect("resolve sparse");
        assert!(resource.checkout_path.join("ingots/core/fe.toml").is_file());
        assert!(!resource.checkout_path.join("root.txt").is_file());
        assert!(resolver.has_valid_cached_checkout(&sparse));

        // Requesting a full checkout should materialize the root file.
        let full = GitDescription::new(source, rev);
        assert!(!resolver.has_valid_cached_checkout(&full));
        let mut handler = EchoHandler;
        let resource = resolver.resolve(&mut handler, &full).expect("resolve full");
        assert!(resource.checkout_path.join("root.txt").is_file());
        assert!(resolver.has_valid_cached_checkout(&full));
        assert!(resolver.has_valid_cached_checkout(&sparse));
    }

    #[test]
    fn widened_sparse_request_is_not_treated_as_cached() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("workspace/ingots/core").as_std_path()).unwrap();
        fs::write(
            remote_repo.join("workspace/fe.toml").as_std_path(),
            "[workspace]\nmembers = [\"ingots/*\"]\n",
        )
        .unwrap();
        fs::write(
            remote_repo
                .join("workspace/ingots/core/fe.toml")
                .as_std_path(),
            "[ingot]\nname=\"core\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let nested =
            GitDescription::new(source.clone(), rev.clone()).with_path("workspace/ingots/core");
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &nested)
            .expect("resolve nested sparse");
        assert!(
            resource
                .checkout_path
                .join("workspace/ingots/core/fe.toml")
                .is_file()
        );
        assert!(resource.checkout_path.join("workspace/fe.toml").is_file());
        assert!(resolver.has_valid_cached_checkout(&nested));

        let widened = GitDescription::new(source, rev).with_path("workspace");
        assert!(!resolver.has_valid_cached_checkout(&widened));

        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &widened)
            .expect("resolve widened sparse");
        assert!(resource.checkout_path.join("workspace/fe.toml").is_file());
        assert!(resolver.has_valid_cached_checkout(&widened));
        assert!(resolver.has_valid_cached_checkout(&nested));
    }

    #[test]
    fn sparse_checkout_preserves_ancestor_workspace_configs() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("workspace/ingots/core").as_std_path()).unwrap();
        fs::write(
            remote_repo.join("workspace/fe.toml").as_std_path(),
            "name = \"workspace\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        fs::write(
            remote_repo
                .join("workspace/ingots/core/fe.toml")
                .as_std_path(),
            "[ingot]\nname=\"core\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        fs::write(
            remote_repo.join("workspace/outside.txt").as_std_path(),
            "outside\n",
        )
        .unwrap();
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let sparse = GitDescription::new(source, rev).with_path("workspace/ingots/core");
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &sparse)
            .expect("resolve sparse");

        assert!(
            resource
                .checkout_path
                .join("workspace/ingots/core/fe.toml")
                .is_file()
        );
        assert!(resource.checkout_path.join("workspace/fe.toml").is_file());
        assert!(
            !resource
                .checkout_path
                .join("workspace/outside.txt")
                .is_file()
        );
        assert!(!resource.checkout_path.join("root.txt").is_file());
        assert!(resolver.has_valid_cached_checkout(&sparse));
    }

    #[test]
    fn sibling_sparse_requests_do_not_invalidate_each_other() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("ingots/core").as_std_path()).unwrap();
        fs::create_dir_all(remote_repo.join("ingots/utils").as_std_path()).unwrap();
        fs::write(
            remote_repo.join("ingots/core/fe.toml").as_std_path(),
            "[ingot]\nname=\"core\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        fs::write(
            remote_repo.join("ingots/utils/fe.toml").as_std_path(),
            "[ingot]\nname=\"utils\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let core = GitDescription::new(source.clone(), rev.clone()).with_path("ingots/core");
        let utils = GitDescription::new(source, rev).with_path("ingots/utils");

        let mut handler = EchoHandler;
        let core_resource = resolver.resolve(&mut handler, &core).expect("resolve core");
        assert!(
            core_resource
                .checkout_path
                .join("ingots/core/fe.toml")
                .is_file()
        );
        assert!(resolver.has_valid_cached_checkout(&core));

        let mut handler = EchoHandler;
        let utils_resource = resolver
            .resolve(&mut handler, &utils)
            .expect("resolve utils");
        assert!(
            utils_resource
                .checkout_path
                .join("ingots/utils/fe.toml")
                .is_file()
        );

        assert!(
            resolver.has_valid_cached_checkout(&core),
            "resolving a sibling sparse path should not invalidate an existing checkout"
        );
        assert!(
            resolver.has_valid_cached_checkout(&utils),
            "the newly resolved sparse path should remain cached"
        );
        assert!(
            core_resource
                .checkout_path
                .join("ingots/core/fe.toml")
                .is_file()
        );
        assert!(
            utils_resource
                .checkout_path
                .join("ingots/utils/fe.toml")
                .is_file()
        );
    }

    #[test]
    fn full_checkout_remains_valid_after_later_sparse_request() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("ingots/core").as_std_path()).unwrap();
        fs::write(
            remote_repo.join("ingots/core/fe.toml").as_std_path(),
            "[ingot]\nname=\"core\"\nversion=\"0.1.0\"\n",
        )
        .unwrap();
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let full = GitDescription::new(source.clone(), rev.clone());
        let mut handler = EchoHandler;
        resolver.resolve(&mut handler, &full).expect("resolve full");
        assert!(resolver.has_valid_cached_checkout(&full));

        let sparse = GitDescription::new(source, rev).with_path("ingots/core");
        assert!(resolver.has_valid_cached_checkout(&sparse));
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &sparse)
            .expect("resolve sparse");
        assert!(resource.checkout_path.join("ingots/core/fe.toml").is_file());
        assert!(resource.checkout_path.join("root.txt").is_file());
        assert!(resolver.has_valid_cached_checkout(&full));
        assert!(resolver.has_valid_cached_checkout(&sparse));
    }

    #[test]
    fn reuses_existing_checkout() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let resolver = GitResolver::new(checkout_root);
        let description = GitDescription::new(source, rev);

        let first = resolver
            .ensure_checkout_resource(&description)
            .expect("first checkout");
        assert!(!first.reused_checkout);
        let second = resolver
            .ensure_checkout_resource(&description)
            .expect("second checkout");
        assert!(second.reused_checkout);
    }

    #[test]
    fn rejects_invalid_revision() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let source = Url::parse("file:///tmp/does-not-matter").unwrap();
        let resolver = GitResolver::new(root.join("cache"));
        let description = GitDescription::new(source, "not-a-rev");
        let err = resolver
            .ensure_checkout_resource(&description)
            .expect_err("invalid rev");
        assert!(matches!(err, GitResolutionError::InvalidRevision { .. }));
    }

    #[test]
    fn sparse_checkout_prefix_uses_repo_separators() {
        let mut path = Utf8PathBuf::new();
        path.push("ingots");
        path.push("core");

        assert_eq!(
            sparse_checkout_prefix(path.as_path()).unwrap(),
            Some("ingots/core/".to_string())
        );
    }

    #[test]
    fn sparse_checkout_ancestor_configs_use_repo_separators() {
        let mut path = Utf8PathBuf::new();
        path.push("workspace");
        path.push("ingots");
        path.push("core");

        assert_eq!(
            sparse_checkout_ancestor_config_paths(path.as_path()).unwrap(),
            vec![
                "fe.toml".to_string(),
                "workspace/fe.toml".to_string(),
                "workspace/ingots/fe.toml".to_string(),
            ]
        );
    }

    #[test]
    fn normalize_relative_path_rejects_absolute_paths() {
        let err = normalize_relative_path(Utf8Path::new("/abs")).expect_err("absolute path");
        assert!(
            err.contains("must be relative"),
            "unexpected error message: {err}"
        );
    }

    #[test]
    fn normalize_relative_path_removes_dots_and_collapses_parents() {
        let normalized = normalize_relative_path(Utf8Path::new("a/./b/../c")).expect("normalized");
        assert_eq!(normalized.as_str(), "a/c");
    }

    #[test]
    fn empty_path_is_treated_like_full_checkout_request() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let full = GitDescription::new(source.clone(), rev.clone());
        let mut handler = EchoHandler;
        resolver.resolve(&mut handler, &full).expect("resolve full");
        assert!(resolver.has_valid_cached_checkout(&full));

        let empty = GitDescription::new(source, rev).with_path("");
        assert!(
            resolver.has_valid_cached_checkout(&empty),
            "empty paths should behave like a full checkout request"
        );
    }

    #[test]
    fn reclones_when_existing_checkout_does_not_contain_requested_object() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let resolver = GitResolver::new(checkout_root);
        let description = GitDescription::new(source, rev);
        let checkout_path = resolver.checkout_path(&description);

        fs::create_dir_all(checkout_path.as_std_path()).unwrap();
        git(&checkout_path, &["init"]);
        fs::write(checkout_path.join("corrupt.txt").as_std_path(), "corrupt\n").unwrap();

        let resource = resolver
            .ensure_checkout_resource(&description)
            .expect("resolve after corruption");
        assert!(resource.checkout_path.join("root.txt").is_file());
        assert!(
            !resource.checkout_path.join("corrupt.txt").exists(),
            "expected reclone to replace the checkout contents"
        );
    }

    #[test]
    fn rejects_sparse_checkout_paths_that_escape_repository_root() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let resolver = GitResolver::new(checkout_root);
        let description = GitDescription::new(source, rev).with_path("../escape");

        let err = resolver
            .ensure_checkout_resource(&description)
            .expect_err("expected invalid sparse checkout path error");
        match err {
            GitResolutionError::Checkout { error, .. } => assert!(
                error.contains("escapes repository root"),
                "unexpected error message: {error}"
            ),
            other => panic!("expected checkout error, got {other:?}"),
        }
    }

    #[test]
    fn disjoint_sparse_requests_widen_to_full_checkout() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::create_dir_all(remote_repo.join("a").as_std_path()).unwrap();
        fs::create_dir_all(remote_repo.join("b").as_std_path()).unwrap();
        fs::write(remote_repo.join("a/a.txt").as_std_path(), "a\n").unwrap();
        fs::write(remote_repo.join("b/b.txt").as_std_path(), "b\n").unwrap();
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let sparse_a = GitDescription::new(source.clone(), rev.clone()).with_path("a");
        let sparse_b = GitDescription::new(source.clone(), rev.clone()).with_path("b");
        let full = GitDescription::new(source, rev);

        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &sparse_a)
            .expect("resolve sparse a");
        assert!(resource.checkout_path.join("a/a.txt").is_file());
        assert!(!resource.checkout_path.join("root.txt").is_file());

        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &sparse_b)
            .expect("resolve sparse b");
        assert!(
            resource.checkout_path.join("root.txt").is_file(),
            "expected checkout to widen to a full checkout"
        );
        assert!(resource.checkout_path.join("a/a.txt").is_file());
        assert!(resource.checkout_path.join("b/b.txt").is_file());

        assert!(resolver.has_valid_cached_checkout(&full));
        assert!(resolver.has_valid_cached_checkout(&sparse_a));
        assert!(resolver.has_valid_cached_checkout(&sparse_b));
    }

    #[test]
    fn checks_out_non_head_commit_in_history() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);

        fs::write(remote_repo.join("root.txt").as_std_path(), "v1\n").unwrap();
        let rev1 = git_commit(&remote_repo, "v1");

        fs::write(remote_repo.join("root.txt").as_std_path(), "v2\n").unwrap();
        let _rev2 = git_commit(&remote_repo, "v2");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let mut resolver = GitResolver::new(checkout_root);

        let description = GitDescription::new(source, rev1);
        let mut handler = EchoHandler;
        let resource = resolver
            .resolve(&mut handler, &description)
            .expect("resolve");
        let content = fs::read_to_string(resource.checkout_path.join("root.txt").as_std_path())
            .expect("read root.txt");
        assert_eq!(content.replace("\r\n", "\n"), "v1\n");
        assert!(resolver.has_valid_cached_checkout(&description));
    }

    #[test]
    fn reclones_when_existing_checkout_is_not_a_git_repository() {
        let temp = tempfile::tempdir().expect("tempdir");
        let root = Utf8PathBuf::from_path_buf(temp.path().to_path_buf()).unwrap();
        let remote_repo = root.join("remote");
        fs::create_dir_all(remote_repo.as_std_path()).unwrap();

        git(&remote_repo, &["init"]);
        git(&remote_repo, &["config", "user.email", "fe@example.com"]);
        git(&remote_repo, &["config", "user.name", "fe"]);
        fs::write(remote_repo.join("root.txt").as_std_path(), "root\n").unwrap();
        let rev = git_commit(&remote_repo, "initial");

        let source = Url::from_directory_path(remote_repo.as_std_path()).unwrap();
        let checkout_root = root.join("cache");
        let resolver = GitResolver::new(checkout_root);
        let description = GitDescription::new(source, rev);
        let checkout_path = resolver.checkout_path(&description);

        fs::create_dir_all(checkout_path.as_std_path()).unwrap();
        fs::write(checkout_path.join("corrupt.txt").as_std_path(), "corrupt\n").unwrap();

        let resource = resolver
            .ensure_checkout_resource(&description)
            .expect("resolve after corruption");
        assert!(!resource.reused_checkout);
        assert!(resource.checkout_path.join("root.txt").is_file());
        assert!(
            !resource.checkout_path.join("corrupt.txt").exists(),
            "expected reclone to replace the checkout contents"
        );
    }
}
