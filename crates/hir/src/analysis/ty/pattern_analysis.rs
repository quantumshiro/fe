//! Pattern matching analysis for exhaustiveness and reachability checking
//! Based on "Warnings for pattern matching" by Luc Maranget

use common::indexmap::IndexSet;

use crate::analysis::HirAnalysisDb;
use crate::analysis::ty::AdtRef;
use crate::analysis::ty::pattern_ir::{
    BindingRef, ConstructorKind, PatternStore, ValidatedPatId, ValidatedPatKind, ctor_variant_num,
};
use crate::analysis::ty::ty_def::TyId;
use crate::core::hir_def::LitKind;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternMatrix<'db> {
    pub rows: Vec<PatternRowVec<'db>>,
}

impl<'db> PatternMatrix<'db> {
    pub(crate) fn new(rows: Vec<PatternRowVec<'db>>) -> Self {
        Self { rows }
    }

    pub fn from_roots(store: &PatternStore<'db>, roots: &[ValidatedPatId]) -> Self {
        let rows = roots
            .iter()
            .copied()
            .map(|root| PatternRowVec::new(vec![MatrixPat::from_root(store, root)]))
            .collect();
        Self { rows }
    }

    pub fn push_wildcard_row(&mut self, ty: TyId<'db>) {
        self.rows
            .push(PatternRowVec::new(vec![MatrixPat::wildcard(None, ty)]));
    }

    fn find_missing_patterns(&self, db: &'db dyn HirAnalysisDb) -> Option<Vec<MatrixPat<'db>>> {
        if self.nrows() == 0 {
            return Some(Vec::new());
        }
        if self.ncols() == 0 {
            return None;
        }

        let ty = self.first_column_ty();
        let sigma_set = self.sigma_set();

        if sigma_set.is_complete(db) {
            for ctor in sigma_set {
                let specialized = self.phi_specialize(db, ctor);

                match specialized.find_missing_patterns(db) {
                    Some(vec) if vec.is_empty() => {
                        let fields = ctor
                            .field_types(db)
                            .into_iter()
                            .map(|field_ty| MatrixPat::wildcard(None, field_ty))
                            .collect();
                        return Some(vec![MatrixPat::constructor(ctor, fields, ty)]);
                    }
                    Some(mut vec) => {
                        let field_num = ctor.arity(db);
                        let remaining_patterns = if vec.len() >= field_num {
                            vec.split_off(field_num)
                        } else {
                            let field_types = ctor.field_types(db);
                            while vec.len() < field_num {
                                let field_ty = field_types
                                    .get(vec.len())
                                    .copied()
                                    .unwrap_or_else(|| field_types[0]);
                                vec.push(MatrixPat::wildcard(None, field_ty));
                            }
                            Vec::new()
                        };

                        let pat = MatrixPat::constructor(ctor, vec, ty);
                        let mut result = vec![pat];
                        result.extend_from_slice(&remaining_patterns);
                        return Some(result);
                    }
                    None => {}
                }
            }

            None
        } else {
            self.d_specialize().find_missing_patterns(db).map(|vec| {
                let sigma_set = self.sigma_set();
                let kind = if sigma_set.is_empty() {
                    MatrixPatKind::WildCard(None)
                } else {
                    let complete_sigma = SigmaSet::complete_sigma(db, ty);
                    MatrixPatKind::Or(
                        complete_sigma
                            .difference(&sigma_set)
                            .map(|ctor| MatrixPat::ctor_with_wild_card_fields(db, *ctor, ty))
                            .collect(),
                    )
                };

                let mut result = vec![MatrixPat::new(kind, ty)];
                result.extend_from_slice(&vec);
                result
            })
        }
    }

    pub fn is_row_useful(&self, db: &'db dyn HirAnalysisDb, row: usize) -> bool {
        debug_assert!(self.nrows() > row);
        if row == 0 {
            return true;
        }

        let previous = PatternMatrix {
            rows: self.rows[0..row].to_vec(),
        };
        previous.is_pattern_useful(db, &self.rows[row])
    }

    fn is_pattern_useful(&self, db: &'db dyn HirAnalysisDb, pat_vec: &PatternRowVec<'db>) -> bool {
        if self.nrows() == 0 {
            return true;
        }
        if pat_vec.is_empty() || self.ncols() == 0 {
            return false;
        }

        match &pat_vec.head().unwrap().kind {
            MatrixPatKind::WildCard(_) => {
                let d_specialized = pat_vec.d_specialize();
                if d_specialized.is_empty() {
                    false
                } else {
                    self.d_specialize().is_pattern_useful(db, &d_specialized[0])
                }
            }
            MatrixPatKind::Constructor { kind, .. } => {
                let phi_specialized = pat_vec.phi_specialize(db, *kind);
                if phi_specialized.is_empty() {
                    false
                } else {
                    self.phi_specialize(db, *kind)
                        .is_pattern_useful(db, &phi_specialized[0])
                }
            }
            MatrixPatKind::Or(pats) => pats.iter().any(|pat| {
                let mut expanded = Vec::with_capacity(pat_vec.len());
                expanded.push(pat.clone());
                expanded.extend_from_slice(&pat_vec.inner[1..]);
                self.is_pattern_useful(db, &PatternRowVec::new(expanded))
            }),
        }
    }

    pub fn phi_specialize(&self, db: &'db dyn HirAnalysisDb, ctor: ConstructorKind<'db>) -> Self {
        let rows = self
            .rows
            .iter()
            .flat_map(|row| row.phi_specialize(db, ctor))
            .collect();
        Self::new(rows)
    }

    pub fn d_specialize(&self) -> Self {
        let rows = self
            .rows
            .iter()
            .flat_map(PatternRowVec::d_specialize)
            .collect();
        Self::new(rows)
    }

    pub fn sigma_set(&self) -> SigmaSet<'db> {
        SigmaSet::from_rows(self.rows.iter(), 0)
    }

    pub fn first_column_ty(&self) -> TyId<'db> {
        self.rows[0].first_column_ty()
    }

    pub fn nrows(&self) -> usize {
        self.rows.len()
    }

    pub fn ncols(&self) -> usize {
        if self.nrows() == 0 {
            0
        } else {
            let ncols = self.rows[0].len();
            debug_assert!(self.rows.iter().all(|row| row.len() == ncols));
            ncols
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PatternRowVec<'db> {
    pub(crate) inner: Vec<MatrixPat<'db>>,
}

impl<'db> PatternRowVec<'db> {
    pub(crate) fn new(inner: Vec<MatrixPat<'db>>) -> Self {
        Self { inner }
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub(crate) fn head(&self) -> Option<&MatrixPat<'db>> {
        self.inner.first()
    }

    pub fn phi_specialize(
        &self,
        db: &'db dyn HirAnalysisDb,
        ctor: ConstructorKind<'db>,
    ) -> Vec<Self> {
        debug_assert!(!self.inner.is_empty());

        let first_pat = &self.inner[0];
        let ctor_fields = ctor.field_types(db);

        match &first_pat.kind {
            MatrixPatKind::WildCard(bind) => {
                let mut inner = Vec::with_capacity(self.inner.len() + ctor_fields.len() - 1);
                for field_ty in ctor_fields {
                    inner.push(MatrixPat::wildcard(*bind, field_ty));
                }
                inner.extend_from_slice(&self.inner[1..]);
                vec![Self::new(inner)]
            }
            MatrixPatKind::Constructor { kind, fields } => {
                if *kind == ctor {
                    let mut inner = Vec::with_capacity(self.inner.len() + ctor_fields.len() - 1);
                    for (idx, field_ty) in ctor_fields.iter().copied().enumerate() {
                        if let Some(field) = fields.get(idx) {
                            inner.push(field.clone());
                        } else {
                            inner.push(MatrixPat::wildcard(None, field_ty));
                        }
                    }
                    inner.extend_from_slice(&self.inner[1..]);
                    vec![Self::new(inner)]
                } else {
                    Vec::new()
                }
            }
            MatrixPatKind::Or(pats) => {
                let mut result = Vec::new();
                for pat in pats {
                    let mut tmp_inner = Vec::with_capacity(self.inner.len());
                    tmp_inner.push(pat.clone());
                    tmp_inner.extend_from_slice(&self.inner[1..]);
                    result.extend(PatternRowVec::new(tmp_inner).phi_specialize(db, ctor));
                }
                result
            }
        }
    }

    pub fn d_specialize(&self) -> Vec<Self> {
        debug_assert!(!self.inner.is_empty());

        match &self.inner[0].kind {
            MatrixPatKind::WildCard(_) => vec![Self::new(self.inner[1..].to_vec())],
            MatrixPatKind::Constructor { .. } => Vec::new(),
            MatrixPatKind::Or(pats) => {
                let mut result = Vec::new();
                for pat in pats {
                    let mut tmp_inner = Vec::with_capacity(self.inner.len());
                    tmp_inner.push(pat.clone());
                    tmp_inner.extend_from_slice(&self.inner[1..]);
                    result.extend(PatternRowVec::new(tmp_inner).d_specialize());
                }
                result
            }
        }
    }

    fn first_column_ty(&self) -> TyId<'db> {
        debug_assert!(!self.inner.is_empty());
        self.inner[0].ty
    }

    fn collect_column_ctors(&self, column: usize) -> Vec<ConstructorKind<'db>> {
        self.inner[column].kind.collect_ctors()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MatrixPat<'db> {
    pub(crate) kind: MatrixPatKind<'db>,
    pub(crate) ty: TyId<'db>,
}

impl<'db> MatrixPat<'db> {
    pub(crate) fn new(kind: MatrixPatKind<'db>, ty: TyId<'db>) -> Self {
        Self { kind, ty }
    }

    pub(crate) fn wildcard(bind: Option<BindingRef<'db>>, ty: TyId<'db>) -> Self {
        Self::new(MatrixPatKind::WildCard(bind), ty)
    }

    pub(crate) fn constructor(
        ctor: ConstructorKind<'db>,
        fields: Vec<MatrixPat<'db>>,
        ty: TyId<'db>,
    ) -> Self {
        Self::new(MatrixPatKind::Constructor { kind: ctor, fields }, ty)
    }

    pub(crate) fn ctor_with_wild_card_fields(
        db: &'db dyn HirAnalysisDb,
        ctor: ConstructorKind<'db>,
        ty: TyId<'db>,
    ) -> Self {
        let fields = ctor
            .field_types(db)
            .into_iter()
            .map(|field_ty| Self::wildcard(None, field_ty))
            .collect();
        Self::constructor(ctor, fields, ty)
    }

    pub(crate) fn is_wildcard(&self) -> bool {
        matches!(self.kind, MatrixPatKind::WildCard(_))
    }

    pub(crate) fn from_root(store: &PatternStore<'db>, root: ValidatedPatId) -> Self {
        let node = store.node(root);
        let kind = match &node.kind {
            ValidatedPatKind::Wildcard { binding } => MatrixPatKind::WildCard(*binding),
            ValidatedPatKind::Constructor { ctor, fields } => MatrixPatKind::Constructor {
                kind: *ctor,
                fields: fields
                    .iter()
                    .copied()
                    .map(|field| Self::from_root(store, field))
                    .collect(),
            },
            ValidatedPatKind::Or(pats) => MatrixPatKind::Or(
                pats.iter()
                    .copied()
                    .map(|pat| Self::from_root(store, pat))
                    .collect(),
            ),
        };
        Self::new(kind, node.ty)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum MatrixPatKind<'db> {
    WildCard(Option<BindingRef<'db>>),
    Constructor {
        kind: ConstructorKind<'db>,
        fields: Vec<MatrixPat<'db>>,
    },
    Or(Vec<MatrixPat<'db>>),
}

impl<'db> MatrixPatKind<'db> {
    fn collect_ctors(&self) -> Vec<ConstructorKind<'db>> {
        match self {
            Self::WildCard(_) => Vec::new(),
            Self::Constructor { kind, .. } => vec![*kind],
            Self::Or(pats) => {
                let mut ctors = Vec::new();
                for pat in pats {
                    ctors.extend_from_slice(&pat.kind.collect_ctors());
                }
                ctors
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SigmaSet<'db>(pub IndexSet<ConstructorKind<'db>>);

impl<'db> SigmaSet<'db> {
    pub fn from_rows<'a>(rows: impl Iterator<Item = &'a PatternRowVec<'db>>, column: usize) -> Self
    where
        'db: 'a,
    {
        let mut ctor_set = IndexSet::new();
        for row in rows {
            for ctor in row.collect_column_ctors(column) {
                ctor_set.insert(ctor);
            }
        }
        Self(ctor_set)
    }

    pub fn complete_sigma(db: &'db dyn HirAnalysisDb, ty: TyId<'db>) -> Self {
        let mut ctors = IndexSet::new();

        if ty.is_bool(db) {
            ctors.insert(ConstructorKind::Literal(LitKind::Bool(true), ty));
            ctors.insert(ConstructorKind::Literal(LitKind::Bool(false), ty));
        } else if ty.is_tuple(db) {
            ctors.insert(ConstructorKind::Type(ty));
        } else if let Some(adt_def) = ty.adt_def(db) {
            if let AdtRef::Enum(enum_def) = adt_def.adt_ref(db) {
                for (idx, _) in enum_def.variants(db).enumerate() {
                    ctors.insert(ConstructorKind::Variant(
                        crate::core::hir_def::EnumVariant::new(enum_def, idx),
                        ty,
                    ));
                }
            } else if let AdtRef::Struct(_) = adt_def.adt_ref(db) {
                ctors.insert(ConstructorKind::Type(ty));
            }
        }

        Self(ctors)
    }

    pub fn is_complete(&self, db: &'db dyn HirAnalysisDb) -> bool {
        match self.0.first() {
            Some(ctor) => {
                let expected = ctor_variant_num(db, ctor);
                debug_assert!(
                    self.0.len() <= expected,
                    "sigma set {self:?} has {} ctors, expected at most {expected}",
                    self.0.len(),
                );
                self.0.len() == expected
            }
            None => false,
        }
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn difference<'a>(
        &'a self,
        other: &'a Self,
    ) -> impl Iterator<Item = &'a ConstructorKind<'db>> + 'a {
        self.0.difference(&other.0)
    }
}

impl<'db> IntoIterator for SigmaSet<'db> {
    type Item = ConstructorKind<'db>;
    type IntoIter = <IndexSet<ConstructorKind<'db>> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

pub fn check_exhaustiveness<'db>(
    db: &'db dyn HirAnalysisDb,
    store: &PatternStore<'db>,
    roots: &[ValidatedPatId],
    ty: TyId<'db>,
) -> Result<(), Vec<String>> {
    let matrix = PatternMatrix::from_roots(store, roots);
    match matrix.find_missing_patterns(db) {
        Some(missing) => Err(condense_missing_patterns(db, &missing, ty)),
        None => Ok(()),
    }
}

pub fn check_reachability<'db>(
    db: &'db dyn HirAnalysisDb,
    store: &PatternStore<'db>,
    roots: &[ValidatedPatId],
) -> Vec<bool> {
    let matrix = PatternMatrix::from_roots(store, roots);
    (0..roots.len())
        .map(|i| matrix.is_row_useful(db, i))
        .collect()
}

fn condense_missing_patterns<'db>(
    db: &'db dyn HirAnalysisDb,
    missing: &[MatrixPat<'db>],
    _ty: TyId<'db>,
) -> Vec<String> {
    if missing.is_empty() {
        return Vec::new();
    }

    let mut result = Vec::new();
    for pattern in missing.iter().take(3) {
        result.push(display_missing_pattern(db, pattern));
    }
    if missing.len() > 3 {
        result.push(format!("... and {} more patterns", missing.len() - 3));
    }
    result
}

pub(crate) fn display_missing_pattern<'db>(
    db: &'db dyn HirAnalysisDb,
    pat: &MatrixPat<'db>,
) -> String {
    match &pat.kind {
        MatrixPatKind::WildCard(_) => "_".to_string(),
        MatrixPatKind::Constructor { kind, fields } => match kind {
            ConstructorKind::Variant(variant, _) => {
                let variant_name = variant
                    .name(db)
                    .map(|name| name.to_string())
                    .unwrap_or_else(|| "UnknownVariant".to_string());
                let enum_name = match variant.enum_.name(db) {
                    crate::core::hir_def::Partial::Present(name) => name.data(db).to_string(),
                    crate::core::hir_def::Partial::Absent => "UnknownEnum".to_string(),
                };
                let full_name = format!("{enum_name}::{variant_name}");

                match variant.kind(db) {
                    crate::core::hir_def::VariantKind::Unit => full_name,
                    crate::core::hir_def::VariantKind::Tuple(_) => {
                        if fields.is_empty() {
                            format!("{full_name}(..)")
                        } else {
                            let field_patterns: Vec<String> = fields
                                .iter()
                                .map(|f| display_missing_pattern(db, f))
                                .collect();
                            format!("{}({})", full_name, field_patterns.join(", "))
                        }
                    }
                    crate::core::hir_def::VariantKind::Record(_) => format!("{full_name} {{ .. }}"),
                }
            }
            ConstructorKind::Type(ty) => {
                if ty.is_tuple(db) {
                    if fields.is_empty() {
                        "()".to_string()
                    } else {
                        let parts: Vec<String> = fields
                            .iter()
                            .map(|f| display_missing_pattern(db, f))
                            .collect();
                        format!("({})", parts.join(", "))
                    }
                } else {
                    format!("{} {{ .. }}", ty.pretty_print(db))
                }
            }
            ConstructorKind::Literal(lit, _) => match lit {
                LitKind::Bool(b) => b.to_string(),
                LitKind::Int(i) => i.data(db).to_string(),
                LitKind::String(s) => format!("\"{}\"", s.data(db)),
            },
        },
        MatrixPatKind::Or(patterns) => {
            if patterns.is_empty() {
                "_".to_string()
            } else if patterns.len() == 1 {
                display_missing_pattern(db, &patterns[0])
            } else {
                let examples: Vec<String> = patterns
                    .iter()
                    .take(3)
                    .map(|p| display_missing_pattern(db, p))
                    .collect();
                if patterns.len() <= 3 {
                    examples.join(" | ")
                } else {
                    format!(
                        "{} | ... ({} more)",
                        examples.join(" | "),
                        patterns.len() - 3
                    )
                }
            }
        }
    }
}
