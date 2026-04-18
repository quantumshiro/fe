//! Thread-local panic context stack.
//!
//! Modeled on rust-analyzer's `DbPanicContext` (see
//! `rust-lang/rust-analyzer crates/base-db/src/lib.rs:390-432`).
//!
//! # What problem this solves
//!
//! When an LSP handler panics, the Rust backtrace tells us *where* in the
//! codebase the panic fired, but not *which user request* was in flight at
//! the time. A line like `assertion failed at hir/src/foo.rs:142` is
//! untriagable without knowing which source file the user was hovering
//! over or completing in. This module gives us that.
//!
//! Each request handler pushes a small context frame — the LSP method
//! name and a short params summary — onto a thread-local stack via
//! [`enter`]. The frame is popped automatically when the returned
//! [`PanicContext`] guard drops, including on panic unwinds. The panic
//! hook reads the stack via [`format_stack`] and includes it in the panic
//! record written to `panics-<pid>.log`.
//!
//! # Thread locality
//!
//! Frames live in a `thread_local!` `RefCell<Vec<String>>`, so pushing on
//! one thread is invisible from another. That's the right semantics for
//! our actor model: each LSP request runs as a detached task on the
//! actor's smol `LocalExecutor`, which runs on a dedicated OS thread —
//! frames pushed by `LspActorService::call` on the main loop thread are
//! visible when *that thread* panics, and frames pushed inside actor
//! handlers (on the actor thread) are visible when the actor thread
//! panics. See also the note about span propagation in
//! `backend::spawn_on_workers`: worker pool threads have their own
//! separate context.

use std::cell::RefCell;

thread_local! {
    static CTX: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

/// Push a context frame onto the thread-local stack. The frame is popped
/// when the returned guard drops, whether normally or during unwind.
///
/// Typical use:
///
/// ```ignore
/// let _pctx = panic_context::enter(format!("request: {method} {params:?}"));
/// // ... handle request ...
/// // _pctx drops at end of scope, popping the frame.
/// ```
#[must_use]
pub fn enter(frame: String) -> PanicContext {
    CTX.with(|ctx| ctx.borrow_mut().push(frame));
    PanicContext(())
}

/// RAII guard for a context frame. Dropping pops the top of the
/// thread-local stack. The field is a private `()` so external code
/// cannot construct one — use [`enter`] instead.
pub struct PanicContext(());

impl Drop for PanicContext {
    fn drop(&mut self) {
        CTX.with(|ctx| {
            // Pop even on unwind — this preserves stack invariants so
            // nested enters still balance across panics. If the stack is
            // unexpectedly empty, just no-op: double-panic would be worse
            // than a silently skipped pop.
            let _ = ctx.borrow_mut().pop();
        });
    }
}

/// Render the current thread's context stack as a newline-terminated
/// string, with frames numbered from the innermost (most recent) to the
/// outermost. Returns an empty string if the stack is empty.
///
/// Called from the panic hook at [`crate::logging::setup_panic_hook`].
pub fn format_stack() -> String {
    CTX.with(|ctx| {
        let stack = ctx.borrow();
        if stack.is_empty() {
            return String::new();
        }
        let mut out = String::new();
        for (idx, frame) in stack.iter().rev().enumerate() {
            out.push_str(&format!("{idx:>4}: {frame}\n"));
        }
        out
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_stack_formats_empty() {
        assert_eq!(format_stack(), "");
    }

    #[test]
    fn frames_are_popped_on_drop() {
        {
            let _a = enter("outer".to_owned());
            {
                let _b = enter("inner".to_owned());
                let s = format_stack();
                assert!(s.contains("outer"));
                assert!(s.contains("inner"));
                // inner should appear before outer (innermost first)
                let inner_pos = s.find("inner").unwrap();
                let outer_pos = s.find("outer").unwrap();
                assert!(inner_pos < outer_pos);
            }
            // After inner drops, only outer remains
            let s = format_stack();
            assert!(s.contains("outer"));
            assert!(!s.contains("inner"));
        }
        assert_eq!(format_stack(), "");
    }

    #[test]
    fn drop_during_unwind_pops_cleanly() {
        // Push a frame, panic inside, catch the panic, verify the stack
        // was popped by the RAII guard drop during unwind.
        let _ = std::panic::catch_unwind(|| {
            let _pctx = enter("unwind test".to_owned());
            panic!("intentional");
        });
        assert_eq!(format_stack(), "");
    }
}
