//! # Prolog²
//!
//! A Meta-Interpretive Learning (MIL) framework implementing native second-order
//! SLD resolution. Prolog² extends traditional Prolog with the ability to learn
//! logical rules from examples through predicate invention.
//!
//! ## Library usage
//!
//! The main extension point is the **predicate module** system. A
//! [`predicate_modules::PredicateModule`] bundles native Rust predicate functions
//! together with optional Prolog source code. Modules are registered with the
//! [`app::App`] builder, which also handles configuration loading and execution.
//! Examples of builtin predicate functions can be found at: https://github.com/JamesTrewern/prolog2/tree/master/src/predicate_modules
//! 
//! ### Writing a native predicate
//!
//! A native predicate is a Rust function with the signature defined by
//! [`predicate_modules::PredicateFunction`]. It receives the current heap, the
//! hypothesis being constructed, the heap address of the goal term, the predicate
//! table, and the engine configuration. It returns a [`predicate_modules::PredReturn`]
//! indicating:
//!
//! - [`predicate_modules::PredReturn::True`] — success with no heap side-effects.
//! - [`predicate_modules::PredReturn::False`] — deterministic failure; the engine backtracks.
//! - [`predicate_modules::PredReturn::Success`] — success with a list of `(source, target)` variable
//!   bindings to apply on the heap, and an optional list of new sub-goals to resolve.
//!
//! For the common case of a simple boolean check, `bool` converts directly via
//! `Into<PredReturn>`.
//!
//! ```no_run
//! use std::process::ExitCode;
//! use prolog2::{app::App, Config};
//! use prolog2::predicate_modules::{
//!     MATHS, META_PREDICATES, PredReturn, PredicateFunction, PredicateModule,
//! };
//! use prolog2::heap::query_heap::QueryHeap;
//! use prolog2::program::hypothesis::Hypothesis;
//! use prolog2::program::predicate_table::PredicateTable;
//!
//! fn my_pred(
//!     heap: &mut QueryHeap,
//!     hypothesis: &mut Hypothesis,
//!     goal: usize,
//!     pred_table: &PredicateTable,
//!     config: Config,
//! ) -> PredReturn {
//!     // Custom predicate logic here
//!     true.into()
//! }
//!
//! static MY_MODULE: PredicateModule = (
//! &[("my_pred", 1, my_pred)],
//! &[]
//! );
//!
//! fn main() -> ExitCode {
//!     let app = App::default()
//!         .load_module(&MY_MODULE).expect("failed to load MY_MODULE");
//!     app.run()
//! }
//! ```
//!
//! ## Error handling
//!
//! Fallible operations return [`Result<T>`], a type alias for
//! `std::result::Result<T, `[`Error`]`>`. The [`Error`] enum covers all error
//! categories the engine can produce:
//!
//! - [`Error::IO`] — I/O errors when reading source files.
//! - [`Error::Setup`] — JSON deserialisation failures for `setup.json`.
//! - [`Error::Parser`] — structured parse errors from the Prolog parser; wraps a
//!   [`parser::ParserError`] which carries source-line information via its
//!   `AtLine` variant.
//! - [`Error::Query`] — a query could not be executed (e.g. bad goal syntax).
//! - [`Error::BodyPred`] — a body-predicate specification in the setup is invalid.
//! - [`Error::Module`] — a predicate module could not be loaded (e.g. duplicate predicate).

/// Application builder and configuration types.
pub mod app;
/// Heap memory management: cells, query heaps, and the symbol database.
pub mod heap;
/// Prolog source parsing: tokenisation, syntax tree construction, and term encoding.
pub mod parser;
/// Built-in predicate modules and the predicate module system.
#[allow(dead_code)]
#[allow(unused)]
pub mod predicate_modules;
/// Program representation: clauses, hypotheses, and the predicate table.
pub mod program;
/// Resolution engine: proof search, unification, and term building.
pub mod resolution;
/// Implementation of the Top Program Consturction algorithm with parallelism
#[allow(dead_code)]
#[allow(unused)]
pub mod top_prog;

// Re-export commonly used types at crate root.
pub use app::{BodyPred, Config, Examples, SetUp};

use crate::parser::ParserError;
use std::fmt;

#[derive(Debug)]
pub enum Error {
    IO(std::io::Error),
    Setup(serde_json::Error),
    Parser(ParserError),
    Query(String),
    BodyPred(String),
    Module(String),
}

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IO(e) => write!(f, "IO error: {e}"),
            Self::Setup(e) => write!(f, "setup error: {e}"),
            Self::Parser(e) => write!(f, "parse error: {e}"),
            Self::Query(msg) => write!(f, "query error: {msg}"),
            Self::BodyPred(msg) => write!(f, "body predicate error: {msg}"),
            Self::Module(msg) => write!(f, "module error: {msg}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::IO(e) => Some(e),
            Self::Setup(e) => Some(e),
            Self::Parser(e) => Some(e),
            _ => None,
        }
    }
}

impl From<std::io::Error> for Error {
    fn from(value: std::io::Error) -> Self {
        Error::IO(value)
    }
}

impl From<serde_json::Error> for Error {
    fn from(value: serde_json::Error) -> Self {
        Error::Setup(value)
    }
}

impl From<ParserError> for Error {
    fn from(value: ParserError) -> Self {
        Error::Parser(value)
    }
}

/// Normalise a hypothesis (list of clause strings) so that functionally
/// identical hypotheses — differing only in invented predicate numbering —
/// produce the same canonical form.
///
/// Algorithm:
/// 1. Build a "skeleton" of each clause by replacing every `pred_\d+` with `pred_$`.
/// 2. Compute a sort order over clause indices using `(skeleton.len(), skeleton)`.
/// 3. Walk the original clauses in that order; assign `pred_1`, `pred_2`, …
///    to each unique `pred_\d+` token in order of first appearance.
/// 4. Apply the renaming to all clauses and return them in the sorted order.
pub fn normalise_hypothesis(clauses: &[String]) -> Vec<String> {
    if clauses.is_empty() {
        return Vec::new();
    }

    // 1. Build skeletons
    let skeletons: Vec<String> = clauses.iter().map(|c| replace_pred_ids(c, "pred_$")).collect();

    // 2. Sort indices by (skeleton length, skeleton lexicographic)
    let mut order: Vec<usize> = (0..clauses.len()).collect();
    order.sort_by(|&a, &b| {
        skeletons[a]
            .len()
            .cmp(&skeletons[b].len())
            .then_with(|| skeletons[a].cmp(&skeletons[b]))
    });

    // 3. Walk in sorted order, enumerate invented predicates by first appearance
    let mut mapping: Vec<(String, String)> = Vec::new();
    let mut counter = 1usize;
    for &idx in &order {
        for token in find_pred_tokens(&clauses[idx]) {
            if !mapping.iter().any(|(old, _)| old == &token) {
                mapping.push((token, format!("pred_{counter}")));
                counter += 1;
            }
        }
    }

    // 4. Apply renaming in sorted clause order.
    //
    // Rewritten in a single scanning pass rather than by repeated
    // `str::replace`. Sequential replacement is unsound here because the
    // names it writes are drawn from the same space as the names it is
    // still looking for: renaming `pred_5` to `pred_2` and then `pred_2` to
    // `pred_3` would rewrite the text produced by the first step. Scanning
    // once and substituting each token as it is found cannot do that, and
    // it also removes the need to order the mapping by token length to
    // avoid `pred_1` matching inside `pred_10`.
    order
        .iter()
        .map(|&idx| {
            let s = &clauses[idx];
            let bytes = s.as_bytes();
            let mut out = String::with_capacity(s.len());
            let mut i = 0;
            while i < bytes.len() {
                match invented_pred_token_end(bytes, i) {
                    Some(end) => {
                        let token = &s[i..end];
                        match mapping.iter().find(|(old, _)| old == token) {
                            Some((_, new)) => out.push_str(new),
                            None => out.push_str(token),
                        }
                        i = end;
                    }
                    None => {
                        out.push(bytes[i] as char);
                        i += 1;
                    }
                }
            }
            out
        })
        .collect()
}

/// Find the invented-predicate token starting at `i`, if there is one.
///
/// Returns the index just past the token. Two spellings count:
///
/// * `pred_\d+` — the historical form, from when invention minted a fresh
///   constant symbol for each new predicate.
/// * `Ref_\d+` **immediately followed by `(`** — what an invented predicate
///   renders as now that invention leaves it as an unbound variable. The
///   `(` requirement restricts this to functor position, because an ordinary
///   free variable sitting in an argument slot renders as `Ref_\d+` too and
///   must not be renumbered as though it were a predicate.
fn invented_pred_token_end(bytes: &[u8], i: usize) -> Option<usize> {
    let (prefix, needs_functor_position) = if bytes[i..].starts_with(b"pred_") {
        (&b"pred_"[..], false)
    } else if bytes[i..].starts_with(b"Ref_") {
        (&b"Ref_"[..], true)
    } else {
        return None;
    };

    let mut j = i + prefix.len();
    if j >= bytes.len() || !bytes[j].is_ascii_digit() {
        return None;
    }
    while j < bytes.len() && bytes[j].is_ascii_digit() {
        j += 1;
    }
    // Word boundary: `pred_1x` and `pred_1_2` are not tokens.
    if j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
        return None;
    }
    if needs_functor_position && bytes.get(j) != Some(&b'(') {
        return None;
    }
    Some(j)
}

/// Replace every invented-predicate token in `s` with `replacement`.
fn replace_pred_ids(s: &str, replacement: &str) -> String {
    let mut result = String::with_capacity(s.len());
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match invented_pred_token_end(bytes, i) {
            Some(end) => {
                result.push_str(replacement);
                i = end;
            }
            None => {
                result.push(bytes[i] as char);
                i += 1;
            }
        }
    }
    result
}

/// Find all invented-predicate tokens in `s`, in order of appearance.
pub fn find_pred_tokens(s: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        match invented_pred_token_end(bytes, i) {
            Some(end) => {
                tokens.push(s[i..end].to_string());
                i = end;
            }
            None => i += 1,
        }
    }
    tokens
}

/// Convenience: produce a canonical key string from a hypothesis for deduplication.
pub fn hypothesis_canonical_key(clauses: &[String]) -> String {
    normalise_hypothesis(clauses).join("|")
}

#[cfg(test)]
mod normalise_tests {
    use super::*;

    #[test]
    fn identical_structure_different_ids() {
        let h1 = vec![
            "in_cluster(Arg_0):-Arg_0(Arg_1),pred_42(Arg_1,Arg_2).".to_string(),
            "pred_42(Arg_0,Arg_1):-ring(Arg_0,Arg_1),aromatic(Arg_1,Arg_1).".to_string(),
        ];
        let h2 = vec![
            "in_cluster(Arg_0):-Arg_0(Arg_1),pred_99(Arg_1,Arg_2).".to_string(),
            "pred_99(Arg_0,Arg_1):-ring(Arg_0,Arg_1),aromatic(Arg_1,Arg_1).".to_string(),
        ];
        assert_eq!(
            hypothesis_canonical_key(&h1),
            hypothesis_canonical_key(&h2)
        );
    }

    #[test]
    fn different_structure_different_keys() {
        let h1 = vec![
            "in_cluster(Arg_0):-Arg_0(Arg_1),pred_1(Arg_1,Arg_2).".to_string(),
            "pred_1(Arg_0,Arg_1):-ring(Arg_0,Arg_1).".to_string(),
        ];
        let h2 = vec![
            "in_cluster(Arg_0):-Arg_0(Arg_1),pred_1(Arg_1,Arg_2).".to_string(),
            "pred_1(Arg_0,Arg_1):-bound(Arg_0,Arg_1).".to_string(),
        ];
        assert_ne!(
            hypothesis_canonical_key(&h1),
            hypothesis_canonical_key(&h2)
        );
    }

    #[test]
    fn multiple_invented_predicates() {
        let h1 = vec![
            "in_cluster(A):-A(M),pred_50(M,P).".to_string(),
            "pred_50(X,Z):-pred_51(X,Y),bound(Y,Z).".to_string(),
            "pred_51(X,Y):-ring(X,Y),aromatic(Y,Y).".to_string(),
        ];
        let h2 = vec![
            "in_cluster(A):-A(M),pred_7(M,P).".to_string(),
            "pred_7(X,Z):-pred_8(X,Y),bound(Y,Z).".to_string(),
            "pred_8(X,Y):-ring(X,Y),aromatic(Y,Y).".to_string(),
        ];
        assert_eq!(
            hypothesis_canonical_key(&h1),
            hypothesis_canonical_key(&h2)
        );
    }

    #[test]
    fn pred_10_not_confused_with_pred_1() {
        let tokens = find_pred_tokens("pred_1(X):-pred_10(X,Y).");
        assert_eq!(tokens, vec!["pred_1", "pred_10"]);
    }
}

#[cfg(test)]
mod examples;
