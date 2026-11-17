//! The configuration structs and how they are read from a JSON config file.

use std::fs;

use serde::{Deserialize, Serialize};

/// Bounds on meta (second order) resolution, the `resolution` block of a
/// JSON config file.
#[derive(Clone, Copy, Serialize, Deserialize, Debug)]
pub struct ResolutionConfig {
    /// Maximum proof search depth.
    pub max_depth: usize,
    /// Maximum number of learned clauses per hypothesis.
    pub max_clause: usize,
    /// Enable debug trace output.
    #[serde(default)]
    pub debug: bool,
    /// Keep invented predicates insulated from the rest of the program.
    #[serde(default = "protect_h_preds_default")]
    pub protect_h_preds: bool,
}

/// Default for [`ResolutionConfig::protect_h_preds`]: absent means enabled.
///
/// `#[serde(default)]` on a `bool` would use `bool::default()`, which is
/// `false` — the opposite of the intended default — so the field needs an
/// explicit default function.
fn protect_h_preds_default() -> bool {
    true
}

impl ResolutionConfig {
    /// Set [`Self::max_depth`].
    pub fn max_depth(self, max_depth: usize) -> Self {
        Self { max_depth, ..self }
    }

    /// Set [`Self::max_clause`].
    pub fn max_clause(self, max_clause: usize) -> Self {
        Self { max_clause, ..self }
    }

    /// Set [`Self::debug`].
    pub fn debug(self, debug: bool) -> Self {
        Self { debug, ..self }
    }

    /// Set [`Self::protect_h_preds`].
    pub fn protect_h_preds(self, protect_h_preds: bool) -> Self {
        Self {
            protect_h_preds,
            ..self
        }
    }
}

/// ```text
/// ResolutionConfig {
///     max_depth: 100,
///     max_clause: 4,
///     debug: false,
///     protect_h_preds: true,
/// }
/// ```
impl Default for ResolutionConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_clause: 4,
            debug: false,
            protect_h_preds: protect_h_preds_default(),
        }
    }
}

/// A body predicate declaration in the config file.
/// Deserialized from a string whith predicate and arity seperated by '/'
/// e.g `"p/2"`.
#[derive(Serialize, Debug)]
pub struct BodyPred {
    /// Predicate name.
    pub symbol: String,
    /// Predicate arity.
    pub arity: usize,
}

impl TryFrom<&str> for BodyPred {
    type Error = String;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        let (symbol, arity_str) = value
            .rsplit_once('/')
            .ok_or_else(|| format!("expected \"symbol/arity\", got {value:?}"))?;
        let arity = arity_str
            .parse()
            .map_err(|_| format!("arity must be a non-negative integer, got {arity_str:?}"))?;
        Ok(Self {
            symbol: symbol.into(),
            arity,
        })
    }
}

/// Conversion into a [`BodyPred`] that may fail with a [`crate::Error`].
///
/// Implemented for:
/// - [`BodyPred`] itself — infallible identity conversion.
/// - Any string-like type implementing [`AsRef<str>`] (e.g. `&str`, `&&str`,
///   `String`) — parses the `"name/arity"` format.
///
/// This trait is the bound on [`App::add_body_predicates`](super::App::add_body_predicates), so you can pass
/// either a `Vec<BodyPred>` or a plain string slice like `&["p/2", "q/1"]`
/// without any intermediate allocation.
pub trait TryIntoBodyPred {
    fn try_into_body_pred(self) -> crate::Result<BodyPred>;
}

impl TryIntoBodyPred for BodyPred {
    fn try_into_body_pred(self) -> crate::Result<BodyPred> {
        Ok(self)
    }
}

impl<S: AsRef<str>> TryIntoBodyPred for S {
    fn try_into_body_pred(self) -> crate::Result<BodyPred> {
        BodyPred::try_from(self.as_ref()).map_err(crate::Error::BodyPred)
    }
}

impl<'de> serde::Deserialize<'de> for BodyPred {
    fn deserialize<D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> std::result::Result<Self, D::Error> {
        use serde::de::{self, Visitor};
        use std::fmt;

        struct BodyPredVisitor;

        impl<'de> Visitor<'de> for BodyPredVisitor {
            type Value = BodyPred;

            fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
                f.write_str(r#"a string like "p/2""#)
            }

            fn visit_str<E: de::Error>(self, v: &str) -> std::result::Result<BodyPred, E> {
                v.try_into().map_err(|err| E::custom(err))
            }
        }

        deserializer.deserialize_any(BodyPredVisitor)
    }
}

fn deserialize_examples<'de, D>(deserializer: D) -> std::result::Result<Vec<String>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::{self, SeqAccess, Visitor};
    use std::fmt;

    struct ExamplesVisitor;

    impl<'de> Visitor<'de> for ExamplesVisitor {
        type Value = Vec<String>;

        fn expecting(&self, f: &mut fmt::Formatter) -> fmt::Result {
            f.write_str("a file path string or a list of example strings")
        }

        // "examples/pos.pl" — treat as a file path and load it
        fn visit_str<E: de::Error>(self, v: &str) -> std::result::Result<Vec<String>, E> {
            read_examples(v)
                .map_err(|e| E::custom(format!("failed to read examples file {v:?}: {e}")))
        }

        // ["p(a)", "p(b)"] — take the strings directly
        fn visit_seq<A: SeqAccess<'de>>(
            self,
            mut seq: A,
        ) -> std::result::Result<Vec<String>, A::Error> {
            let mut items = Vec::with_capacity(seq.size_hint().unwrap_or(0));
            while let Some(item) = seq.next_element::<String>()? {
                items.push(item);
            }
            Ok(items)
        }
    }

    deserializer.deserialize_any(ExamplesVisitor)
}

/// The examples in the file at `path`: one literal each, ended by a `.` and
/// a new line.
fn read_examples(path: &str) -> std::io::Result<Vec<String>> {
    Ok(fs::read_to_string(path)?
        .split(".\n")
        .map(str::trim)
        .filter(|ex| !ex.is_empty())
        .map(String::from)
        .collect())
}

/// One side of the [`Examples`], positive or negative: a file path or a list
/// of literals.
///
/// A string (`&str`, `String`) is the path of a file holding one literal per
/// line, each ended by a `.`. A list (`&[T]`, `&[T; N]`, `[T; N]`, `Vec<T>`,
/// for any `T: AsRef<str>`) holds the literals themselves.
///
/// # Panics
///
/// Converting a path panics if the file cannot be read.
pub trait ExampleSource {
    fn into_examples(self) -> Vec<String>;
}

impl ExampleSource for &str {
    fn into_examples(self) -> Vec<String> {
        read_examples(self).unwrap_or_else(|e| panic!("failed to read examples file {self:?}: {e}"))
    }
}

impl ExampleSource for String {
    fn into_examples(self) -> Vec<String> {
        self.as_str().into_examples()
    }
}

impl<T: AsRef<str>> ExampleSource for &[T] {
    fn into_examples(self) -> Vec<String> {
        self.iter().map(|ex| ex.as_ref().to_string()).collect()
    }
}

impl<T: AsRef<str>, const N: usize> ExampleSource for &[T; N] {
    fn into_examples(self) -> Vec<String> {
        self.as_slice().into_examples()
    }
}

impl<T: AsRef<str>, const N: usize> ExampleSource for [T; N] {
    fn into_examples(self) -> Vec<String> {
        self.as_slice().into_examples()
    }
}

impl<T: AsRef<str>> ExampleSource for Vec<T> {
    fn into_examples(self) -> Vec<String> {
        self.as_slice().into_examples()
    }
}

/// Positive examples only, from a file path or a list of literals.
impl<P: ExampleSource> From<P> for Examples {
    fn from(pos: P) -> Self {
        Examples {
            pos: pos.into_examples(),
            neg: Vec::new(),
        }
    }
}

/// Positive then negative examples, each from a file path or a list of
/// literals.
impl<P: ExampleSource, N: ExampleSource> From<(P, N)> for Examples {
    fn from((pos, neg): (P, N)) -> Self {
        Examples {
            pos: pos.into_examples(),
            neg: neg.into_examples(),
        }
    }
}

/// Positive and negative training examples.
///
/// Usually made by conversion, from one [`ExampleSource`] for the positives
/// or a pair for the positives and negatives. Each source is a file path or
/// a list of literals:
///
/// ```no_run
/// use prolog2::Examples;
///
/// // Two files, or the positives' file alone.
/// let examples = Examples::from(("pos.pl", "neg.pl"));
/// let examples = Examples::from("pos.pl");
///
/// // Two lists, or the positives alone.
/// let examples = Examples::from((["p(a)", "p(b)"], ["p(c)"]));
/// let examples = Examples::from(["p(a)", "p(b)"]);
/// ```
///
/// In a JSON config file `pos` and `neg` each take the same two forms: a
/// path string or a list of strings.
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Examples {
    #[serde(deserialize_with = "deserialize_examples")]
    pub pos: Vec<String>,
    #[serde(deserialize_with = "deserialize_examples")]
    pub neg: Vec<String>,
}

/// Settings for parallel MIL pipeline. Generalising from all the
/// positive examples at once.
///
/// [`Config::parallel`] is an `Option`,
/// so a config either carries this block and learns, or omits it
/// and runs the examples as a direct query. That is why there is no `enabled`
/// field here.
#[derive(Serialize, Deserialize, Debug, Clone, Copy)]
// An omitted field takes its value from `Default`, not the zero of its type.
#[serde(default)]
pub struct ParallelConfig {
    /// Run Plotkin's program reduction over each learned program, dropping
    /// clauses the remaining ones already cover.
    /// Off by default, which is useful for profiling or for inspecting the
    /// raw top program.
    pub reduce: bool,
    /// Break ties between equally-sized sub hypotheses by literal count.
    pub sort_by_literals: bool,
    /// How many complete programs to return.
    pub final_h_count: usize,
    /// How many negative examples may be set aside as noise. Defaults to 0.
    ///
    /// When some positive is only entailed together with negatives, the
    /// fewest examples whose removal leaves a hypothesis are found: those
    /// negatives ignored, or those positives left uncovered. Within this
    /// and [`Self::pos_noise`] they are filtered out, with a note, and the
    /// run goes on. Otherwise it ends with a report on those examples.
    pub neg_noise: usize,
    /// How many positive examples may be left uncovered as noise. Defaults
    /// to 0. See [`Self::neg_noise`].
    pub pos_noise: usize,
}

impl ParallelConfig {
    /// Set [`Self::reduce`].
    pub fn reduce(self, reduce: bool) -> Self {
        Self { reduce, ..self }
    }

    /// Set [`Self::sort_by_literals`].
    pub fn sort_by_literals(self, sort_by_literals: bool) -> Self {
        Self {
            sort_by_literals,
            ..self
        }
    }

    /// Set [`Self::final_h_count`].
    pub fn final_h_count(self, final_h_count: usize) -> Self {
        Self {
            final_h_count,
            ..self
        }
    }

    /// Set [`Self::neg_noise`].
    pub fn neg_noise(self, neg_noise: usize) -> Self {
        Self { neg_noise, ..self }
    }

    /// Set [`Self::pos_noise`].
    pub fn pos_noise(self, pos_noise: usize) -> Self {
        Self { pos_noise, ..self }
    }
}

/// ```text
/// ParallelConfig {
///     reduce: false,
///     sort_by_literals: false,
///     final_h_count: 5,
///     neg_noise: 0,
///     pos_noise: 0,
/// }
/// ```
impl Default for ParallelConfig {
    fn default() -> Self {
        Self {
            reduce: false,
            sort_by_literals: false,
            final_h_count: 5,
            neg_noise: 0,
            pos_noise: 0,
        }
    }
}

/// Top-level configuration loaded from a JSON config file.
#[derive(Serialize, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
pub struct Config {
    /// Bounds on meta (second order) resolution.
    pub resolution: ResolutionConfig,
    pub body_predicates: Vec<BodyPred>,
    pub files: Vec<String>,
    pub examples: Option<Examples>,
    /// When true, the examples are run as a query without prompting.
    #[serde(default)]
    pub auto: bool,
    /// Present to learn from the examples by parallel Top Program
    /// Construction; absent to run them as a direct query.
    #[serde(default)]
    pub parallel: Option<ParallelConfig>,
    /// Tolerance for the `=~=` (approximately-equal) operator, as an integer
    /// percentage. `5` means "within 5 %". Defaults to `10`.
    #[serde(default = "default_approx_tolerance")]
    pub approx_tolerance_pct: u8,
}

fn default_approx_tolerance() -> u8 {
    10
}

impl Examples {
    /// Convert the examples into a single Prolog query string.
    ///
    /// Positive examples become goals; negative examples are wrapped in `not(...)`.
    pub fn to_query(&self) -> String {
        let mut buffer = String::new();
        for pos_ex in &self.pos {
            buffer += pos_ex;
            buffer += ",";
        }
        for neg_ex in &self.neg {
            buffer += &format!("not({neg_ex}),");
        }
        buffer.pop();
        buffer += ".";
        buffer
    }

    pub fn normalise_for_parallel(&mut self) {
        fn normalise(ex: &mut String) {
            *ex = ex.trim().into();
            if ex.chars().last() != Some('.') {
                *ex += ".";
            }
        }
        self.pos.iter_mut().for_each(normalise);
        self.neg.iter_mut().for_each(normalise);
    }
}

#[cfg(test)]
mod example_tests {
    use super::Examples;

    const POS_FILE: &str = "examples/colreg/pos/avoid.pl";
    const NEG_FILE: &str = "examples/colreg/neg/avoid.pl";

    fn from_json(pos: &str, neg: &str) -> Examples {
        serde_json::from_str(&format!(r#"{{"pos":{pos},"neg":{neg}}}"#)).unwrap()
    }

    #[test]
    fn lists_are_taken_as_the_literals() {
        let examples = Examples::from((["p(a)", "p(b)"], ["p(c)"]));
        assert_eq!(examples.pos, ["p(a)", "p(b)"]);
        assert_eq!(examples.neg, ["p(c)"]);

        // Slices, array references and vectors of any string type.
        let (pos, neg) = (vec!["p(a)".to_string()], ["p(c)"]);
        let examples = Examples::from((pos.as_slice(), &neg));
        assert_eq!(
            (examples.pos, examples.neg),
            (pos.clone(), vec!["p(c)".to_string()])
        );
        assert_eq!(Examples::from((pos.clone(), neg)).pos, pos);
    }

    #[test]
    fn one_source_is_the_positives_alone() {
        let examples = Examples::from(["p(a)", "p(b)"]);
        assert_eq!(examples.pos, ["p(a)", "p(b)"]);
        assert!(examples.neg.is_empty());

        let examples = Examples::from(POS_FILE);
        assert!(!examples.pos.is_empty() && examples.neg.is_empty());
    }

    #[test]
    fn paths_load_what_the_config_file_loads() {
        let expected = from_json(&format!("{POS_FILE:?}"), &format!("{NEG_FILE:?}"));
        assert!(!expected.pos.is_empty() && !expected.neg.is_empty());

        let examples = Examples::from((POS_FILE, NEG_FILE));
        assert_eq!(
            (&examples.pos, &examples.neg),
            (&expected.pos, &expected.neg)
        );

        // Owned paths, and a path beside a list.
        let examples = Examples::from((POS_FILE.to_string(), ["p(c)"]));
        assert_eq!(examples.pos, expected.pos);
        assert_eq!(examples.neg, ["p(c)"]);
    }

    #[test]
    #[should_panic(expected = "failed to read examples file")]
    fn a_missing_file_panics_naming_it() {
        let _ = Examples::from("no/such/examples.pl");
    }
}

#[cfg(test)]
mod builder_tests {
    use super::{ParallelConfig, ResolutionConfig};

    #[test]
    fn each_resolution_field_has_a_builder() {
        let config = ResolutionConfig::default()
            .max_depth(7)
            .max_clause(2)
            .debug(true)
            .protect_h_preds(false);
        assert_eq!((config.max_depth, config.max_clause), (7, 2));
        assert!(config.debug && !config.protect_h_preds);
    }

    #[test]
    fn each_parallel_field_has_a_builder() {
        let parallel = ParallelConfig::default()
            .reduce(true)
            .sort_by_literals(true)
            .final_h_count(3)
            .neg_noise(2)
            .pos_noise(1);
        assert!(parallel.reduce && parallel.sort_by_literals);
        assert_eq!(
            (
                parallel.final_h_count,
                parallel.neg_noise,
                parallel.pos_noise
            ),
            (3, 2, 1)
        );
    }
}
