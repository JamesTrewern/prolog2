//! Clause representation and metadata.
use crate::{
    heap::{Heap, Tag},
    LITERALS_DEFAULT_SIZE,
};
use smallvec::SmallVec;
use std::{
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

pub(crate) const MAX_ARG: usize = 64;

/// Compact 64-bit flag set used to mark meta-variables and constrained variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BitFlag64(u64);

impl BitFlag64 {
    pub fn set(&mut self, idx: usize) {
        self.0 = self.0 | 1 << idx;
    }

    pub fn _unset(&mut self, idx: usize) {
        self.0 = self.0 & !(1 << idx);
    }

    pub fn get(&self, idx: usize) -> bool {
        self.0 & (1 << idx) != 0
    }

    pub fn is_some(&self) -> bool {
        self.0 != 0
    }

    pub fn is_none(&self) -> bool {
        self.0 == 0
    }

    /// Iterate the set bit indices in ascending order.
    ///
    /// The inverse of the filter in
    /// [`MetaSub::from_arg_regs`](crate::program::MetaSub::from_arg_regs),
    /// which compacts the argument registers by discarding every position
    /// whose bit is clear. Zipping this iterator with the compacted vector
    /// recovers the original argument ids.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..MAX_ARG).filter(move |&idx| self.get(idx))
    }
}

impl From<Vec<usize>> for BitFlag64 {
    fn from(bit_positions: Vec<usize>) -> Self {
        let mut bit_flags = Self(0);
        for bit_pos in bit_positions {
            assert!(
                bit_pos < MAX_ARG,
                "meta clause cannot have more than {MAX_ARG} variables (variable index {bit_pos} exceeds limit)"
            );
            bit_flags.set(bit_pos);
        }
        bit_flags
    }
}

static META_CLAUSE_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct MetaData {
    /// The lowest arg id that is a meta variable.
    ///
    /// Equivalent to the bit set it replaces, because the compiler packs a
    /// meta rule's *non*-meta variables into the lower ids before encoding
    /// its literals -- see the pre-ordering in `build_clause`. So the meta
    /// variables are always the contiguous run
    /// `meta_var_threshold..max_arg_id`, and one bound says everything the
    /// bit set did while turning the substitution extraction into a slice
    /// copy.
    ///
    /// Equal to `max_arg_id` when nothing is meta.
    pub meta_var_threshold: usize,
    pub constrained_vars: BitFlag64,
    /// Arg ids of the meta variables in a predicate position: the functor of
    /// a literal. Set by [`Clause::with_pred_vars`].
    pub pred_vars: BitFlag64,
    /// Whether the head's functor is one of them. Not derivable from
    /// `pred_vars`: a constant-headed rule with a meta-variable body functor
    /// also has its first predicate variable at the threshold.
    pub head_pred: bool,
    pub id: usize,
}

/// A compiled clause: a list of literal heap addresses with metadata
/// about which variables are second-order (meta) and which are constrained.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Clause {
    pub literals: SmallVec<[usize; LITERALS_DEFAULT_SIZE]>,
    pub max_arg_id: usize,
    pub meta_data: Option<MetaData>,
}

impl Clause {
    pub fn new(
        literals: Vec<usize>,
        meta_constrained_vars: Option<(Vec<usize>, Vec<usize>)>,
        max_arg_id: usize,
    ) -> Self {
        let meta_data = meta_constrained_vars.map(|(mvs, cvs)| {
            let meta_var_threshold = mvs.iter().copied().min().unwrap_or(max_arg_id);
            debug_assert!(
                {
                    let mut sorted = mvs.clone();
                    sorted.sort_unstable();
                    sorted.dedup();
                    sorted.iter().copied().eq(meta_var_threshold..max_arg_id)
                },
                "meta variables {mvs:?} of a clause with {max_arg_id} variables are not the \
                 contiguous top run {meta_var_threshold}..{max_arg_id}. A single threshold \
                 can only stand in for the bit set while the compiler keeps packing \
                 non-meta variables into the lower ids.",
            );
            MetaData {
                meta_var_threshold,
                constrained_vars: cvs.into(),
                pred_vars: BitFlag64::default(),
                head_pred: false,
                id: META_CLAUSE_COUNT.fetch_add(1, Relaxed),
            }
        });

        let literals: SmallVec<[usize; LITERALS_DEFAULT_SIZE]> = SmallVec::from_vec(literals);
        Clause {
            literals,
            max_arg_id,
            meta_data,
        }
    }

    /// Record which meta variables are literal functors, read from the
    /// encoded literals on `heap`. A no-op for a clause that is not meta.
    pub fn with_pred_vars(mut self, heap: &impl Heap) -> Self {
        let Some(meta_data) = &mut self.meta_data else {
            return self;
        };
        let threshold = meta_data.meta_var_threshold;
        for (i, &addr) in self.literals.iter().enumerate() {
            // A literal with no arguments is its own functor.
            let functor = if heap[addr].0 == Tag::Comp { addr + 1 } else { addr };
            if let (Tag::Arg, arg_id) = heap[functor] {
                if arg_id >= threshold {
                    meta_data.pred_vars.set(arg_id);
                    if i == 0 {
                        debug_assert_eq!(
                            arg_id, threshold,
                            "the head functor is encoded first, so it is the lowest meta variable"
                        );
                        meta_data.head_pred = true;
                    }
                }
            }
        }
        self
    }

    /// Index into a `MetaSub`'s `subs` of the predicate this clause defines,
    /// or `None` if its head functor is a constant. Always 0 when there is
    /// one: the head functor is the lowest meta variable.
    pub fn head_pred_sub_index(&self) -> Option<usize> {
        self.meta_data
            .as_ref()
            .and_then(|meta_data| meta_data.head_pred.then_some(0))
    }

    /// Indices into a `MetaSub`'s `subs` of the predicates this clause calls.
    pub fn body_pred_sub_indices(&self) -> impl Iterator<Item = usize> + '_ {
        let (threshold, pred_vars, head_pred) = match &self.meta_data {
            Some(meta_data) => (
                meta_data.meta_var_threshold,
                meta_data.pred_vars,
                meta_data.head_pred,
            ),
            None => (self.max_arg_id, BitFlag64::default(), false),
        };
        (threshold..self.max_arg_id)
            .filter(move |&arg_id| pred_vars.get(arg_id))
            .map(move |arg_id| arg_id - threshold)
            .skip(usize::from(head_pred))
    }

    pub fn head(&self) -> usize {
        self[0]
    }

    pub fn body(&self) -> &[usize] {
        &self[1..]
    }

    pub fn meta(&self) -> bool {
        self.meta_data.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool, &'static str> {
        if let Some(MetaData {
            meta_var_threshold, ..
        }) = self.meta_data
        {
            Ok(arg_id >= meta_var_threshold)
        } else {
            return Err("Clause is not a meta clause");
        }
    }

    pub fn constrained_var(&self, arg_id: usize) -> bool {
        if let Some(MetaData {
            constrained_vars, ..
        }) = self.meta_data
        {
            constrained_vars.get(arg_id)
        } else {
            false
        }
    }

    /// The lowest arg id that is a meta variable, or `None` if this is not a
    /// meta clause. See [`MetaData::meta_var_threshold`].
    pub fn meta_threshold(&self) -> Option<usize> {
        self.meta_data
            .as_ref()
            .map(|meta_data| meta_data.meta_var_threshold)
    }

    pub fn constrained_vars(&self) -> Option<BitFlag64> {
        self.meta_data
            .as_ref()
            .map(|meta_data| meta_data.constrained_vars)
    }

    /// Shift every literal's heap address by `offset`. Used when appending a
    /// clause -- and the heap region it was extracted into -- onto a larger,
    /// already-populated heap.
    pub fn shift_literals(&mut self, offset: usize) {
        for literal in self.literals.iter_mut() {
            *literal += offset;
        }
    }

    pub fn to_string(&self, heap: &impl Heap) -> String {
        if self.len() == 1 {
            return heap.term_string(self.head()) + ".";
        }
        let mut buffer = format!("{}:-", heap.term_string(self.head()));
        for body_literal in self.body() {
            buffer += &heap.term_string(*body_literal);
            buffer += ","
        }
        buffer.pop();
        buffer += ".";
        buffer
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &[usize] {
        &self.literals
    }
}

impl DerefMut for Clause {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.literals
    }
}

#[cfg(test)]
mod program_symbol_isolation {
    use crate::{heap::ProgramHeap, parser::_build_clause};

    /// Two programs name their own clause variables.
    ///
    /// This is what a global symbol table actually broke. A program `Arg`
    /// cell is named through `get_var(address, 0)` -- keyed on the cell's
    /// address, with 0 standing for "a program heap" -- and every program
    /// starts at address 0. With one shared map, loading the second clause
    /// overwrote the first's names, and the first clause then rendered as
    /// `p(Alpha,Beta):-q(Alpha,Beta)`.
    ///
    /// Resolution never consulted those names, so the damage was confined to
    /// anything that printed a program clause. That is why it goes unnoticed
    /// in a query and has to be asserted on the rendered clause.
    #[test]
    fn two_programs_keep_their_own_clause_var_names() {
        let mut first = ProgramHeap::new();
        let clause = _build_clause(&mut first, "p(X,Y):-q(X,Y).");

        let mut second = ProgramHeap::new();
        let _ = _build_clause(&mut second, "p(Alpha,Beta):-q(Alpha,Beta).");

        assert_eq!(clause.to_string(&first), "p(X,Y):-q(X,Y).");
    }
}

/// The compiler's pre-ordering is what lets one threshold stand in for the
/// old 64-bit flag set, so it is worth pinning against the real parser
/// rather than against hand-built fixtures.
#[cfg(test)]
mod meta_var_threshold {
    use crate::{heap::ProgramHeap, parser::_build_clause};

    /// Compile `src` and return `(threshold, max_arg_id)`.
    fn compile(src: &str) -> (usize, usize) {
        let mut prog = ProgramHeap::new();
        let clause = _build_clause(&mut prog, src);
        (
            clause.meta_threshold().expect("a meta clause"),
            clause.max_arg_id,
        )
    }

    /// `build_clause` inserts the non-meta variables into `var_values` first,
    /// so they take the low ids and the meta variables are left with the
    /// contiguous top run. Each case states the arity it expects, because an
    /// off-by-one here would silently turn a predicate variable into an
    /// ordinary one.
    #[test]
    fn meta_vars_are_the_contiguous_top_run() {
        // X,Y -> 0,1; P,Q -> 2,3.
        assert_eq!(compile("P(X,Y):-Q(X,Y),{P,Q}."), (2, 4));
        // X,Y -> 0,1; P,Q,R -> 2,3,4.
        assert_eq!(compile("P(X,Y):-Q(X),R(Y),{P,Q,R}."), (2, 5));
        // Only the head predicate is second order: X,Y -> 0,1; P -> 2.
        assert_eq!(compile("P(X,Y):-q(X,Y),{P}."), (2, 3));
        // A body predicate variable is still part of the top run, even though
        // the head's predicate is an ordinary constant.
        assert_eq!(compile("p(X):-Q(X),{Q}."), (1, 2));
    }

    /// Every arg at or above the threshold must answer `meta_var`, and every
    /// arg below it must not -- the property `build` and `MetaSub` rely on.
    #[test]
    fn meta_var_agrees_with_the_threshold_either_side() {
        let mut prog = ProgramHeap::new();
        let clause = _build_clause(&mut prog, "P(X,Y):-Q(X),R(Y),{P,Q,R}.");
        let threshold = clause.meta_threshold().unwrap();

        for arg_id in 0..clause.max_arg_id {
            assert_eq!(
                clause.meta_var(arg_id).unwrap(),
                arg_id >= threshold,
                "arg {arg_id} is on the wrong side of threshold {threshold}"
            );
        }
    }

    /// An ordinary clause has no metadata at all, so it has no threshold and
    /// `meta_var` refuses rather than answering against a default.
    ///
    /// The `unwrap_or(max_arg_id)` fallback in `Clause::new` -- a meta clause
    /// whose variable set is empty -- is not reachable through the parser,
    /// since `{}` does not parse. It stays as a total definition of the
    /// threshold rather than as behaviour under test here.
    #[test]
    fn an_ordinary_clause_has_no_threshold() {
        let mut prog = ProgramHeap::new();
        let clause = _build_clause(&mut prog, "p(X,Y).");
        assert!(
            clause.meta_threshold().is_none(),
            "an ordinary clause is not a meta clause"
        );
        assert!(clause.meta_var(0).is_err());
    }
}
