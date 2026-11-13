//! The clauses a goal may resolve against, as cursors rather than a copy.
//!
//! Gathering choices used to build a `Vec<Clause>` per goal, cloning the
//! hypothesis, the goal's own predicate and every applicable body clause into
//! it. A `Clause` is 96 bytes, a goal sees around eighteen of them, and
//! `get_choices` runs hundreds of millions of times in a learning run -- which
//! came to hundreds of gigabytes of memcpy, plus the reallocation as the
//! vector grew, plus the cache it displaced while doing it.
//!
//! [`Choices`] holds four slices and an index instead. Everything it offers is
//! already allocated -- the clause arena in
//! [`PredicateTable`](crate::program::PredicateTable), the caller's test
//! clauses, the [`Hypothesis`] -- so the whole structure is a handful of fat
//! pointers that live inline in the goal's [`Env`](super::env::Env) and copy
//! nothing.

use crate::program::Clause;

/// The clauses a goal has left to try.
///
/// Each category is a cursor that is taken from and then set to `None` once
/// exhausted, so a category is never re-examined. No allocation: the slices
/// point into storage that outlives the proof, and the hypothesis is reached
/// by index because it is mutated during the search.
///
/// # Order
///
/// Categories are tried test, then body predicates, then the goal's own
/// predicate, then meta clauses, then the hypothesis -- and each slice is
/// consumed from the **back**.
///
/// That is not arbitrary: it reproduces exactly what the previous
/// `Vec<Clause>` did. It was filled hypothesis-first and drained with
/// `Vec::pop`, so both the order of the categories and the order within each
/// one were reversed. Clause order decides which proof is found first and,
/// because `max_clause` bounds the hypothesis, which hypothesis is learned at
/// all -- so this refactor holds it fixed rather than quietly changing what
/// the engine learns.
/// Index of each category in [`Choices::slices`].
///
/// Ordered so that counting *down* from the top of the stack tries test
/// clauses, then body predicates, then the goal's own predicate, then meta
/// clauses -- the order the previous `Vec<Clause>` produced.
const VAR_PRED: usize = 0;
const KNOWN_PRED: usize = 1;
const BODY_PREDS: usize = 2;
const CATEGORIES: usize = 3;

#[derive(Debug)]
pub(super) struct Choices<'a> {
    /// The clause categories, indexed by the constants above.
    ///
    /// A spent category is an empty slice rather than a `None`, so taking the
    /// next clause is one indexed load and a length test instead of four
    /// discriminant tests in sequence.
    slices: [&'a [Clause]; CATEGORIES],
    /// How many categories are still live, so the live top of the stack is
    /// `slices[categories_left - 1]`. Counts down; `0` means every slice is
    /// spent and only the hypothesis is left.
    categories_left: usize,
    /// How many hypothesis clauses are still to try, lowest-indexed last.
    ///
    /// `0` is the exhausted state, so this needs no `Option` either. Counting
    /// down from the length read at gather time is what gives the same
    /// snapshot semantics the cloned vector had: a clause the search adds to
    /// the hypothesis after this goal gathered its choices sits above the
    /// starting count and so is never visited.
    hypothesis: usize,
    /// Withhold hypothesis clauses headed by an invented predicate.
    ///
    /// Only set for a goal on a predicate the program defines; see
    /// `Env::try_hypothesis`.
    protect_hypothesis: bool,
}

impl Default for Choices<'_> {
    fn default() -> Self {
        Self {
            slices: [&[]; CATEGORIES],
            categories_left: CATEGORIES,
            hypothesis: 0,
            protect_hypothesis: false,
        }
    }
}

impl<'a> Choices<'a> {
    /// Offer the whole hypothesis, unfiltered.
    ///
    /// For a goal that may *be* an invented predicate, which must see the
    /// clauses defining invented predicates -- they are the ones it needs.
    /// `len` is the hypothesis's current length.
    pub(super) fn with_hypothesis(len: usize) -> Self {
        Self {
            hypothesis: len,
            ..Self::default()
        }
    }

    /// Offer the hypothesis, minus clauses headed by an invented predicate.
    /// `len` is its current length.
    pub(super) fn with_protected_hypothesis(len: usize) -> Self {
        Self {
            protect_hypothesis: true,
            ..Self::with_hypothesis(len)
        }
    }

    pub(super) fn body_preds(mut self, clauses: &'a [Clause]) -> Self {
        self.slices[BODY_PREDS] = clauses;
        self
    }

    pub(super) fn known_pred(mut self, clauses: &'a [Clause]) -> Self {
        self.slices[KNOWN_PRED] = clauses;
        self
    }

    pub(super) fn var_pred(mut self, clauses: Option<&'a [Clause]>) -> Self {
        self.slices[VAR_PRED] = clauses.unwrap_or_default();
        self
    }

    /// How many clauses are still on offer.
    ///
    /// Counts the hypothesis at face value, so it ignores any
    /// invented-headed clauses that [`Self::next`] will skip. Debug output
    /// only.
    pub(super) fn remaining(&self) -> usize {
        self.slices[..self.categories_left]
            .iter()
            .map(|clauses| clauses.len())
            .sum::<usize>()
            + self.hypothesis
    }

    /// Take the next program clause to try, or `None` once every category
    /// is spent. The hypothesis comes after, from [`Self::next_hypothesis`].
    pub(super) fn next(&mut self) -> Option<&'a Clause> {
        // Pop from the top of the category stack, dropping a category once
        // its slice is empty. One indexed load plus a length test, rather
        // than a discriminant test per category.
        while self.categories_left > 0 {
            let top = self.categories_left - 1;
            if let Some((last, rest)) = self.slices[top].split_last() {
                self.slices[top] = rest;
                return Some(last);
            }
            self.categories_left = top;
        }
        None
    }

    /// Index of the next hypothesis clause to try, highest first, or `None`
    /// once they are spent. Only meaningful after [`Self::next`] has run out.
    ///
    /// An index rather than a clause: a hypothesis clause is resolved from
    /// its `MetaSub`, and whether a protected goal may see it can only be
    /// answered with that substitution in hand, so both are left to
    /// [`Env`](super::env::Env).
    pub(super) fn next_hypothesis(&mut self) -> Option<usize> {
        if self.hypothesis == 0 {
            return None;
        }
        self.hypothesis -= 1;
        Some(self.hypothesis)
    }

    /// Whether hypothesis clauses headed by an invented predicate are
    /// withheld from this goal.
    pub(super) fn protects_hypothesis(&self) -> bool {
        self.protect_hypothesis
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::program::Clause;

    fn clause(literal: usize) -> Clause {
        Clause::new(vec![literal], None, 0)
    }

    /// What is offered, in order: the literal of each program clause, then
    /// each hypothesis index plus 100.
    fn drain(mut choices: Choices<'_>) -> Vec<usize> {
        let mut out = Vec::new();
        while let Some(clause) = choices.next() {
            out.push(clause[0]);
        }
        while let Some(index) = choices.next_hypothesis() {
            out.push(100 + index);
        }
        out
    }

    /// The order is the one the old `Vec` + `pop` produced: categories in
    /// reverse, and each category back-to-front.
    #[test]
    fn categories_and_slices_are_consumed_in_reverse() {
        let var = [clause(20), clause(21)];
        let body = [clause(30), clause(31)];

        let choices = Choices::with_hypothesis(2)
            .var_pred(Some(&var))
            .body_preds(&body);

        assert_eq!(
            drain(choices),
            vec![31, 30, 21, 20, 101, 100],
            "body, then meta, then hypothesis -- each back-to-front"
        );
    }

    /// A known predicate's own clauses sit between the body clauses and the
    /// meta clauses, matching the old insertion order.
    #[test]
    fn a_known_predicate_is_tried_before_the_hypothesis() {
        let known = [clause(50), clause(51)];
        let choices = Choices::with_hypothesis(1).known_pred(&known);

        assert_eq!(drain(choices), vec![51, 50, 100]);
    }

    #[test]
    fn empty_categories_and_an_empty_hypothesis_yield_nothing() {
        let choices = Choices::with_hypothesis(0)
            .var_pred(Some(&[]))
            .body_preds(&[]);

        assert_eq!(choices.remaining(), 0);
        assert!(drain(choices).is_empty());
    }

    /// The cursor counts down from the length it was given, so clauses the
    /// search adds after a goal gathered its choices are not offered to it.
    #[test]
    fn hypothesis_clauses_added_later_are_not_offered() {
        assert_eq!(drain(Choices::with_hypothesis(1)), vec![100]);
    }

    /// The cursor only reports protection; `Env::try_hypothesis` does the
    /// skipping, since it needs the clause's substitution to decide.
    #[test]
    fn a_protected_cursor_reports_it_and_still_indexes_every_clause() {
        let protected = Choices::with_protected_hypothesis(2);
        assert!(protected.protects_hypothesis());
        assert_eq!(drain(protected), vec![101, 100]);
        assert!(!Choices::with_hypothesis(2).protects_hypothesis());
    }

    #[test]
    fn remaining_counts_every_category() {
        let var = [clause(20)];
        let body = [clause(40), clause(41)];
        let choices = Choices::with_hypothesis(2)
            .var_pred(Some(&var))
            .body_preds(&body);

        assert_eq!(choices.remaining(), 5);
    }
}
