use std::{collections::HashMap, ops::Deref, ops::Range};

use crate::predicate_modules::PredicateFunction;

use super::Clause;

/// A `(symbol_id, arity)` pair identifying a predicate.
pub(crate) type SymbolArity = (usize, usize);

/// A predicate is either a built-in function or a run of clauses in the
/// table's arena.
///
/// The clause variant holds a *range*, not the clauses themselves: every
/// clause in the program lives in one [`PredicateTable::clauses`] vector, so
/// that walking the clauses of several predicates in a row -- which is what
/// gathering choices for a variable-predicate goal does -- stays within one
/// allocation instead of chasing a separate boxed slice per predicate.
///
/// A range is meaningless without the table that owns the arena, so this type
/// is internal. Callers get [`PredicateRef`], which carries the resolved
/// slice.
#[allow(unpredictable_function_pointer_comparisons)]
#[derive(PartialEq, Eq, Debug, Clone)]
pub(crate) enum Predicate {
    /// A native Rust predicate function.
    Function(PredicateFunction),
    /// Where this predicate's clauses sit in the arena. Never empty.
    Clauses(Range<usize>),
}

/// A predicate as handed to a caller: the function, or the clauses themselves.
///
/// [`Predicate`] stores a range into the arena, which is useful only to the
/// table. This is the resolved form, so a caller reads
/// `PredicateRef::Clauses(clauses)` and gets a slice it can iterate.
#[allow(unpredictable_function_pointer_comparisons)]
#[derive(PartialEq, Debug, Clone, Copy)]
pub enum PredicateRef<'a> {
    /// A native Rust predicate function.
    Function(PredicateFunction),
    /// This predicate's clauses, in source order.
    Clauses(&'a [Clause]),
}

/// Internal entry in the predicate table.
#[derive(PartialEq, Eq, Debug)]
pub struct PredicateEntry {
    symbol_arity: SymbolArity,
    predicate: Predicate,
}

/// One arity's run of the arena.
///
/// The arena is partitioned into blocks, one per arity present in the
/// program, ordered by ascending arity and tiling it without gaps -- so
/// `blocks[i].range.end == blocks[i + 1].range.start`.
///
/// Within a block, the clauses of *body* predicates are packed at the front,
/// in `range.start..body_end`. That is what lets
/// [`PredicateTable::get_body_clauses`] return a single slice: the body
/// clauses of a given arity are contiguous even though they belong to several
/// different predicates, because grouping by arity is a coarser partition
/// than grouping by predicate, so both runs can be contiguous at once.
///
/// This layout is deliberately independent of the order of
/// [`PredicateTable::predicates`], which is sorted by `(symbol, arity)` --
/// symbol first -- and so does not group arities together at all. The ranges
/// held by the entries are therefore *not* monotonic in entry order.
#[derive(PartialEq, Eq, Debug, Clone)]
struct ArityBlock {
    arity: usize,
    /// The whole block.
    range: Range<usize>,
    /// End of the body-predicate run at the front of the block.
    /// `range.start <= body_end <= range.end`.
    body_end: usize,
}

/// The program's predicate table.
///
/// Maps `(symbol, arity)` pairs to predicates (clause runs or built-in
/// functions). Clauses live in one arena; see [`Predicate`] and
/// [`ArityBlock`].
///
/// Which predicates are body predicates is not stored separately: a
/// predicate is a body predicate exactly when its clause range lies inside
/// the body run at the front of its arity block. Keeping it derived rather
/// than listed removes a class of bug -- the previous `body_list` held
/// *positional* indices into `predicates`, which every insertion shifts.
#[derive(Debug, PartialEq)]
pub struct PredicateTable {
    predicates: Vec<PredicateEntry>,
    /// Every clause in the program, laid out as described on [`ArityBlock`].
    clauses: Vec<Clause>,
    /// One per arity present, ascending.
    blocks: Vec<ArityBlock>,
    /// Reverse index from `MetaData::id` to the
    /// meta clause's location, as a `(symbol_arity, clause index)` pair.
    ///
    /// Keyed on `symbol_arity` rather than an index into `predicates` because
    /// `predicates` is kept sorted: inserting a new predicate shifts the entry
    /// indices after it, while the clause index within a predicate is stable --
    /// the only mutation a clause set ever undergoes is the append in
    /// [`Self::add_clause_to_predicate`].
    meta_clause_index: HashMap<usize, (SymbolArity, usize)>,
}

impl Default for PredicateTable {
    fn default() -> Self {
        Self::new()
    }
}

impl PredicateTable {
    pub fn new() -> Self {
        PredicateTable {
            predicates: vec![],
            clauses: vec![],
            blocks: vec![],
            meta_clause_index: HashMap::new(),
        }
    }

    /// The entry index for `symbol_arity`, or `Err` with the index at which
    /// one should be inserted to keep `predicates` sorted.
    ///
    /// `Err` carrying the insertion point is exactly what the callers that
    /// miss want, so the two outcomes stay in one return value. Keys are
    /// unique, so the "which of several equal elements" ambiguity of
    /// `binary_search_by_key` cannot arise here.
    fn find_predicate(&self, symbol_arity: SymbolArity) -> Result<usize, usize> {
        self.predicates
            .binary_search_by_key(&symbol_arity, |entry| entry.symbol_arity)
    }

    // ── arena bookkeeping ───────────────────────────────────────────────

    /// Index of `arity`'s block, or where one would be inserted.
    fn find_block(&self, arity: usize) -> Result<usize, usize> {
        self.blocks.binary_search_by_key(&arity, |b| b.arity)
    }

    /// `arity`'s block, creating an empty one if the arity is new.
    ///
    /// A new block is opened at the start of the next arity's block, which
    /// keeps the blocks tiling the arena without gaps.
    fn block_for(&mut self, arity: usize) -> usize {
        match self.find_block(arity) {
            Ok(i) => i,
            Err(i) => {
                let start = match self.blocks.get(i) {
                    Some(next) => next.range.start,
                    None => self.clauses.len(),
                };
                self.blocks.insert(
                    i,
                    ArityBlock {
                        arity,
                        range: start..start,
                        body_end: start,
                    },
                );
                i
            }
        }
    }

    /// Account for `count` clauses inserted at `at`, owned by `owner`.
    ///
    /// `owner` has to be named rather than inferred from the position:
    /// ranges tile the arena, so when a clause is appended at the end of one
    /// predicate's run that offset is simultaneously the end of `owner` and
    /// the start of the next predicate. Deciding by position alone would
    /// either grow both or neither. The owner grows; everything that starts
    /// at or after `at` moves up.
    ///
    /// The owner's entry must already be in `predicates` -- with an empty
    /// `at..at` range if this is its first clause, which this then grows to
    /// `at..at + count`.
    fn shift_up(&mut self, at: usize, count: usize, owner: SymbolArity) {
        for entry in &mut self.predicates {
            if let Predicate::Clauses(range) = &mut entry.predicate {
                if entry.symbol_arity == owner {
                    range.end += count;
                } else if range.start >= at {
                    range.start += count;
                    range.end += count;
                }
            }
        }
        for block in &mut self.blocks {
            if block.arity == owner.1 {
                block.range.end += count;
                // Only a clause landing *inside* the body run extends it.
                if at < block.body_end {
                    block.body_end += count;
                }
            } else if block.range.start >= at {
                block.range.start += count;
                block.range.end += count;
                block.body_end += count;
            }
        }
    }

    /// Account for the `count` clauses of an `arity` predicate that used to
    /// sit at `at`.
    ///
    /// The owner's entry is expected to be gone from `predicates` already, so
    /// every remaining range starting at or after `at` is strictly after the
    /// hole and moves down.
    fn shift_down(&mut self, at: usize, count: usize, arity: usize) {
        for entry in &mut self.predicates {
            if let Predicate::Clauses(range) = &mut entry.predicate {
                if range.start >= at {
                    range.start -= count;
                    range.end -= count;
                }
            }
        }
        for block in &mut self.blocks {
            if block.arity == arity {
                block.range.end -= count;
                if at < block.body_end {
                    block.body_end -= count;
                }
            } else if block.range.start >= at {
                block.range.start -= count;
                block.range.end -= count;
                block.body_end -= count;
            }
        }
        self.blocks.retain(|block| !block.range.is_empty());
    }

    /// Set the clause range of the entry at `idx`, which must be a clause
    /// predicate.
    fn set_range(&mut self, idx: usize, range: Range<usize>) {
        self.predicates[idx].predicate = Predicate::Clauses(range);
    }

    /// The clause range of a predicate, if it has clauses.
    fn clause_range(&self, symbol_arity: SymbolArity) -> Option<Range<usize>> {
        match &self[self.find_predicate(symbol_arity).ok()?].predicate {
            Predicate::Clauses(range) => Some(range.clone()),
            Predicate::Function(_) => None,
        }
    }

    // ── insertion ───────────────────────────────────────────────────────

    //Inserts a new predicate function to the table
    pub fn insert_predicate_function(
        &mut self,
        symbol_arity: SymbolArity,
        predicate_fn: PredicateFunction,
    ) -> Result<(), &'static str> {
        match self.find_predicate(symbol_arity) {
            Ok(_) => Err("Cannot insert predicate function to clause predicate"),
            Err(insert_idx) => {
                self.predicates.insert(
                    insert_idx,
                    PredicateEntry {
                        symbol_arity,
                        predicate: Predicate::Function(predicate_fn),
                    },
                );
                Ok(())
            }
        }
    }

    /// Adds a clause to an existing entry, or creates a new entry holding it.
    ///
    /// The clause goes at the end of the predicate's existing run, so clauses
    /// keep the order they were loaded in. A new predicate's run opens at the
    /// end of its arity block, after any body-predicate clauses -- a
    /// predicate is never a body predicate at the moment it is created, since
    /// [`Self::set_body`] is called once the program is loaded.
    pub fn add_clause_to_predicate(
        &mut self,
        clause: Clause,
        symbol_arity: SymbolArity,
    ) -> Result<(), &'static str> {
        // Read the id before the clause is moved into the table.
        let meta_clause_id = clause.meta_data.as_ref().map(|meta_data| meta_data.id);

        let (at, clause_idx) = match self.find_predicate(symbol_arity) {
            Ok(idx) => match &self[idx].predicate {
                Predicate::Function(_) => return Err("Cannot add clause to function predicate"),
                Predicate::Clauses(range) => (range.end, range.len()),
            },
            Err(insert_idx) => {
                let block = self.block_for(symbol_arity.1);
                let at = self.blocks[block].range.end;
                self.predicates.insert(
                    insert_idx,
                    PredicateEntry {
                        symbol_arity,
                        predicate: Predicate::Clauses(at..at),
                    },
                );
                (at, 0)
            }
        };

        self.clauses.insert(at, clause);
        self.shift_up(at, 1, symbol_arity);

        if let Some(meta_clause_id) = meta_clause_id {
            self.meta_clause_index
                .insert(meta_clause_id, (symbol_arity, clause_idx));
        }
        Ok(())
    }

    /// Adds a batch of clauses, laying the table out exactly as calling
    /// [`Self::add_clause_to_predicate`] on each in turn would.
    ///
    /// That call rescans every entry per clause, so adding many new
    /// predicates one at a time is quadratic. Here the ranges are shifted
    /// once: a new predicate's clauses go at the end of its arity block, so
    /// an existing range moves by the clauses added to lower arities.
    ///
    /// Nothing is added if any clause names a function predicate.
    pub fn add_clauses(&mut self, batch: Vec<(SymbolArity, Clause)>) -> Result<(), &'static str> {
        let mut new = Vec::with_capacity(batch.len());
        let mut existing = Vec::new();
        for (symbol_arity, clause) in batch {
            match self.find_predicate(symbol_arity) {
                Ok(idx) if matches!(self[idx].predicate, Predicate::Function(_)) => {
                    return Err("Cannot add clause to function predicate")
                }
                Ok(_) => existing.push((symbol_arity, clause)),
                Err(_) => new.push((symbol_arity, clause)),
            }
        }
        // Growing an existing run inserts mid-block, which the batch path
        // does not handle.
        for (symbol_arity, clause) in existing {
            self.add_clause_to_predicate(clause, symbol_arity)?;
        }
        if new.is_empty() {
            return Ok(());
        }

        // Group by arity, then by predicate in order of first appearance.
        let mut first = HashMap::new();
        for (i, (symbol_arity, _)) in new.iter().enumerate() {
            first.entry(*symbol_arity).or_insert(i);
        }
        new.sort_by_cached_key(|(symbol_arity, _)| (symbol_arity.1, first[symbol_arity]));

        // Each new predicate with its clause count, and each arity with its.
        let mut runs: Vec<(SymbolArity, usize)> = Vec::new();
        let mut counts: Vec<(usize, usize)> = Vec::new();
        for (symbol_arity, clause) in &new {
            if runs.last().map(|run| run.0) != Some(*symbol_arity) {
                runs.push((*symbol_arity, 0));
            }
            if counts.last().map(|count| count.0) != Some(symbol_arity.1) {
                counts.push((symbol_arity.1, 0));
            }
            let run_len = &mut runs.last_mut().unwrap().1;
            if let Some(meta_data) = &clause.meta_data {
                self.meta_clause_index
                    .insert(meta_data.id, (*symbol_arity, *run_len));
            }
            *run_len += 1;
            counts.last_mut().unwrap().1 += 1;
        }

        // Highest arity first, so each block's end is still where it was.
        for &(arity, count) in counts.iter().rev() {
            let block = self.block_for(arity);
            let at = self.blocks[block].range.end;
            let clauses = new.split_off(new.len() - count);
            self.clauses
                .splice(at..at, clauses.into_iter().map(|(_, clause)| clause));
        }

        // Move each block up by the clauses added below it, and grow it by
        // its own.
        let mut shift = 0;
        let mut shifts = Vec::with_capacity(self.blocks.len());
        for block in &mut self.blocks {
            let count = counts
                .binary_search_by_key(&block.arity, |count| count.0)
                .map_or(0, |i| counts[i].1);
            block.range.start += shift;
            block.body_end += shift;
            block.range.end += shift + count;
            shifts.push(shift);
            shift += count;
        }
        for entry in &mut self.predicates {
            if let Predicate::Clauses(range) = &mut entry.predicate {
                let block = self
                    .blocks
                    .binary_search_by_key(&entry.symbol_arity.1, |block| block.arity)
                    .expect("a clause predicate always has a block for its arity");
                range.start += shifts[block];
                range.end += shifts[block];
            }
        }

        // The new clauses fill the last `count` slots of their block.
        let mut counts = counts.into_iter().peekable();
        let mut at = 0;
        let mut arity = None;
        for (symbol_arity, len) in runs {
            if arity != Some(symbol_arity.1) {
                arity = Some(symbol_arity.1);
                let (_, count) = counts.next().unwrap();
                let block = self.find_block(symbol_arity.1).unwrap();
                at = self.blocks[block].range.end - count;
            }
            self.predicates.push(PredicateEntry {
                symbol_arity,
                predicate: Predicate::Clauses(at..at + len),
            });
            at += len;
        }
        self.predicates
            .sort_unstable_by_key(|entry| entry.symbol_arity);
        Ok(())
    }

    // ── lookup ──────────────────────────────────────────────────────────

    /// Look up a meta clause by its `MetaData::id`.
    ///
    /// Used to recover the template a
    /// `MetaSub` was recorded against, since a
    /// `MetaSub` stores only the id and the substitution, not the clause.
    pub fn get_meta_clause(&self, meta_clause_id: usize) -> Option<&Clause> {
        let (symbol_arity, clause_idx) = *self.meta_clause_index.get(&meta_clause_id)?;
        let range = self.clause_range(symbol_arity)?;
        self.clauses.get(range.start + clause_idx)
    }

    //Get predicate by SymbolArity key
    pub fn get_predicate(&self, symbol_arity: SymbolArity) -> Option<PredicateRef<'_>> {
        Some(
            match &self[self.find_predicate(symbol_arity).ok()?].predicate {
                Predicate::Function(f) => PredicateRef::Function(*f),
                Predicate::Clauses(range) => PredicateRef::Clauses(&self.clauses[range.clone()]),
            },
        )
    }

    /// The clauses of a predicate, or `None` if it is unknown or a function.
    pub fn get_predicate_clauses(&self, symbol_arity: SymbolArity) -> Option<&[Clause]> {
        let range = self.clause_range(symbol_arity)?;
        Some(&self.clauses[range])
    }

    /// The meta clauses for `arity` -- those stored under the variable
    /// predicate symbol `0`.
    pub fn get_variable_clauses(&self, arity: usize) -> Option<&[Clause]> {
        self.get_predicate_clauses((0, arity))
    }

    /// Every body-predicate clause of this arity, as one slice.
    ///
    /// One slice rather than an iterator over several, because the body
    /// clauses of an arity are packed at the front of its block; see
    /// [`ArityBlock`]. Empty when no body predicate has this arity.
    pub fn get_body_clauses(&self, arity: usize) -> &[Clause] {
        match self.find_block(arity) {
            Ok(i) => {
                let block = &self.blocks[i];
                &self.clauses[block.range.start..block.body_end]
            }
            Err(_) => &[],
        }
    }

    // ── removal and body designation ────────────────────────────────────

    //Remove predicate by SymbolArity key
    pub fn remove_predicate(&mut self, symbol_arity: SymbolArity) {
        let Ok(predicate_idx) = self.find_predicate(symbol_arity) else {
            return;
        };
        let removed = self.predicates.remove(predicate_idx).predicate;
        if let Predicate::Clauses(range) = removed {
            self.clauses.drain(range.clone());
            self.shift_down(range.start, range.len(), symbol_arity.1);
            // The clauses are gone, so any meta clause ids pointing at them
            // would resolve to whatever predicate later takes this key.
            self.meta_clause_index
                .retain(|_, (indexed_symbol_arity, _)| *indexed_symbol_arity != symbol_arity);
        }
    }

    /// Add or remove a predicate from the body-predicate set.
    ///
    /// Body-ness is a position in the arena rather than a flag, so this
    /// *moves* the predicate's clauses: to the front of the non-body part of
    /// its arity block when set, and to the end of the body part when
    /// cleared. Both are a rotation within the block, so no other block and
    /// no other arity is disturbed.
    pub fn set_body(&mut self, symbol_arity: SymbolArity, value: bool) -> Result<(), &str> {
        let Ok(idx) = self.find_predicate(symbol_arity) else {
            return Ok(()); //Err("Can't set non existing predicate to body"),
        };
        let range = match &self[idx].predicate {
            Predicate::Function(_) => return Err("Can't set predicate function to body"),
            Predicate::Clauses(range) => range.clone(),
        };
        let block_idx = self
            .find_block(symbol_arity.1)
            .expect("a clause predicate always has a block for its arity");
        let body_end = self.blocks[block_idx].body_end;
        let len = range.len();

        if value {
            if range.end <= body_end {
                return Ok(()); // already a body predicate
            }
            // Move [range.start, range.end) down to body_end.
            self.clauses[body_end..range.end].rotate_right(len);
            for entry in &mut self.predicates {
                if let Predicate::Clauses(other) = &mut entry.predicate {
                    if other.start >= body_end && other.end <= range.start {
                        other.start += len;
                        other.end += len;
                    }
                }
            }
            self.set_range(idx, body_end..body_end + len);
            self.blocks[block_idx].body_end += len;
        } else {
            if range.end > body_end {
                return Ok(()); // already not a body predicate
            }
            // Move [range.start, range.end) up to the end of the body run.
            self.clauses[range.start..body_end].rotate_left(len);
            for entry in &mut self.predicates {
                if let Predicate::Clauses(other) = &mut entry.predicate {
                    if other.start >= range.end && other.end <= body_end {
                        other.start -= len;
                        other.end -= len;
                    }
                }
            }
            self.set_range(idx, body_end - len..body_end);
            self.blocks[block_idx].body_end -= len;
        }
        Ok(())
    }

    /// Panics unless the arena layout invariants hold.
    ///
    /// Blocks tile the arena in ascending arity without gaps or overlap, each
    /// block's body run is within it, and every predicate's range lies inside
    /// the block for its own arity. Called from the tests, and cheap enough
    /// to call from a `debug_assert` if a future change makes the
    /// bookkeeping harder to trust.
    #[cfg(test)]
    pub(crate) fn assert_layout(&self) {
        let mut expected_start = 0;
        let mut last_arity = None;
        for block in &self.blocks {
            assert_eq!(
                block.range.start, expected_start,
                "blocks must tile the arena without gaps: {:?}",
                self.blocks
            );
            assert!(
                block.range.start <= block.body_end && block.body_end <= block.range.end,
                "body run must lie inside its block: {block:?}"
            );
            assert!(
                !block.range.is_empty(),
                "an empty block should have been dropped: {block:?}"
            );
            if let Some(last) = last_arity {
                assert!(last < block.arity, "blocks must ascend by arity");
            }
            last_arity = Some(block.arity);
            expected_start = block.range.end;
        }
        assert_eq!(
            expected_start,
            self.clauses.len(),
            "blocks must cover the whole arena"
        );

        let mut covered = vec![false; self.clauses.len()];
        for entry in &self.predicates {
            let Predicate::Clauses(range) = &entry.predicate else {
                continue;
            };
            assert!(!range.is_empty(), "a clause predicate must own a clause");
            assert!(
                range.end <= self.clauses.len(),
                "range {range:?} out of bounds"
            );
            let block = &self.blocks[self
                .find_block(entry.symbol_arity.1)
                .expect("every clause predicate has a block")];
            assert!(
                range.start >= block.range.start && range.end <= block.range.end,
                "{:?}'s range {range:?} escapes its arity block {block:?}",
                entry.symbol_arity
            );
            for slot in &mut covered[range.clone()] {
                assert!(!*slot, "ranges overlap at {range:?}");
                *slot = true;
            }
        }
        assert!(
            covered.iter().all(|c| *c),
            "every clause in the arena must belong to some predicate"
        );
    }
}

/// Read-only access to the entries, so `len`, `iter` and indexing work as
/// they did when the table was a bare `Vec`.
///
/// Deliberately not `DerefMut`: inserting or removing an entry through the
/// `Vec` would bypass the arena bookkeeping in [`PredicateTable::shift_up`]
/// and [`PredicateTable::shift_down`] and leave the ranges pointing at the
/// wrong clauses.
impl Deref for PredicateTable {
    type Target = Vec<PredicateEntry>;

    fn deref(&self) -> &Self::Target {
        &self.predicates
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{super::Clause, Predicate, PredicateRef, PredicateTable};
    use crate::{
        heap::{test_prog, Heap, ProgramHeap, QueryHeap},
        predicate_modules::PredReturn,
        program::Hypothesis,
        Config,
    };

    fn pred_fn_placeholder(
        _heap: &mut QueryHeap,
        _hypothesis: &mut Hypothesis,
        _goal: usize,
        _predicate_table: &PredicateTable,
        _config: Config,
    ) -> PredReturn {
        PredReturn::True
    }

    fn clause(literals: Vec<usize>) -> Clause {
        Clause::new(literals, None, 0)
    }

    /// A table with four entries, built through the public API so the arena
    /// bookkeeping is exercised rather than bypassed.
    ///
    /// `(p, 2)` is the body predicate, as in the original fixture. All four
    /// predicates have arity 2, so they share one arity block -- which is
    /// what makes the body-packing rotation observable.
    fn setup() -> (PredicateTable, usize, usize, usize) {
        let prog = test_prog();
        let p = prog.symbols().set_const("p");
        let q = prog.symbols().set_const("q");
        let pred_func = prog.symbols().set_const("func");

        let mut table = PredicateTable::new();
        for (sa, literals) in [
            ((0, 2), vec![0, 3]),
            ((0, 2), vec![7, 11]),
            ((p, 2), vec![15, 19]),
            ((p, 2), vec![23, 27]),
            ((q, 2), vec![31, 35]),
            ((q, 2), vec![39, 43]),
        ] {
            table.add_clause_to_predicate(clause(literals), sa).unwrap();
        }
        table
            .insert_predicate_function((pred_func, 2), pred_fn_placeholder)
            .unwrap();
        table.set_body((p, 2), true).unwrap();
        table.assert_layout();

        (table, p, q, pred_func)
    }

    /// `add_clauses` must leave the same table as one insert per clause.
    fn assert_bulk_matches_single(
        base: &[((usize, usize), Vec<usize>)],
        body: &[(usize, usize)],
        batch: &[((usize, usize), Vec<usize>)],
    ) {
        let build = || {
            let mut table = PredicateTable::new();
            for (sa, literals) in base {
                table
                    .add_clause_to_predicate(clause(literals.clone()), *sa)
                    .unwrap();
            }
            for sa in body {
                table.set_body(*sa, true).unwrap();
            }
            table
        };

        let mut single = build();
        for (sa, literals) in batch {
            single
                .add_clause_to_predicate(clause(literals.clone()), *sa)
                .unwrap();
        }

        let mut bulk = build();
        bulk.add_clauses(
            batch
                .iter()
                .map(|(sa, literals)| (*sa, clause(literals.clone())))
                .collect(),
        )
        .unwrap();

        bulk.assert_layout();
        assert_eq!(bulk, single);
    }

    #[test]
    fn add_clauses_matches_single_inserts_across_arities() {
        assert_bulk_matches_single(
            &[
                ((1, 1), vec![1]),
                ((2, 2), vec![2]),
                ((3, 2), vec![3]),
                ((4, 4), vec![4]),
            ],
            &[(2, 2)],
            &[
                ((10, 2), vec![10]),
                ((11, 1), vec![11]),
                ((12, 4), vec![12]),
                ((13, 2), vec![13]),
                ((14, 1), vec![14]),
            ],
        );
    }

    #[test]
    fn add_clauses_opens_blocks_for_new_arities() {
        assert_bulk_matches_single(
            &[((1, 2), vec![1]), ((2, 4), vec![2])],
            &[],
            &[
                ((10, 3), vec![10]),
                ((11, 5), vec![11]),
                ((12, 1), vec![12]),
                ((13, 3), vec![13]),
            ],
        );
        assert_bulk_matches_single(&[], &[], &[((10, 2), vec![10]), ((11, 1), vec![11])]);
    }

    #[test]
    fn add_clauses_keeps_a_predicates_scattered_clauses_together() {
        // Two mutually recursive predicates whose clauses interleave.
        assert_bulk_matches_single(
            &[((1, 2), vec![1])],
            &[],
            &[
                ((10, 2), vec![10]),
                ((11, 2), vec![11]),
                ((10, 2), vec![12]),
                ((11, 2), vec![13]),
                ((10, 2), vec![14]),
            ],
        );
    }

    #[test]
    fn add_clauses_extends_predicates_already_in_the_table() {
        assert_bulk_matches_single(
            &[((1, 2), vec![1]), ((2, 2), vec![2]), ((3, 3), vec![3])],
            &[(1, 2)],
            &[
                ((10, 2), vec![10]),
                ((1, 2), vec![11]),
                ((2, 2), vec![12]),
                ((10, 2), vec![13]),
                ((3, 3), vec![14]),
            ],
        );
    }

    #[test]
    fn add_clauses_to_a_function_predicate_adds_nothing() {
        let (mut table, _p, _q, pred_func) = setup();
        let (before, _, _, _) = setup();

        let result = table.add_clauses(vec![
            ((900, 2), clause(vec![1])),
            ((pred_func, 2), clause(vec![2])),
        ]);

        assert!(result.is_err());
        assert_eq!(table, before);
    }

    #[test]
    fn find_predicate() {
        let prog = test_prog();
        let (pred_table, p, _q, _pred_func) = setup();

        let symbol = prog.symbols().set_const("find_predicate_test_symbol");
        let p_idx = pred_table
            .iter()
            .position(|e| e.symbol_arity == (p, 2))
            .unwrap();

        assert_eq!(pred_table.find_predicate((0, 1)), Err(0));
        assert_eq!(pred_table.find_predicate((p, 2)), Ok(p_idx));

        // A symbol larger than all entries should go at the end
        assert_eq!(
            pred_table.find_predicate((symbol, 2)),
            if symbol > pred_table.last().unwrap().symbol_arity.0 {
                Err(pred_table.len())
            } else {
                pred_table.find_predicate((symbol, 2))
            }
        );

        // Same symbol, different arity should get an insert position
        assert_eq!(pred_table.find_predicate((p, 1)), Err(p_idx));

        let pred_table = PredicateTable::new();
        assert_eq!(pred_table.find_predicate((50, 2)), Err(0));
    }

    #[test]
    fn get_predicate() {
        let (pred_table, p, _q, pred_func) = setup();

        assert_eq!(pred_table.get_predicate((p, 3)), None);
        assert_eq!(
            pred_table.get_predicate((p, 2)),
            Some(PredicateRef::Clauses(&[
                clause(vec![15, 19]),
                clause(vec![23, 27]),
            ]))
        );
        assert_eq!(
            pred_table.get_predicate((pred_func, 2)),
            Some(PredicateRef::Function(pred_fn_placeholder))
        );
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)),
            Some(&[clause(vec![15, 19]), clause(vec![23, 27])][..])
        );
        assert_eq!(
            pred_table.get_predicate_clauses((pred_func, 2)),
            None,
            "a function predicate has no clauses"
        );
    }

    #[test]
    fn insert_predicate_function() {
        let (mut pred_table, p, _q, pred_func) = setup();

        assert_eq!(
            pred_table.insert_predicate_function((p, 2), pred_fn_placeholder),
            Err("Cannot insert predicate function to clause predicate")
        );

        pred_table
            .insert_predicate_function((pred_func, 3), pred_fn_placeholder)
            .unwrap();
        assert_eq!(
            pred_table.get_predicate((pred_func, 3)),
            Some(PredicateRef::Function(pred_fn_placeholder))
        );
        pred_table.assert_layout();
    }

    #[test]
    fn add_clause_to_predicate() {
        let prog = test_prog();
        let (mut pred_table, p, _q, pred_func) = setup();
        let r = prog.symbols().set_const("r");

        let dummy_meta = Clause::new(vec![99], Some((vec![], vec![])), 0);
        let meta_id = dummy_meta.meta_data.unwrap().id;

        // Appending to an existing predicate keeps load order.
        pred_table
            .add_clause_to_predicate(dummy_meta, (p, 2))
            .unwrap();
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)).unwrap().len(),
            3,
            "the clause should join p/2's existing run"
        );
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)).unwrap()[2][0],
            99,
            "and go at the end of it"
        );
        assert_eq!(
            pred_table.get_meta_clause(meta_id).map(|c| c[0]),
            Some(99),
            "the meta clause index must still resolve after the arena shifted"
        );
        pred_table.assert_layout();

        // A brand new predicate of a new arity opens its own block.
        pred_table
            .add_clause_to_predicate(clause(vec![100]), (r, 1))
            .unwrap();
        assert_eq!(
            pred_table.get_predicate_clauses((r, 1)).unwrap(),
            &[clause(vec![100])]
        );
        pred_table.assert_layout();

        // Every other predicate's clauses must have survived the shuffling.
        assert_eq!(
            pred_table.get_predicate_clauses((0, 2)).unwrap(),
            &[clause(vec![0, 3]), clause(vec![7, 11])]
        );
        assert_eq!(pred_table.get_predicate_clauses((pred_func, 2)), None);

        assert_eq!(
            pred_table.add_clause_to_predicate(clause(vec![0]), (pred_func, 2)),
            Err("Cannot add clause to function predicate")
        );
    }

    #[test]
    fn remove_predicate() {
        let (mut pred_table, p, q, _pred_func) = setup();

        let before = pred_table.clauses.len();
        pred_table.remove_predicate((q, 2));
        assert_eq!(pred_table.get_predicate((q, 2)), None);
        assert_eq!(
            pred_table.clauses.len(),
            before - 2,
            "q/2's two clauses should have left the arena"
        );
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)).unwrap(),
            &[clause(vec![15, 19]), clause(vec![23, 27])],
            "p/2 must still resolve to its own clauses"
        );
        assert_eq!(
            pred_table.get_body_clauses(2),
            &[clause(vec![15, 19]), clause(vec![23, 27])],
            "and must still be a body predicate"
        );
        pred_table.assert_layout();

        // Removing the body predicate shrinks the body run.
        pred_table.remove_predicate((p, 2));
        assert!(pred_table.get_body_clauses(2).is_empty());
        pred_table.assert_layout();

        // Removing the last clause predicate of an arity drops its block.
        pred_table.remove_predicate((0, 2));
        assert!(pred_table.blocks.is_empty());
        assert!(pred_table.clauses.is_empty());
        pred_table.assert_layout();
    }

    #[test]
    fn set_body() {
        let (mut pred_table, p, q, pred_func) = setup();

        assert_eq!(
            pred_table.set_body((pred_func, 2), true),
            Err("Can't set predicate function to body")
        );

        // p/2 was set in the fixture.
        assert_eq!(
            pred_table.get_body_clauses(2),
            &[clause(vec![15, 19]), clause(vec![23, 27])]
        );

        // Adding q/2 extends the body run; both predicates keep their own
        // clauses even though the rotation moved them.
        pred_table.set_body((q, 2), true).unwrap();
        pred_table.assert_layout();
        assert_eq!(pred_table.get_body_clauses(2).len(), 4);
        assert_eq!(
            pred_table.get_predicate_clauses((q, 2)).unwrap(),
            &[clause(vec![31, 35]), clause(vec![39, 43])]
        );
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)).unwrap(),
            &[clause(vec![15, 19]), clause(vec![23, 27])]
        );
        assert_eq!(
            pred_table.get_predicate_clauses((0, 2)).unwrap(),
            &[clause(vec![0, 3]), clause(vec![7, 11])],
            "the non-body predicate was pushed back but is otherwise intact"
        );

        // Clearing is the inverse.
        pred_table.set_body((p, 2), false).unwrap();
        pred_table.assert_layout();
        assert_eq!(
            pred_table.get_body_clauses(2),
            &[clause(vec![31, 35]), clause(vec![39, 43])]
        );
        assert_eq!(
            pred_table.get_predicate_clauses((p, 2)).unwrap(),
            &[clause(vec![15, 19]), clause(vec![23, 27])]
        );

        // Idempotent in both directions.
        pred_table.set_body((p, 2), false).unwrap();
        pred_table.set_body((q, 2), true).unwrap();
        pred_table.assert_layout();
        assert_eq!(pred_table.get_body_clauses(2).len(), 2);
    }

    #[test]
    fn get_body_clauses() {
        let (mut pred_table, _p, q, _pred_func) = setup();

        // No body predicate has arity 1, and no predicate has arity 7.
        assert!(pred_table.get_body_clauses(1).is_empty());
        assert!(pred_table.get_body_clauses(7).is_empty());

        assert_eq!(
            pred_table.get_body_clauses(2),
            &[clause(vec![15, 19]), clause(vec![23, 27])]
        );

        pred_table.set_body((q, 2), true).unwrap();
        assert_eq!(
            pred_table.get_body_clauses(2).len(),
            4,
            "both body predicates' clauses come back as one slice"
        );
    }

    /// Body clauses of one arity stay contiguous even with another arity
    /// interleaved, which is the property that lets `get_body_clauses`
    /// return a single slice.
    #[test]
    fn body_runs_stay_contiguous_across_arities() {
        let prog = test_prog();
        let [a, b] = ["arity_mix_a", "arity_mix_b"].map(|s| prog.symbols().set_const(s));

        let mut table = PredicateTable::new();
        // Interleave the arities on insertion so the blocks cannot be
        // contiguous by accident of ordering.
        for (sa, lit) in [
            ((a, 1), 1),
            ((b, 2), 2),
            ((a, 1), 3),
            ((b, 2), 4),
            ((a, 2), 5),
            ((b, 1), 6),
        ] {
            table
                .add_clause_to_predicate(clause(vec![lit]), sa)
                .unwrap();
        }
        table.set_body((b, 1), true).unwrap();
        table.set_body((b, 2), true).unwrap();
        table.assert_layout();

        assert_eq!(table.get_body_clauses(1), &[clause(vec![6])]);
        assert_eq!(
            table.get_body_clauses(2),
            &[clause(vec![2]), clause(vec![4])]
        );
        assert_eq!(
            table.get_predicate_clauses((a, 1)).unwrap(),
            &[clause(vec![1]), clause(vec![3])]
        );
        assert_eq!(
            table.get_predicate_clauses((a, 2)).unwrap(),
            &[clause(vec![5])]
        );
    }

    /// Adding a predicate after body designation must not corrupt the body
    /// run -- the hazard the old positional `body_list` had, where inserting
    /// an entry ahead of a body predicate shifted the index pointing at it
    /// without the list being told.
    ///
    /// Uses its own program heap so the interning order, and therefore the
    /// entry order, can be chosen: `early` is interned first and so sorts
    /// before the body predicate.
    #[test]
    fn a_predicate_added_after_body_designation_keeps_the_body_run_intact() {
        let prog = ProgramHeap::new();
        let early = prog.symbols().set_const("early");
        let body = prog.symbols().set_const("body_pred");
        assert!(early < body, "interning order should order the symbol ids");

        let mut table = PredicateTable::new();
        table
            .add_clause_to_predicate(clause(vec![10]), (body, 2))
            .unwrap();
        table.set_body((body, 2), true).unwrap();
        assert_eq!(table.get_body_clauses(2), &[clause(vec![10])]);

        // Inserts at entry index 0, ahead of the body predicate.
        table
            .add_clause_to_predicate(clause(vec![20]), (early, 2))
            .unwrap();
        table.assert_layout();
        assert_eq!(
            table.iter().next().unwrap().symbol_arity,
            (early, 2),
            "the new entry should indeed sort first, or the test proves nothing"
        );

        assert_eq!(
            table.get_body_clauses(2),
            &[clause(vec![10])],
            "the body run must still be the body predicate's clause"
        );
        assert_eq!(
            table.get_predicate_clauses((early, 2)).unwrap(),
            &[clause(vec![20])]
        );
    }

    #[test]
    fn meta_clause_index_survives_arena_shifts() {
        let prog = test_prog();
        let mut table = PredicateTable::new();
        let z = prog.symbols().set_const("meta_idx_z");

        // Arity 1, because arg 0 is declared a meta variable: a clause that
        // claims zero variables cannot have one. This test only cares that the
        // meta clause *ids* survive an arena shift, not about the vars.
        let first = Clause::new(vec![1], Some((vec![0], vec![0])), 1);
        let second = Clause::new(vec![2], Some((vec![0], vec![0])), 1);
        let (id1, id2) = (first.meta_data.unwrap().id, second.meta_data.unwrap().id);

        table.add_clause_to_predicate(first, (0, 2)).unwrap();
        table.add_clause_to_predicate(second, (0, 2)).unwrap();
        // Insert a lower-arity predicate, which opens a block *before* the
        // meta clauses and shifts their range.
        table
            .add_clause_to_predicate(clause(vec![3]), (z, 1))
            .unwrap();
        table.assert_layout();

        assert_eq!(table.get_meta_clause(id1).map(|c| c[0]), Some(1));
        assert_eq!(table.get_meta_clause(id2).map(|c| c[0]), Some(2));
    }

    /// The arena holds every clause exactly once, so a predicate's clauses
    /// are one contiguous run and the whole program is one allocation.
    #[test]
    fn the_arena_holds_every_clause_once() {
        let (pred_table, _p, _q, _pred_func) = setup();
        assert_eq!(
            pred_table.clauses.len(),
            6,
            "six clauses were inserted, so six should be in the arena"
        );
        let mut seen = HashMap::new();
        for entry in pred_table.iter() {
            if let Predicate::Clauses(range) = &entry.predicate {
                seen.insert(entry.symbol_arity, range.len());
            }
        }
        assert_eq!(seen.values().sum::<usize>(), 6);
    }
}
