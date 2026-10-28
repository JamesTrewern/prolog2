use std::{
    collections::{HashMap, HashSet},
    io::{self, Write},
    ops::{Deref, DerefMut, Index},
};

use crate::{
    heap::{Cell, Heap, QueryHeap, Tag::Con},
    parser::{build_clause, tokenise, TokenStream},
    program::{
        clause::Clause,
        predicate_table::{Predicate, PredicateTable},
    },
    resolution::Proof,
    Config,
};

#[derive(Clone, Copy)]
pub(super) struct Coverage(pub u128);

impl Deref for Coverage {
    type Target = u128;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl DerefMut for Coverage {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Coverage {
    pub fn from_len(len: usize) -> Self {
        if len > 128 {
            todo!("More than 128 pos examples not yet implemented");
        }
        let mask = u128::MAX << len;
        Self(mask)
    }

    pub fn sub_set(&self, other: &Self) -> bool {
        other.0 | self.0 == other.0
    }

    /// How many bits set in self not set in other
    pub fn difference(&self, other: &Self) -> usize {
        (self.0 & !other.0).count_ones() as usize
    }

    pub fn count(&self, max_bit: usize) -> usize {
        (self.0 & !(u128::MAX << max_bit)).count_ones() as usize
    }

    pub fn set(&mut self, i: usize) {
        self.0 |= 1 << i
    }

    pub fn get(&self, i: usize) -> bool {
        self.0 & 1 << i != 0
    }

    pub fn all(&self) -> bool {
        self.0 == u128::MAX
    }

    pub fn _none(&self) -> bool {
        self.0 == 0
    }
}

/// Parse a single example string into a goal on the given query heap.
pub(super) fn parse_example(example: &str, query_heap: &mut QueryHeap) -> Result<usize, String> {
    let literals = TokenStream::new(tokenise(example).map_err(|e| e.to_string())?)
        .parse_goals()
        .map_err(|e| format!("Example '{example}' incorrectly formatted: {e}"))?;
    let heap_id = query_heap.id;
    let clause = build_clause(literals, None, query_heap, Some(heap_id));
    Ok(clause[0])
}
/// Count how many positive examples a set of clauses can prove.
pub(super) fn count_coverage(
    pos_examples: &[String],
    clauses: &[Clause],
    heap: &[Cell],
    predicate_table: &PredicateTable,
    max_depth: usize,
) -> (Coverage, usize) {
    let config = Config {
        max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: false,
    };

    let mut coverage = Coverage::from_len(pos_examples.len());

    for (i, example) in pos_examples.into_iter().enumerate() {
        let mut query_heap = QueryHeap::new(heap, None);
        let Ok(goal) = parse_example(example, &mut query_heap) else {
            panic!("Could not parse example {example}");
        };
        let mut proof = Proof::new(&query_heap, &[goal]);
        proof.add_test_clauses(clauses);
        if proof.prove(&mut query_heap, predicate_table, config) {
            coverage.set(i);
        }
    }
    let count = coverage.count(pos_examples.len());
    (coverage, count)
}

/// Combine a group's sub hypotheses into one clause list, dropping clauses
/// that appear in more than one of them.
pub(super) fn union_sub_hypotheses(
    sub_hypotheses: Vec<Vec<Clause>>,
    heap: &impl Heap,
) -> Vec<Clause> {
    let mut top_program = Vec::new();
    let mut seen = HashSet::new();
    for hypothesis in sub_hypotheses {
        for clause in hypothesis {
            let key = clause.to_string(heap);
            if seen.insert(key) {
                top_program.push(clause);
            }
        }
    }
    top_program
}

/// The `(symbol, arity)` of a body literal naming an invented predicate, or
/// `None` when it names a background one.
///
/// Membership of `pred_symbols` is the test. The previous one -- symbol id
/// greater than that of `pred_0` -- assumed every background predicate was
/// interned before the first invented one. `SymbolDB` is process-global, so
/// anything that interned `pred_0` earlier (another example in the same run,
/// another test in the same binary) pushed the background predicates above
/// the threshold and swept the whole fact base into the output.
fn invented_body_pred<H>(
    heap: &H,
    literal: usize,
    pred_symbols: &HashSet<usize>,
) -> Option<(usize, usize)>
where
    H: Index<usize, Output = Cell> + ?Sized,
{
    // Only a constant can name a predicate here; an `Arg` or `Ref` cell's
    // value is an argument id or variable id, which would collide with
    // symbol ids by coincidence.
    let (Con, symbol) = heap[literal + 1] else {
        return None;
    };
    if !pred_symbols.contains(&symbol) {
        return None;
    }
    // The `Comp` cell counts the functor as well as the arguments.
    Some((symbol, heap[literal].1 - 1))
}

pub(super) fn collect_used_pred(
    hypothesis: &mut Vec<Clause>,
    heap: &impl Heap,
    predicate_table: &PredicateTable,
    pred_symbols: &HashSet<usize>,
) {
    let mut pred_set = HashMap::new();
    loop {
        let start_len = pred_set.len();
        for clause in hypothesis.iter() {
            for literal in clause.body() {
                if let Some((symbol, arity)) = invented_body_pred(heap, *literal, pred_symbols) {
                    pred_set.insert(symbol, (arity, false));
                }
            }
        }
        if start_len == pred_set.len() {
            break;
        }
        for (symbol, (arity, collected)) in pred_set.iter_mut() {
            if !*collected {
                let Predicate::Clauses(clauses) =
                    predicate_table.get_predicate((*symbol, *arity)).unwrap()
                else {
                    panic!();
                };
                hypothesis.extend_from_slice(clauses);
                *collected = true
            }
        }
    }
}

/// Count how many predicate clauses are used hypothesis
pub(super) fn count_pred_clauses(
    h: &Box<[Clause]>,
    heap: &[Cell],
    predicate_table: &PredicateTable,
    pred_symbols: &HashSet<usize>,
) -> usize {
    let mut count = 0;
    let mut pred_set = HashSet::new();
    let mut pred_list = Vec::new();
    for clause in h.iter() {
        for literal in clause.body() {
            if let Some(symbol_arity) = invented_body_pred(heap, *literal, pred_symbols) {
                if pred_set.insert(symbol_arity) {
                    pred_list.push(symbol_arity);
                }
            }
        }
    }
    while let Some(symbol_arity) = pred_list.pop() {
        let Predicate::Clauses(clauses) = predicate_table.get_predicate(symbol_arity).unwrap()
        else {
            panic!();
        };
        count += clauses.len();
        for clause in clauses.iter() {
            for literal in clause.body() {
                if let Some(symbol_arity) = invented_body_pred(heap, *literal, pred_symbols) {
                    if pred_set.insert(symbol_arity) {
                        pred_list.push(symbol_arity);
                    }
                }
            }
        }
    }
    count
}

/// Plotkin's program reduction (Algorithm 3).
/// Sequentially tries removing each clause; if all positives are still provable
/// without it, the clause is redundant and permanently removed.
pub(super) fn reduce(
    pos_examples: &[String],
    mut hypothesis: Vec<Clause>,
    heap: &[Cell],
    predicate_table: &PredicateTable,
    config: Config,
    verbose: bool,
) -> Vec<Clause> {
    let config = Config {
        max_depth: config.max_depth,
        max_clause: 0,
        debug: false,
        protect_h_preds: config.protect_h_preds,
    };

    // New reduction method
    // pop clause
    // check coverage if same continue
    // if less coverage add clause to front (design vec with easy front adding)
    // loop until clauses_considered == initial size

    let total = hypothesis.len();
    let mut removed = 0usize;
    let mut i = 0;
    while i < hypothesis.len() {
        if verbose {
            eprint!(
                "\rReduce: {}/{total} checked, {removed} removed    ",
                i + removed + 1
            );
            let _ = io::stderr().flush();
        }

        let c = hypothesis.remove(i);

        // Check if all positive examples are still provable without clause i
        let redundant = pos_examples.iter().all(|example| {
            let mut query_heap = QueryHeap::new(heap, None);
            let goal = match parse_example(example, &mut query_heap) {
                Ok(g) => g,
                Err(_) => return true, // skip unparseable examples
            };
            let mut proof = Proof::new(&query_heap, &[goal]);
            proof.add_test_clauses(&hypothesis);
            proof.prove(&mut query_heap, predicate_table, config)
        });

        if redundant {
            removed += 1;
            // Don't increment i — next clause slides into this position
        } else {
            hypothesis.insert(i, c);
            i += 1;
        }
    }
    if verbose {
        eprintln!(" ...done");
    }

    hypothesis
}

#[cfg(test)]
mod tests {
    use crate::learners::utils::Coverage;

    #[test]
    fn coverage_sub_set() {
        let mut a = Coverage::from_len(4);
        let mut b = Coverage::from_len(4);

        a.set(0);
        a.set(1);
        b.set(1);
        assert!(!a.sub_set(&b));
        assert!(b.sub_set(&a));

        b.set(0);
        assert!(a.sub_set(&b));
        assert!(b.sub_set(&a));
    }
}
