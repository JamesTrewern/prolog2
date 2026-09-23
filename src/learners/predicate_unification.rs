use std::cmp::Ordering;

use crate::{
    heap::{Heap, SymbolDB, Tag::*, TermWalk, Walk},
    program::clause::Clause,
};

pub struct PredDef {
    clauses: Vec<Clause>,
    // symbol: usize, //Con id for invented symbol
}

fn cmp_clause(a: &Clause, b: &Clause, heap: &impl Heap) -> Ordering {
    match a.len().cmp(&b.len()) {
        ordering => ordering,
        Ordering::Equal => {
            let len = a.len();
            for i in 1..len {
                let (_, arr1) = heap[a[i]];
                let (_, arr2) = heap[b[i]];
                match arr1.cmp(&arr2) {
                    Ordering::Equal => continue,
                    ordering => return ordering,
                }
            }
            Ordering::Equal
        }
    }
}

impl PredDef {
    pub fn new(heap: &mut impl Heap, mut clauses: Vec<Clause>) -> Self {
        // Order Clauses by literal count
        clauses.sort_by(|a, b| cmp_clause(a, b, heap));
        // Order Clauses by literal count, break ties with 1st body arity

        Self { clauses }
    }

    pub fn make_const(&mut self, heap: &mut impl Heap, next_id: usize) {
        // Extract var pred
        let (Ref, var_pred) = heap[self.clauses[0][0] + 1] else {
            panic!()
        };
        // coin new const
        let pred_symbol = SymbolDB::set_const(format!("pred_{next_id}"));
        let pred_addr = heap.heap_push((Con, pred_symbol));
        // Update Clauses with new symbol
        for clause in &self.clauses {
            for literal in clause.iter() {
                let mut walk = TermWalk::new(*literal);
                while let Some((addr, cell)) = walk.next_cell_with_addr(heap) {
                    if cell == (Ref, var_pred) {
                        heap[addr] = (Con, pred_symbol)
                    }
                }
            }
        }
    }

    pub fn new_const(heap: &mut impl Heap, mut clauses: Vec<Clause>, next_id: usize) -> Self {
        // Extract var pred
        let (Ref, var_pred) = heap[clauses[0][0] + 1] else {
            panic!()
        };
        // coin new const
        let pred_symbol = SymbolDB::set_const(format!("pred_{next_id}"));
        let pred_addr = heap.heap_push((Con, pred_symbol));

        // Update Clauses with new symbol
        // Assumes ownership of clause literals
        for clause in &clauses {
            for literal in clause.iter() {
                let mut walk = TermWalk::new(*literal);
                while let Some((addr, cell)) = walk.next_cell_with_addr(heap) {
                    if cell == (Ref, var_pred) {
                        heap[addr] = (Con, pred_symbol)
                    }
                }
            }
        }

        //Order Clauses by literal count
        // TODO move this out of new, assume pred defs come ordered
        clauses.sort_by(|a, b| a.len().cmp(&b.len()));

        Self {
            clauses,
            // symbol: pred_symbol,
        }
    }

    /// Attempt to unify variable with constant predicate defintion
    pub fn unify(&self, var_pred_def: &Vec<Clause>, heap: &impl Heap) -> bool {
        if self.clauses.len() != var_pred_def.len() {
            return false;
        }

        // Order

        true
    }
}

#[cfg(test)]
mod tests {
    use smallvec::SmallVec;

    use crate::{
        heap::{
            Cell, Heap, QueryHeap, SymbolDB,
            Tag::*,
            VarBind::{self, *},
            VarReg,
        },
        parser::{_build_clause, execute_tree, tokenise, TokenStream},
        program::{clause::Clause, hypothesis::Hypothesis, predicate_table::PredicateTable},
        resolution::{build, Substitution},
    };

    fn get_const_ids<const N: usize>(symbols: [&'static str; N]) -> [usize; N] {
        let mut res = [0; N];

        for i in 0..N {
            res[i] = SymbolDB::set_const(symbols[i])
        }

        res
    }

    fn push_literal(heap: &mut QueryHeap, sub_terms: &[Cell]) -> usize {
        let addr = heap.heap_push((Comp, sub_terms.len()));
        heap.cells.extend_from_slice(&sub_terms);
        addr
    }

    fn instantiate_meta_rule(
        heap: &mut QueryHeap,
        meta: &Clause,
        bindings: &[(usize, VarBind)],
    ) -> Clause {
        let mut subs = Substitution::new(15);
        for (arg_id, binding) in bindings {
            subs.set_arg(*arg_id, *binding);
        }

        let new_clause_literals: Vec<usize> = meta
            .iter()
            .map(|literal| build(heap, &mut subs, Some(meta.meta_vars), *literal))
            .collect();

        Clause::new(new_clause_literals, None, meta.max_arg_id)
    }

    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    fn one_clause_pred() {
        // Create meta rules
        let mut prog_heap: Vec<Cell> = vec![];
        let meta1 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X,Y),{P,Q}");
        let meta2 = _build_clause(&mut prog_heap, "P(X,Y):-Q(X),R(Y),{P,Q,R}");

        //Build hypotheses
        let mut heap = QueryHeap::new(&[], None);
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
        let [p, q, r] = [p, q, r].map(|con_id| heap.heap_push((Con, con_id)));

        let mut h1 = Hypothesis::new();
        heap.var_regs.push(VarReg::UNBOUND);
        h1.push_clause(
            instantiate_meta_rule(&mut heap, &meta1, &[(2, Addr(p)), (3, Var(0))]),
            SmallVec::new(),
        );
        h1.push_clause(
            instantiate_meta_rule(
                &mut heap,
                &meta2,
                &[(2, Var(0)), (3, Addr(q)), (4, Addr(r))],
            ),
            SmallVec::new(),
        );

        let mut h2 = Hypothesis::new();
        heap.var_regs.push(VarReg::UNBOUND);
        h2.push_clause(
            instantiate_meta_rule(&mut heap, &meta1, &[(2, Addr(p)), (3, Var(1))]),
            SmallVec::new(),
        );
        h2.push_clause(
            instantiate_meta_rule(
                &mut heap,
                &meta2,
                &[(2, Var(1)), (3, Addr(q)), (4, Addr(r))],
            ),
            SmallVec::new(),
        );
    }

    // #[test]
    // /// Hypothesis 1
    // ///     p(X,Y):- Var_0(X,Y).
    // ///     Var_0(X,Y):- q(X), r(Y).
    // /// Hypothesis 2
    // ///     p(X,Y):- Var_1(X,Y).
    // ///     Var_1(X,Y):- q(X), r(Y).
    // fn one_clause_pred_2() {
    //     let [p, q, r] = get_const_ids(["p", "q", "r"]);
    //     let mut heap = QueryHeap::new(&[], None);
    //     let literals = [
    //         &[(Con, p), (Arg, 0), (Arg, 1)][..],
    //         &[(Ref, 0), (Arg, 0), (Arg, 1)][..],
    //     ];
    //     let clause1 = build_clause(&mut heap, &literals, 1);
    //     let literals = [
    //         &[(Ref, 1), (Arg, 0), (Arg, 1)][..],
    //         &[(Con, q), (Arg, 0)][..],
    //         &[(Con, q), (Arg, 1)][..],
    //     ];
    //     let clause2 = build_clause(&mut heap, &literals, 1);
    // }
}
