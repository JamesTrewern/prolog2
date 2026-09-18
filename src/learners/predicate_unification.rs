#[cfg(test)]
mod tests {
    use crate::{
        heap::{Cell, Heap, QueryHeap, SymbolDB, Tag::*},
        program::clause::Clause,
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

    fn build_clause(heap: &mut QueryHeap, literals: &[&[Cell]], max_arg_id: usize) -> Clause {
        let literals: Vec<usize> = literals
            .into_iter()
            .map(|sub_terms| push_literal(heap, sub_terms))
            .collect();

        Clause::new(literals, None, max_arg_id)
    }

    #[test]
    /// Hypothesis 1
    ///     p(X,Y):- Var_0(X,Y).
    ///     Var_0(X,Y):- q(X), r(Y).
    /// Hypothesis 2
    ///     p(X,Y):- Var_1(X,Y).
    ///     Var_1(X,Y):- q(X), r(Y).
    fn one_clause_pred() {
        let [p, q, r] = get_const_ids(["p", "q", "r"]);
        let mut heap = QueryHeap::new(&[], None);
        let literals = [
            &[(Con, p), (Arg, 0), (Arg, 1)][..],
            &[(Ref, 0), (Arg, 0), (Arg, 1)][..],
        ];
        let clause1 = build_clause(&mut heap, &literals, 1);
        let literals = [
            &[(Ref, 1), (Arg, 0), (Arg, 1)][..],
            &[(Con, q), (Arg, 0)][..],
            &[(Con, q), (Arg, 1)][..],
        ];
        let clause2 = build_clause(&mut heap, &literals, 1);
    }
}
