//! Term building: construct new heap terms from clause templates and substitutions.

use crate::{
    heap::{Heap, QueryHeap, Tag::*, TermWalk, VarBind::*, Walk},
    program::clause::BitFlag64,
    resolution::Substitution,
};

/// If a ref if bound to some complex term which contains args we want
/// to rebuild this term in the query space replacing args with refs or arg reg values
pub fn re_build_bound_arg_terms(heap: &mut QueryHeap, substitution: &mut Substitution) {
    for i in 0..substitution.len() {
        if substitution.needs_rebuild[i] {
            // Assume if needs rebuild is true variable register is an addr
            let mut bound_addr = heap.var_regs[substitution[i]].value();
            //Update bound_addr to newly built term
            bound_addr = build(heap, substitution, None, bound_addr);
            // don't use heap.bind() to avoid overwrite guards
            heap.var_regs[substitution[i]] = Addr(bound_addr).into();
        }
    }
}

/// Build a new term from previous term and substitution.
/// Assume that src_addr does not point to bound ref.
pub fn build(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    let new_addr = heap.heap_len();
    let mut walk = TermWalk::new(src_addr);

    while let Some(cell) = walk.next_cell(heap) {
        if cell.0 == Arg {
            build_arg(heap, substitution, meta_vars, src_addr);
        } else {
            heap.heap_push(cell);
        }
    }
    new_addr
}

fn build_arg(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) {
    let arg_id = heap[src_addr].1;
    match meta_vars {
        Some(bit_flags) if !bit_flags.get(arg_id) => _ = heap.heap_push(heap[src_addr]),
        _ => match substitution.get_arg(arg_id) {
            Some(Addr(bound_addr)) => _ = build(heap, substitution, meta_vars, bound_addr),
            Some(Var(var_id)) => _ = heap.heap_push((Ref, var_id)),
            None => {
                let var_id = heap.set_var(None);
                substitution.set_arg(arg_id, Var(var_id));
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use std::{assert_eq, vec};

    use crate::{
        heap::{Heap, QueryHeap, SymbolDB, Tag::*, VarBind::*, VarReg, EMPTY_LIS, LIS},
        program::clause::BitFlag64,
        resolution::{build, re_build_bound_arg_terms, unify, Substitution},
    };

    #[test]
    fn args() {
        let p = SymbolDB::set_const("p");
        let f = SymbolDB::set_const("f");
        let prog_heap = vec![];

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Comp, 4), (Con, p), (Arg, 0), (Arg, 0), (Arg, 1)]);
        let mut substitution = Substitution::default();
        let addr = build(&mut heap, &mut substitution, None, 0);
        assert_eq!(
            heap.cells[addr..],
            [(Comp, 4), (Con, p), (Ref, 0), (Ref, 0), (Ref, 1),]
        );
        assert_eq!(heap.var_regs[0], VarReg::UNBOUND);
        assert_eq!(heap.var_regs[1], VarReg::UNBOUND);

        let mut substitution = Substitution::default();
        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let addr = build(&mut heap, &mut substitution, Some(meta_vars), 0);
        heap._print_heap();
        assert_eq!(
            heap.cells[addr..],
            [(Comp, 4), (Con, p), (Ref, 2), (Ref, 2), (Arg, 1)]
        );
        assert_eq!(heap.var_regs[2], VarReg::UNBOUND);

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Comp, 2), (Con, f), (Ref, 0), (Comp, 2), (Con, p), (Arg, 0)]);
        heap.var_regs.push(VarReg::UNBOUND);
        substitution = Substitution::default();
        substitution.set_arg(0, Addr(0));
        let addr = build(&mut heap, &mut substitution, None, 3);
        assert_eq!(
            heap.cells[addr..],
            [(Comp, 2), (Con, p), (Comp, 2), (Con, f), (Ref, 0),]
        );
    }

    #[test]
    fn lists() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let prog_heap = vec![];

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // p([a,b|Arg0])
            (Comp, 2),
            (Con, p),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // p([a,b,c])
            (Comp, 2),
            (Con, p),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ]);
        let mut substitution = Substitution::default();
        substitution.set_arg(0, Var(13));
        let addr = build(&mut heap, &mut substitution, None, 4);
        assert_eq!(heap.term_string(addr), "p([a,b,c])");

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // p([a,b|Ref3])
            (Comp, 2),
            (Con, p),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // p([a,b,Arg0])
            (Comp, 2),
            (Con, p),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Arg, 0),
            EMPTY_LIS,
        ]);
        heap.var_regs.push(Addr(13).into());
        let mut substitution = Substitution::default();
        substitution.push_bound_var(0, true,Addr(13).into());
        let idx = heap.heap_len();
        re_build_bound_arg_terms(&mut heap, &mut substitution);
        assert_eq!(heap.cells[idx..], [LIS, (Ref, 1), EMPTY_LIS,]);
        assert_eq!(heap.var_regs[1], VarReg::UNBOUND);

        let new_term = build(&mut heap, &mut substitution, None, 7);
        assert_eq!(
            heap.cells[new_term..],
            [
                (Comp, 2),
                (Con, p),
                LIS,
                (Con, a),
                LIS,
                (Con, b),
                LIS,
                (Ref, 1),
                EMPTY_LIS,
            ]
        );
    }

    #[test]
    fn meta_vars() {}

    /// Regression test for the molecules stack overflow.
    ///
    /// When a structural subterm is a bound `Ref` that dereferences to a
    /// structure (e.g. a query variable bound to a tuple), `build_complex_term`
    /// must dereference the address before handing it to `build_str`. The
    /// original code passed the raw `src_addr`, so `build_str` read the
    /// `(Ref, ptr)` cell and treated `ptr` as the structure arity — reading far
    /// past the real term and, on the molecules example, recursing until the
    /// stack overflowed.
    ///
    /// Heap below encodes the compound `q(X)` where the single argument `X`
    /// is a `Ref` (addr 2) that derefs to the tuple `(a,b)` at addr 4. Building
    /// it must yield `q((a,b))`, with the built argument being a proper `Tup`
    /// cell rather than the misread `Ref` cell.
    #[test]
    fn build_ref_to_structure_subterm() {
        let q = SymbolDB::set_const("q");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let prog_heap = vec![];

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Comp, 2), // 0: q/1 (functor + 1 arg)
            (Con, q),  // 1: functor
            (Ref, 0),  // 2: arg X -> ref that derefs to the tuple at 4
            (Con, a),  // 3: padding (in misread window)
            (Tup, 2),  // 4: tuple (a,b) — the deref target of the ref at 2
            (Con, a),  // 5
            (Con, b),  // 6
        ]);
        heap.var_regs.push(Addr(4).into());

        let mut sub = Substitution::default();
        let result = build(&mut heap, &mut sub, None, 0);

        // Built term should be q((a,b)).
        assert_eq!(heap.term_string(result), "q((a,b))");

        assert_eq!(
            heap.cells[result..],
            [(Comp, 2), (Con, q), (Tup, 2), (Con, a), (Con, b),]
        );
    }

    #[test]
    fn test1() {
        let p = SymbolDB::set_const("p");
        let prog_heap = vec![];

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Ref, 0),  //0
            (Lis, 2),  //1
            (Ref, 2),  //2
            (ELis, 0), //3
            (Comp, 3), //4
            (Con, p),  //5
            (Ref, 6),  //6
            (Lis, 0),  //7
            (Comp, 3), //8
            (Con, p),  //9
            (Arg, 0),  //10
            (Arg, 0),  //11
        ]);

        let mut sub = unify(&mut heap, 8, 4).unwrap();
        re_build_bound_arg_terms(&mut heap, &mut sub);

        heap._print_heap();
        println!("{:?}", sub.bound(6))
    }

    #[test]
    fn test2() {
        let p = SymbolDB::set_const("p");
        let prog_heap = vec![];

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Ref, 0),  //0
            (Lis, 2),  //1
            (Ref, 2),  //2
            (ELis, 0), //3
            (Comp, 3), //4
            (Con, p),  //5
            (Ref, 6),  //6
            (Lis, 0),  //7
            (Comp, 3), //8
            (Con, p),  //9
            (Arg, 0),  //10
            (Arg, 0),  //11
        ]);

        let mut sub = unify(&mut heap, 8, 4).unwrap();
        re_build_bound_arg_terms(&mut heap, &mut sub);

        heap._print_heap();
        println!("{:?}", sub.bound(6))
    }
}
