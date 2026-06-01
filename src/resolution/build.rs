//! Term building: construct new heap terms from clause templates and substitutions.

use crate::{
    heap::heap::{Cell, Heap, Tag},
    program::clause::BitFlag64,
    resolution::unification::Substitution,
};

/*  If a ref if bound to some complex term which contains args we want
   to rebuild this term in the query space replacing args with refs or arg reg values
*/
pub fn re_build_bound_arg_terms(heap: &mut impl Heap, substitution: &mut Substitution) {
    for i in 0..substitution.len() {
        if let (_, bound_addr, true) = substitution[i] {
            if heap.contains_args(bound_addr) {
                //Build term if contains args
                //Update bound_addr to newly built term
                let new_bound_addr = build(heap, substitution, None, bound_addr);
                substitution[i].1 = new_bound_addr;
            }
        }
    }
}

/*  Build a new term from previous term and substitution.
    Assume that src_addr does not point to bound ref.   ``

*/
pub fn build(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    match heap[heap.deref_addr(src_addr)] {
        (tag @ (Tag::Con | Tag::Flt | Tag::Int | Tag::Stri | Tag::ELis | Tag::Ref| Tag::AVar), value) => {
            heap.heap_push((tag, value))
        }
        (Tag::Arg, _arg_id) => build_arg(heap, substitution, meta_vars, src_addr),
        (Tag::Comp | Tag::Tup | Tag::Set, _) => build_str(heap, substitution, meta_vars, src_addr),
        (Tag::Lis, ptr) => {
            let new_ptr = build_list(heap, substitution, meta_vars, ptr);
            heap.heap_push((Tag::Lis, new_ptr))
        }
        cell => unimplemented!("build: unhandled cell type {cell:?}"),
    }
}

fn build_arg(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    let arg_id = heap[src_addr].1;
    match meta_vars {
        Some(bit_flags) if !bit_flags.get(arg_id) => heap.heap_push(heap[src_addr]),
        _ => match substitution.get_arg(arg_id) {
            Some(bound_addr) => heap.set_ref(Some(bound_addr)),
            None => {
                let ref_addr = heap.set_ref(None);
                substitution.set_arg(arg_id, ref_addr);
                ref_addr
            }
        },
    }
}

fn build_str(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    let (tag, length) = heap[src_addr];
    let mut complex_terms: Vec<Option<Cell>> = Vec::with_capacity(length);
    for i in 1..length + 1 {
        complex_terms.push(build_complex_term(
            heap,
            substitution,
            meta_vars,
            src_addr + i,
        ));
    }
    let addr = heap.heap_push((tag, length));
    let mut i = 1;
    for complex_term in complex_terms {
        match complex_term {
            Some(cell) => heap.heap_push(cell),
            None => build(heap, substitution, meta_vars, src_addr + i),
        };
        i += 1;
    }

    addr
}

fn build_list(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> usize {
    let head = build_complex_term(heap, substitution, meta_vars, src_addr);
    let tail = build_complex_term(heap, substitution, meta_vars, src_addr + 1);
    let ptr = match head {
        Some(cell) => heap.heap_push(cell),
        None => build(heap, substitution, meta_vars, src_addr),
    };
    match tail {
        Some(cell) => heap.heap_push(cell),
        None => build(heap, substitution, meta_vars, src_addr + 1),
    };
    ptr
}

fn build_complex_term(
    heap: &mut impl Heap,
    substitution: &mut Substitution,
    meta_vars: Option<BitFlag64>,
    src_addr: usize,
) -> Option<Cell> {
    match heap[heap.deref_addr(src_addr)] {
        (Tag::Comp | Tag::Tup | Tag::Set, _) => {
            // Dereference first: `src_addr` may be a bound `Ref` pointing to the
            // structure. Passing the raw address would make `build_str` read the
            // `Ref` cell and misinterpret its pointer value as the arity.
            Some((Tag::Str, build_str(heap, substitution, meta_vars, heap.deref_addr(src_addr))))
        }
        (Tag::Str, ptr) => Some((Tag::Str, build_str(heap, substitution, meta_vars, ptr))),
        (Tag::Lis, ptr) => Some((Tag::Lis, build_list(heap, substitution, meta_vars, ptr))),
        (Tag::Arg, id) => match meta_vars {
            Some(bitflags) if !bitflags.get(id) => None,
            _ => match substitution.get_arg(id) {
                Some(addr) => build_complex_term(heap, substitution, meta_vars, addr),
                None => None,
            },
        },
        (Tag::Ref, ref_addr) if ref_addr == src_addr => {
            if let Some(bound_addr) = substitution.bound(ref_addr) {
                build_complex_term(heap, substitution, meta_vars, bound_addr)
            } else {
                None
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        heap::{
            heap::{Heap, Tag},
            symbol_db::SymbolDB,
        },
        program::clause::BitFlag64,
        resolution::{
            build::{build, re_build_bound_arg_terms},
            unification::{unify, Substitution},
        },
    };

    #[test]
    fn args() {
        let p = SymbolDB::set_const("p");
        let f = SymbolDB::set_const("f");

        let mut heap = vec![
            (Tag::Comp, 4),
            (Tag::Con, p),
            (Tag::Arg, 0),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
        ];
        let mut substitution = Substitution::default();
        let addr = build(&mut heap, &mut substitution, None, 0);
        assert_eq!(
            heap[addr..(addr + 4)],
            [
                (Tag::Comp, 4),
                (Tag::Con, p),
                (Tag::Ref, addr + 2),
                (Tag::Ref, addr + 2),
            ]
        );

        let mut substitution = Substitution::default();
        let mut meta_vars = BitFlag64::default();
        meta_vars.set(0);
        let addr = build(&mut heap, &mut substitution, Some(meta_vars), 0);
        heap._print_heap();
        assert_eq!(
            heap[addr..(addr + 5)],
            [
                (Tag::Comp, 4),
                (Tag::Con, p),
                (Tag::Ref, addr + 2),
                (Tag::Ref, addr + 2),
                (Tag::Arg, 1)
            ]
        );

        heap = vec![
            (Tag::Comp, 2),
            (Tag::Con, f),
            (Tag::Ref, 2),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Arg, 0),
        ];
        substitution = Substitution::default();
        substitution.set_arg(0, 0);
        let addr = build(&mut heap, &mut substitution, None, 3);
        assert_eq!(
            heap[addr - 3..(addr + 3)],
            [
                (Tag::Comp, 2),
                (Tag::Con, f),
                (Tag::Ref, 2),
                (Tag::Comp, 2),
                (Tag::Con, p),
                (Tag::Str, addr - 3),
            ]
        );
    }

    #[test]
    fn lists() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");

        let mut heap = vec![
            (Tag::Con, a), //0
            (Tag::Lis, 2), //1
            (Tag::Con, b), //2
            (Tag::Arg, 0), //3
            (Tag::Comp, 2), //4
            (Tag::Con, p), //5
            (Tag::Lis, 0), //6
            (Tag::Con, a), //7
            (Tag::Lis, 9), //8
            (Tag::Con, b), //9
            (Tag::Lis, 11), //10
            (Tag::Con, c), //11
            (Tag::ELis, 0), //12
            (Tag::Comp, 2), //13
            (Tag::Con, p), //14
            (Tag::Lis, 7), //15
        ];
        let mut substitution = Substitution::default();
        substitution.set_arg(0, 10);
        let addr = build(&mut heap, &mut substitution, None, 4);
        assert_eq!(heap.term_string(addr), "p([a,b,c])");

        let mut heap = vec![
            (Tag::Con, a), //0
            (Tag::Lis, 2), //1
            (Tag::Con, b), //2
            (Tag::Ref, 3), //3
            (Tag::Comp, 2), //4
            (Tag::Con, p), //5
            (Tag::Lis, 0), //6
            (Tag::Con, a), //7
            (Tag::Lis, 9), //8
            (Tag::Con, b), //9
            (Tag::Lis, 11), //10
            (Tag::Arg, 0), //11
            (Tag::ELis, 0), //12
            (Tag::Comp, 2), //13
            (Tag::Con, p), //14
            (Tag::Lis, 7), //15
        ];
        let mut substitution = Substitution::default();
        substitution = substitution.push((3, 10, true));
        re_build_bound_arg_terms(&mut heap, &mut substitution);
        let new_term = build(&mut heap, &mut substitution, None, 13);
        println!("{}", heap.term_string(new_term));
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

        let mut heap = vec![
            (Tag::Comp, 2), // 0: q/1 (functor + 1 arg)
            (Tag::Con, q),  // 1: functor
            (Tag::Ref, 4),  // 2: arg X -> ref that derefs to the tuple at 4
            (Tag::Con, a),  // 3: padding (in misread window)
            (Tag::Tup, 2),  // 4: tuple (a,b) — the deref target of the ref at 2
            (Tag::Con, a),  // 5
            (Tag::Con, b),  // 6
        ];

        let mut sub = Substitution::default();
        let result = build(&mut heap, &mut sub, None, 0);

        // Built term should be q((a,b)).
        assert_eq!(heap.term_string(result), "q((a,b))");

        // Structurally: result is a Comp whose argument is a Str indirection to
        // a real Tup cell — NOT to a misread Ref cell.
        assert_eq!(heap[result], (Tag::Comp, 2));
        assert_eq!(heap[result + 1], (Tag::Con, q));
        let (arg_tag, arg_ptr) = heap[result + 2];
        assert_eq!(arg_tag, Tag::Str, "argument should be a Str indirection");
        assert_eq!(
            heap[arg_ptr].0,
            Tag::Tup,
            "built subterm header should be a Tup, not a misread Ref cell (got {:?})",
            heap[arg_ptr]
        );
    }

    #[test]
    fn test1() {
        let p = SymbolDB::set_const("p");
        let mut heap = vec![
            (Tag::Ref, 0),  //0
            (Tag::Lis, 2),  //1
            (Tag::Ref, 2),  //2
            (Tag::ELis, 0), //3
            (Tag::Comp, 3), //4
            (Tag::Con, p),  //5
            (Tag::Ref, 6),  //6
            (Tag::Lis, 0),  //7
            (Tag::Comp, 3), //8
            (Tag::Con, p),  //9
            (Tag::Arg, 0),  //10
            (Tag::Arg, 0),  //11
        ];

        let mut sub = unify(&heap, 8, 4).unwrap();
        re_build_bound_arg_terms(&mut heap, &mut sub);

        heap._print_heap();
        println!("{:?}", sub.bound(6))
    }

    #[test]
    fn test2() {
        let p = SymbolDB::set_const("p");
        let mut heap = vec![
            (Tag::Ref, 0),  //0
            (Tag::Lis, 2),  //1
            (Tag::Ref, 2),  //2
            (Tag::ELis, 0), //3
            (Tag::Comp, 3), //4
            (Tag::Con, p),  //5
            (Tag::Ref, 6),  //6
            (Tag::Lis, 0),  //7
            (Tag::Comp, 3), //8
            (Tag::Con, p),  //9
            (Tag::Arg, 0),  //10
            (Tag::Arg, 0),  //11
        ];

        let mut sub = unify(&heap, 8, 4).unwrap();
        re_build_bound_arg_terms(&mut heap, &mut sub);

        heap._print_heap();
        println!("{:?}", sub.bound(6))
    }
}
