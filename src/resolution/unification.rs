//! Unification algorithm and substitution management.
use super::Substitution;
use crate::heap::{Cell, DualWalk, Heap, QueryHeap, SubWalk, Tag::*, TermWalk, VarBind::*, Walk};
use smallvec::SmallVec;

pub fn unify(
    heap: &mut QueryHeap,
    addr1: usize,
    addr2: usize,
    max_arg: usize,
) -> Option<Substitution> {
    let mut substitution = Substitution::new(max_arg);
    let mut walk = DualWalk::new(addr1, addr2);
    while let Some((res1, res2)) = walk.next_cells_with_addrs_arg_deref(heap, &substitution) {
        let (addr1, (tag1, value1)) = res1;
        let (addr2, (tag2, value2)) = res2;
        match (tag1, tag2) {
            (Arg, Arg) => {
                if value1 != value2 {
                    todo!("How to handle two args unifiying")
                }
            }
            (Arg, _) => {
                if !bind_arg(heap, &mut substitution, value1, res2, &mut walk.walk2) {
                    return undo_substitution(heap, substitution);
                }
            }
            (_, Arg) => {
                if !bind_arg(heap, &mut substitution, value2, res1, &mut walk.walk1) {
                    return undo_substitution(heap, substitution);
                }
            }
            (Ref, Ref) => {
                if value1 != value2 {
                    // If var_id for lhs constrained reverse standard lhs -> rhs binding
                    let (from, to) = if heap.constrained(value1) {
                        (value2, value1)
                    } else {
                        (value1, value2)
                    };
                    heap.bind(from, Var(to));
                    substitution.push_bound_var(from, false, Var(to));
                }
            }
            (Ref, Lis | Comp | Set | Tup) => {
                if !bind_ref_to_complex(heap, &mut substitution, value1, addr2, &mut walk.walk2) {
                    return undo_substitution(heap, substitution);
                }
            }
            (Lis | Comp | Set | Tup, Ref) => {
                if !bind_ref_to_complex(heap, &mut substitution, value2, addr1, &mut walk.walk1) {
                    return undo_substitution(heap, substitution);
                }
            }
            (Ref, _) => {
                heap.bind(value1, Addr(addr2));
                substitution.push_bound_var(value1, false, Addr(addr2));
            }
            (_, Ref) => {
                heap.bind(value2, Addr(addr1));
                substitution.push_bound_var(value2, false, Addr(addr1));
            }
            (Set, Set) => {
                if !set_equal(heap, addr1, addr2, &mut walk) {
                    return undo_substitution(heap, substitution);
                }
            }
            (Comp | Tup, Comp | Tup) if heap[addr1] == heap[addr2] => continue,
            (Lis, Lis) => continue,
            (AVar, _) | (_, AVar) => continue,
            _ if (tag1, value1) == (tag2, value2) => continue,
            _ => return undo_substitution(heap, substitution),
        }
    }
    Some(substitution)
}

fn undo_substitution(heap: &mut QueryHeap, substitution: Substitution) -> Option<Substitution> {
    heap.unbind(&substitution.get_bound_vars());
    None
}

/// Set unification: equality check only.
///
/// Two sets unify iff they have the same length and every element in one has a
/// structurally equal counterpart in the other. No variable bindings are
/// created — this is a deliberate design choice because with two or more
/// unbound variables the lack of element ordering makes correct binding
/// impossible.
fn set_equal(heap: &mut QueryHeap, addr1: usize, addr2: usize, walk: &mut DualWalk) -> bool {
    //TODO this does not handle complex terms

    let len_1 = heap[addr1].1;
    let len_2 = heap[addr2].1;
    if len_1 != len_2 {
        return false;
    }
    walk.walk1.skip_addrs(len_1);
    walk.walk2.skip_addrs(len_1);

    let mut r1 = addr1 + 1..=addr1 + len_1;
    let r2 = addr2 + 1..=addr2 + len_2;

    // Every element in set1 must match some element in set2.
    r1.all(|a| r2.clone().any(|b| heap.term_equal(a, b)))
}

fn bind_ref_to_complex(
    heap: &mut QueryHeap,
    substitution: &mut Substitution,
    var_id: usize,
    complex_addr: usize,
    walk: &mut TermWalk,
) -> bool {
    let Some(needs_rebuild) = occurs(heap, &substitution, var_id, walk.sub_walk(heap)) else {
        return false;
    };
    heap.bind(var_id, Addr(complex_addr));
    substitution.push_bound_var(var_id, needs_rebuild, Addr(complex_addr));
    true
}

fn occurs(
    heap: &mut QueryHeap,
    binding: &Substitution,
    var_id: usize,
    mut walk: SubWalk,
) -> Option<bool> {
    let mut bound_args = SmallVec::<[usize; 2]>::new();
    //TODO make this quicker perhaps SIMD?
    for (arg_id, arg_reg) in binding.arg_regs.iter().enumerate() {
        if let Some(Var(var_id_2)) = arg_reg.get_bind() {
            if var_id == var_id_2 {
                bound_args.push(arg_id);
            }
        }
    }
    let mut contains_args = false;

    while let Some((tag, value)) = walk.next_cell(heap) {
        match tag {
            Ref if value == var_id => return None,
            Arg if bound_args.contains(&value) => return None,
            Arg => contains_args = true,
            _ => (),
        }
    }

    Some(contains_args)
}

fn bind_arg(
    heap: &mut QueryHeap,
    substitution: &mut Substitution,
    arg_id: usize,
    (addr, (tag, value)): (usize, Cell),
    walk: &mut TermWalk,
) -> bool {
    match tag {
        Comp | Tup | Lis => {
            if arg_occurs(heap, arg_id, walk.sub_walk(heap)) {
                return false;
            } else {
                substitution.set_arg(arg_id, Addr(addr));
            }
        }
        Ref => substitution.set_arg(arg_id, Var(value)),
        _ => substitution.set_arg(arg_id, Addr(addr)),
    }
    true
}

fn arg_occurs(heap: &mut QueryHeap, arg_id: usize, mut walk: SubWalk) -> bool {
    while let Some((tag, value)) = walk.next_cell(heap) {
        if tag == Arg && value == arg_id {
            return true;
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::Substitution;
    use crate::{
        heap::{Heap, QueryHeap, SymbolDB, Tag::*, VarBind::*, VarReg, EMPTY_LIS, LIS},
        resolution::unification::unify,
    };

    //-----------------------------------------------------------
    //-------- Comp/Tup Unification ----------------------------
    //-----------------------------------------------------------

    #[test]
    fn equal_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Constant Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Ref Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Ref, 0), (Comp, 2), (Con, p), (Ref, 0)];
        heap.var_regs.push(VarReg::UNBOUND);
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Arg Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0), (Comp, 2), (Con, p), (Arg, 0)];
        heap.var_regs.clear();
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_tup() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Constant Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Con, a), (Tup, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Ref Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Ref, 0), (Tup, 2), (Con, p), (Ref, 0)];
        heap.var_regs.push(VarReg::UNBOUND);
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Arg Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Arg, 0), (Tup, 2), (Con, p), (Arg, 0)];
        heap.var_regs.clear();
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_comp_ref_jump() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Simple ref jump
        heap.cells = vec![
            (Comp, 2),
            (Con, p),
            (Con, a),
            (Comp, 2),
            (Con, p),
            (Ref, 0),
            (Con, a),
        ];
        heap.var_regs = vec![Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Ref chain jump
        heap.var_regs = vec![Var(1).into(), Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_comp_arg_jump() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Simple arg jump

        //Arg to ref jump

        //Arg to ref chain jump
    }

    #[test]
    fn equal_nested_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Basic
        heap.cells = vec![
            // 0: p(q(a))
            (Comp, 2),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Con, a),
            // 5: p(q(a))
            (Comp, 2),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Con, a),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Nested Ref jump
        heap.cells = vec![
            // 0: p(q(a))
            (Comp, 2),
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Con, a),
            // 5: p(X)
            (Comp, 2),
            (Con, p),
            (Ref, 0), // X -> q(a)
            // 8: q(a)
            (Comp, 2),
            (Con, q),
            (Con, a),
        ];
        heap.var_regs = vec![Addr(8).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Nested Arg jump
        heap.cells = vec![
            // 0: (A,p(A))
            (Tup, 2),
            (Arg, 0),
            (Comp, 2), // 2: p(A)
            (Con, p),
            (Arg, 0),
            // 5: (q(a),p(q(a)))
            (Tup, 2),
            (Comp, 2), // 6: q(a)
            (Con, q),
            (Con, a),
            (Comp, 2), // 9: p(q(a))
            (Con, p),
            (Comp, 2),
            (Con, q),
            (Con, a),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));

        //Nested both Ref Jump
        //Nested Ref jump
        heap.cells = vec![
            // 0: p(X)
            (Comp, 2),
            (Con, p),
            (Ref, 0), // X -> q(a)
            // 3: q(a)
            (Comp, 2),
            (Con, q),
            (Con, a),
            // 6: p(Y)
            (Comp, 2),
            (Con, p),
            (Ref, 1), // X -> q(a)
            // 9: q(a)
            (Comp, 2),
            (Con, q),
            (Con, a),
        ];
        heap.var_regs = vec![Addr(3).into(), Addr(9).into()];
        let sub = unify(&mut heap, 0, 6, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    //-----------------------------------------------------------
    //-------- Set unification ----------------------------------
    //-----------------------------------------------------------

    #[test]
    fn equal_set() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Same order
        heap.cells = vec![
            (Set, 3),
            (Con, a),
            (Con, b),
            (Con, c),
            (Set, 3),
            (Con, a),
            (Con, b),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub, Substitution::default());
        heap.cells = vec![
            (Set, 3),
            (Con, a),
            (Con, b),
            (Con, c),
            (Set, 3),
            (Con, c),
            (Con, a),
            (Con, b),
        ];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    //-----------------------------------------------------------
    //-------- List unification ---------------------------------
    //-----------------------------------------------------------

    #[test]
    fn equal_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Proper List
        heap.cells = vec![
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Const tail
        heap.cells = vec![
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Nested List
        //[[a,b],c]
        heap.cells = vec![
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Nested List const tail
        //[[a,b],c]
        heap.cells = vec![
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    /// `[a,b,c]` vs `[a,b,c]` where the rhs reaches parts of the list through
    /// bound `Ref` cells. Every case is structurally equal, so unification must
    /// succeed without creating any new bindings.
    #[test]
    fn equal_proper_list_with_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Jump at a head position: [a,b,c] vs [X,b,c] where X -> a
        heap.cells = vec![
            // 0: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: [X,b,c]
            LIS,
            (Ref, 0),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 14: X -> a
            (Con, a),
        ];
        heap.var_regs = vec![Addr(14).into()];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump at a tail position: [a,b,c] vs [a,b|X] where X -> [c]
        heap.cells = vec![
            // 0: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 12: X -> [c]
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(12).into()];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same tail jump, but reached through a ref chain X -> Y -> [c]
        heap.var_regs = vec![Var(1).into(), Addr(12).into()];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump at the root: [a,b,c] vs X where X -> [a,b,c]
        heap.cells = vec![
            // 0: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: X
            (Ref, 0),
            // 8: X -> [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(8).into()];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //A jump landing on the wrong constant must fail: [a,b,c] vs [X,b,c], X -> c
        heap.cells = vec![
            // 0: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: [X,b,c]
            LIS,
            (Ref, 0),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 14: X -> c
            (Con, c),
        ];
        heap.var_regs = vec![Addr(14).into()];
        assert!(unify(&mut heap, 0, 7, 31).is_none());
    }

    /// Improper list `[a,b|c]` vs itself, with the rhs reaching the head, the
    /// partial tail and the constant tail through bound `Ref` cells.
    #[test]
    fn equal_con_tail_list_with_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Jump at a head position: [a,b|c] vs [X,b|c] where X -> a
        heap.cells = vec![
            // 0: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 5: [X,b|c]
            LIS,
            (Ref, 0),
            LIS,
            (Con, b),
            (Con, c),
            // 10: X -> a
            (Con, a),
        ];
        heap.var_regs = vec![Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump at the constant tail: [a,b|c] vs [a,b|X] where X -> c
        heap.cells = vec![
            // 0: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 10: X -> c
            (Con, c),
        ];
        heap.var_regs = vec![Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same, through a ref chain X -> Y -> c
        heap.var_regs = vec![Var(1).into(), Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump at a partial tail: [a,b|c] vs [a|X] where X -> [b|c]
        heap.cells = vec![
            // 0: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 5: [a|X]
            LIS,
            (Con, a),
            (Ref, 0),
            // 8: X -> [b|c]
            LIS,
            (Con, b),
            (Con, c),
        ];
        heap.var_regs = vec![Addr(8).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //A jump landing on the wrong tail constant must fail
        heap.cells = vec![
            // 0: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 10: X -> b
            (Con, b),
        ];
        heap.var_regs = vec![Addr(10).into()];
        assert!(unify(&mut heap, 0, 5, 31).is_none());
    }

    /// Nested list `[[a,b],c]` vs itself, with the rhs reaching the inner list,
    /// an element of the inner list, and the outer tail through bound `Ref`s.
    #[test]
    fn equal_nested_list_with_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Jump replacing the whole inner list: [[a,b],c] vs [X,c] where X -> [a,b]
        heap.cells = vec![
            // 0: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: [X,c]
            LIS,
            (Ref, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 14: X -> [a,b]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(14).into()];
        let sub = unify(&mut heap, 0, 9, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same, through a ref chain X -> Y -> [a,b]
        heap.var_regs = vec![Var(1).into(), Addr(14).into()];
        let sub = unify(&mut heap, 0, 9, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump inside the inner list: [[a,b],c] vs [[a,X],c] where X -> b
        heap.cells = vec![
            // 0: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: [[a,X],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Ref, 0),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 18: X -> b
            (Con, b),
        ];
        heap.var_regs = vec![Addr(18).into()];
        let sub = unify(&mut heap, 0, 9, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Jump at the outer tail: [[a,b],c] vs [[a,b]|X] where X -> [c]
        heap.cells = vec![
            // 0: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: [[a,b]|X]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            (Ref, 0),
            // 16: X -> [c]
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(16).into()];
        let sub = unify(&mut heap, 0, 9, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //A jump landing on a differently shaped inner list must fail
        heap.cells = vec![
            // 0: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: [X,c]
            LIS,
            (Ref, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 14: X -> [a,c]
            LIS,
            (Con, a),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(14).into()];
        assert!(unify(&mut heap, 0, 9, 31).is_none());
    }

    /// An `Arg` bound earlier in the same unification must be dereferenced when
    /// it is met again inside a proper list. The clause term binds `A` from the
    /// first tuple slot, then re-uses `A` at a head / tail position of a list.
    #[test]
    fn equal_proper_list_with_arg_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Arg jump at a head position: (A,[A,b,c]) vs (a,[a,b,c])
        heap.cells = vec![
            // 0: (A,[A,b,c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Arg, 0),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: (a,[a,b,c])
            (Tup, 2),
            (Con, a),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 9, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());

        //Arg jump at a tail position: (A,[a,b|A]) vs ([c],[a,b,c])
        heap.cells = vec![
            // 0: (A,[a,b|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 7: ([c],[a,b,c])
            (Tup, 2),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(8)));
        assert!(sub.bound_vars.is_empty());

        //Arg jump at the root of a list: (A,A) vs ([a,b,c],[a,b,c])
        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: ([a,b,c],[a,b,c])
            (Tup, 2),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(4)));
        assert!(sub.bound_vars.is_empty());

        //An arg jump onto a conflicting element must fail: (A,[A,b,c]) vs (a,[c,b,c])
        heap.cells = vec![
            // 0: (A,[A,b,c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Arg, 0),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 9: (a,[c,b,c])
            (Tup, 2),
            (Con, a),
            LIS,
            (Con, c),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        assert!(unify(&mut heap, 0, 9, 31).is_none());
    }

    /// As `equal_proper_list_with_arg_jump`, but the list is improper so the
    /// re-used `Arg` sits in a constant-tail position.
    #[test]
    fn equal_con_tail_list_with_arg_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Arg jump at the constant tail: (A,[a|A]) vs (c,[a|c])
        heap.cells = vec![
            // 0: (A,[a|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: (c,[a|c])
            (Tup, 2),
            (Con, c),
            LIS,
            (Con, a),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //Arg jump at a head position: (A,[A|c]) vs (a,[a|c])
        heap.cells = vec![
            // 0: (A,[A|c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Arg, 0),
            (Con, c),
            // 5: (a,[a|c])
            (Tup, 2),
            (Con, a),
            LIS,
            (Con, a),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //Arg bound to a partial improper list: (A,[a,b|c]) vs ([b|c],[a,b|c])
        heap.cells = vec![
            // 0: (A,[a,b|c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: ([b|c],[a,b|c])
            (Tup, 2),
            LIS,
            (Con, b),
            (Con, c),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //A conflicting tail must fail: (A,[a|A]) vs (c,[a|b])
        heap.cells = vec![
            // 0: (A,[a|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: (c,[a|b])
            (Tup, 2),
            (Con, c),
            LIS,
            (Con, a),
            (Con, b),
        ];
        assert!(unify(&mut heap, 0, 5, 31).is_none());
    }

    /// As `equal_proper_list_with_arg_jump`, but the `Arg` stands for a nested
    /// list, so the jump target is itself a list.
    #[test]
    fn equal_nested_list_with_arg_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Arg standing for the inner list: (A,[A,c]) vs ([a,b],[[a,b],c])
        heap.cells = vec![
            // 0: (A,[A,c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Arg, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: ([a,b],[[a,b],c])
            (Tup, 2),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(8)));
        assert!(sub.bound_vars.is_empty());

        //Arg nested inside the inner list: (A,[[a,A],c]) vs (b,[[a,b],c])
        heap.cells = vec![
            // 0: (A,[[a,A],c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Arg, 0),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 11: (b,[[a,b],c])
            (Tup, 2),
            (Con, b),
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 11, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(12)));
        assert!(sub.bound_vars.is_empty());

        //A conflicting nested element must fail: (A,[A,c]) vs ([a,b],[[a,c],c])
        heap.cells = vec![
            // 0: (A,[A,c])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Arg, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: ([a,b],[[a,c],c])
            (Tup, 2),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        assert!(unify(&mut heap, 0, 7, 31).is_none());
    }

    /// Two-hop jump: `Arg` -> `Ref` -> list.
    ///
    /// `(A,A,A)` vs `(X,[a,b,c],[a,b,c])`:
    ///   1. `A = X`             (arg_reg[0] = Var(0), X still unbound)
    ///   2. `A = [a,b,c]`       (`A` derefs to `X`, so `X` binds to the list and
    ///                           arg_reg[0] must be updated to that address)
    ///   3. `A = [a,b,c]`       (`A` must now jump straight to the bound list)
    ///
    /// Step 3 is the interesting one: the walk has to follow the arg through the
    /// ref it was bound to and land on the list.
    #[test]
    fn equal_proper_list_with_arg_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[a,b,c],[a,b,c])
            (Tup, 3),
            (Ref, 0),
            // 6: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 13: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(6).into());
        assert_eq!(sub.get_arg(0), Some(Addr(6)));

        //Same shape, but the second list differs so the jump must expose the clash
        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[a,b,c],[a,b,b])
            (Tup, 3),
            (Ref, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 4, 31).is_none());
    }

    /// `Arg` -> `Ref` -> improper list, see `equal_proper_list_with_arg_ref_jump`.
    #[test]
    fn equal_con_tail_list_with_arg_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[a,b|c],[a,b|c])
            (Tup, 3),
            (Ref, 0),
            // 6: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 11: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(6).into());
        assert_eq!(sub.get_arg(0), Some(Addr(6)));

        //A proper list cannot unify with an improper one of the same prefix
        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[a,b|c],[a,b,c])
            (Tup, 3),
            (Ref, 0),
            // 6: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
            // 11: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 4, 31).is_none());
    }

    /// `Arg` -> `Ref` -> nested list, see `equal_proper_list_with_arg_ref_jump`.
    #[test]
    fn equal_nested_list_with_arg_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[[a,b],c],[[a,b],c])
            (Tup, 3),
            (Ref, 0),
            // 6: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 15: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(6).into());
        assert_eq!(sub.get_arg(0), Some(Addr(6)));

        //A differing inner element must be caught after the jump
        heap.cells = vec![
            // 0: (A,A,A)
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            // 4: (X,[[a,b],c],[[a,c],c])
            (Tup, 3),
            (Ref, 0),
            // 6: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 15: [[a,c],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 4, 31).is_none());
    }

    /// Both tails are the *same* `Arg`, so nothing needs binding — the two
    /// tails are already identical and unification is a pure structural check
    /// over the prefixes.
    #[test]
    fn unify_tail_same_arg() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //[a,b|A] vs [a,b|A]
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same tail arg but a clashing prefix must still fail: [a|A] vs [b|A]
        heap.cells = vec![
            // 0: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
            // 3: [b|A]
            LIS,
            (Con, b),
            (Arg, 0),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());

        //A shared tail arg nested one list deep: [[a|A],b] vs [[a|A],b]
        heap.cells = vec![
            // 0: [[a|A],b]
            LIS,
            LIS,
            (Con, a),
            (Arg, 0),
            LIS,
            (Con, b),
            EMPTY_LIS,
            // 7: [[a|A],b]
            LIS,
            LIS,
            (Con, a),
            (Arg, 0),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    /// A list tail that is an `Arg` meeting a list tail that is an (ultimately
    /// unbound) `Ref`. The arg register records the variable; no heap variable
    /// is bound.
    #[test]
    fn unify_tail_arg_to_ref() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //arg to unbound ref: [a,b|A] vs [a,b|X]
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert!(sub.bound_vars.is_empty());
        assert_eq!(heap.var_regs[0], VarReg::UNBOUND);

        //Same, with the arg on the right hand side
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 5, 0, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert!(sub.bound_vars.is_empty());
        assert_eq!(heap.var_regs[0], VarReg::UNBOUND);

        //arg to ref bound to other ref: X -> Y, so A must record the end of the chain
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(1)));
        assert!(sub.bound_vars.is_empty());
        assert_eq!(heap.var_regs, [Var(1).into(), VarReg::UNBOUND]);

        //Longer chain X -> Y -> Z
        heap.var_regs = vec![Var(1).into(), Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(2)));
        assert!(sub.bound_vars.is_empty());
    }

    /// Two unbound `Ref` tails meeting: one variable is bound to the other.
    #[test]
    fn unify_ref_tails() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //[a,b|X] vs [a,b|Y]
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a,b|Y]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 1),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs, [Var(1).into(), VarReg::UNBOUND]);

        //The same variable on both tails needs no binding: [a,b|X] vs [a,b|X]
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());
        assert_eq!(heap.var_regs, [VarReg::UNBOUND]);

        //Through chains on both sides: X -> Z, Y -> W
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a,b|Y]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 1),
        ];
        heap.var_regs = vec![
            Var(2).into(),
            Var(3).into(),
            VarReg::UNBOUND,
            VarReg::UNBOUND,
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[2]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), Var(3).into(), Var(3).into(), VarReg::UNBOUND]
        );

        //Two chains that already meet at the same variable need no binding
        heap.var_regs = vec![Var(2).into(), Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    /// The list tails are `Arg`s on the clause side, both bound to query
    /// variables during the same unification. When the second pair meets, the
    /// arg has to deref through the variable it was bound to, and binding the
    /// two variables together must be reflected back into the arg register.
    #[test]
    fn unify_ref_tails_through_arg() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //([a|A],[a|A]) vs ([a|X],[a|Y])
        heap.cells = vec![
            // 0: ([a|A],[a|A])
            (Tup, 2),
            LIS,
            (Con, a),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 7: ([a|X],[a|Y])
            (Tup, 2),
            LIS,
            (Con, a),
            (Ref, 0),
            LIS,
            (Con, a),
            (Ref, 1),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(1)));
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs, [Var(1).into(), VarReg::UNBOUND]);

        //Same, but the second query variable is behind a chain Y -> Z
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(2)));
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Var(2).into());

        //Both tails meet the same variable, so nothing is bound
        heap.cells = vec![
            // 0: ([a|A],[a|A])
            (Tup, 2),
            LIS,
            (Con, a),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 7: ([a|X],[a|X])
            (Tup, 2),
            LIS,
            (Con, a),
            (Ref, 0),
            LIS,
            (Con, a),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert!(sub.bound_vars.is_empty());
        assert_eq!(heap.var_regs, [VarReg::UNBOUND]);
    }

    /// `[a,b|X]` vs `[a,b]` — the open tail `X` must bind to the `[]` cell.
    #[test]
    fn bind_ref_tail_to_empty_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a,b]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert!(!sub.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());

        //Switch lhs/rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 5, 0, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());

        //Through Ref Chain: X -> Y, so the end of the chain is what binds
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[1]);
        assert_eq!(heap.var_regs, [Var(1).into(), Addr(9).into()]);

        //Through Arg: (A,[a,b|A]) vs (X,[a,b])
        //  A = X, then A (i.e. X) meets [] and must bind to it.
        heap.cells = vec![
            // 0: (A,[a,b|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 7: (X,[a,b])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(13).into());
        assert_eq!(sub.get_arg(0), Some(Addr(13)));

        //An open tail must not paper over a short rhs: [a,b|X] vs [a].
        //`b` has no counterpart, so this has to fail.
        //
        //KNOWN FAILURE: the catch-all arm of `unify` compares only the cell
        //*values* (`heap[addr1].1 == heap[addr2].1`) and ignores the tags.
        //`LIS` is `(Lis, 0)` and `EMPTY_LIS` is `(ELis, 0)`, so a cons cell and
        //`[]` compare equal. The two walks then desync — only the `Lis` side
        //asks for two more cells — and the loop exits early via `?`, reporting
        //success. The same hole makes `[a]` unify with `[a,b]`.
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a]
            LIS,
            (Con, a),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 5, 31).is_none());
    }

    /// `[a|X]` vs `[a,b,c]` — the open tail `X` must bind to the remaining
    /// list `[b,c]`, i.e. to the cons cell that starts it.
    #[test]
    fn bind_ref_tail_to_other_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a|X]
            LIS,
            (Con, a),
            (Ref, 0),
            // 3: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert!(!sub.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(5).into());

        //Switch lhs/rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 3, 0, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(5).into());

        //Through Ref Chain: X -> Y
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[1]);
        assert_eq!(heap.var_regs, [Var(1).into(), Addr(5).into()]);

        //Through Arg: (A,[a|A]) vs (X,[a,b,c])
        heap.cells = vec![
            // 0: (A,[a|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: (X,[a,b,c])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());
        assert_eq!(sub.get_arg(0), Some(Addr(9)));

        //Two open tails that are already the same variable: (A,[a|A]) vs (X,[a|X]).
        //A = X makes the second components identical, so this succeeds and binds
        //nothing beyond the arg register.
        heap.cells = vec![
            // 0: (A,[a|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: (X,[a|X])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Var(0)));
        assert!(sub.bound_vars.is_empty());
        assert_eq!(heap.var_regs, [VarReg::UNBOUND]);

        //Occurs check: (A,A) vs (X,[a|X]) would make X = [a|X]
        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: (X,[a|X])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 3, 31).is_none());
        //The failed binding must be rolled back
        assert_eq!(heap.var_regs, [VarReg::UNBOUND]);

        //A distinct tail variable is fine: (A,A) vs (X,[a|Y])
        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: (X,[a|Y])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            (Ref, 1),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(5).into());
        assert_eq!(sub.get_arg(0), Some(Addr(5)));
    }

    /// `[a,b|X]` vs `[a,b|c]` — the open tail binds to a plain constant,
    /// producing the improper list `[a,b|c]`.
    #[test]
    fn bind_ref_tail_to_con() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 5: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert!(!sub.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());

        //Switch lhs/rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 5, 0, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());

        //Through Ref Chain: X -> Y
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[1]);
        assert_eq!(heap.var_regs, [Var(1).into(), Addr(9).into()]);

        //Through Arg: (A,[a,b|A]) vs (X,[a,b|c])
        heap.cells = vec![
            // 0: (A,[a,b|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 7: (X,[a,b|c])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(13).into());
        assert_eq!(sub.get_arg(0), Some(Addr(13)));
    }

    /// `[a|X]` vs `[a,[b,c]]` — the open tail binds to the remaining list,
    /// whose single element is itself a list.
    #[test]
    fn bind_ref_tail_to_mested_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a|X]
            LIS,
            (Con, a),
            (Ref, 0),
            // 3: [a,[b,c]]
            LIS,
            (Con, a),
            LIS,
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert!(!sub.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(5).into());

        //Switch lhs/rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 3, 0, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(5).into());

        //Through Ref Chain: X -> Y
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[1]);
        assert_eq!(heap.var_regs, [Var(1).into(), Addr(5).into()]);

        //Binding the head of a nested list: [[a|X],c] vs [[a,b],c]
        heap.cells = vec![
            // 0: [[a|X],c]
            LIS,
            LIS,
            (Con, a),
            (Ref, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(10).into());

        //Through Arg: (A,[a|A]) vs (X,[a,[b,c]])
        heap.cells = vec![
            // 0: (A,[a|A])
            (Tup, 2),
            (Arg, 0),
            LIS,
            (Con, a),
            (Arg, 0),
            // 5: (X,[a,[b,c]])
            (Tup, 2),
            (Ref, 0),
            LIS,
            (Con, a),
            LIS,
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Addr(9).into());
        assert_eq!(sub.get_arg(0), Some(Addr(9)));
    }

    /// `[a,b|A]` vs `[a,b]` — the clause's open tail records `[]` in its arg
    /// register. No query variable is touched.
    #[test]
    fn bind_arg_tail_to_empty_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(9)));
        assert!(sub.bound_vars.is_empty());

        //Switch lhs/rhs
        let sub = unify(&mut heap, 5, 0, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(9)));
        assert!(sub.bound_vars.is_empty());

        //Through Ref Chain: [a,b|A] vs [a,b|X] where X -> []
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 10: X -> []
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());

        //Longer chain X -> Y -> []
        heap.var_regs = vec![Var(1).into(), Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());

        //An open arg tail must not paper over a short rhs: [a,b|A] vs [a].
        //See the matching note in `bind_ref_tail_to_empty_list` — `Lis` and
        //`ELis` both carry value 0, so the catch-all arm treats a cons cell and
        //`[]` as equal and the walks desync.
        //KNOWN FAILURE.
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a]
            LIS,
            (Con, a),
            EMPTY_LIS,
        ];
        assert!(unify(&mut heap, 0, 5, 31).is_none());
    }

    /// `[a|A]` vs `[a,b,c]` — the arg register records the remaining list.
    #[test]
    fn bind_arg_tail_to_other_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
            // 3: [a,b,c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(5)));
        assert!(sub.bound_vars.is_empty());

        //Switch lhs/rhs
        let sub = unify(&mut heap, 3, 0, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(5)));
        assert!(sub.bound_vars.is_empty());

        //Through Ref Chain: [a|A] vs [a|X] where X -> [b,c]
        heap.cells = vec![
            // 0: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
            // 3: [a|X]
            LIS,
            (Con, a),
            (Ref, 0),
            // 6: X -> [b,c]
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //Longer chain X -> Y -> [b,c]
        heap.var_regs = vec![Var(1).into(), Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //Occurs check: A vs [a|A] would need A = [a|A]
        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
        ];
        assert!(unify(&mut heap, 0, 1, 31).is_none());

        //A different arg in the tail is fine: A vs [a|B]
        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: [a|B]
            LIS,
            (Con, a),
            (Arg, 1),
        ];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(1)));
    }

    /// `[a,b|A]` vs `[a,b|c]` — the arg register records the constant tail.
    #[test]
    fn bind_arg_tail_to_con() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b|c]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Con, c),
        ];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(9)));
        assert!(sub.bound_vars.is_empty());

        //Switch lhs/rhs
        let sub = unify(&mut heap, 5, 0, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(9)));
        assert!(sub.bound_vars.is_empty());

        //Through Ref Chain: [a,b|A] vs [a,b|X] where X -> c
        heap.cells = vec![
            // 0: [a,b|A]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Arg, 0),
            // 5: [a,b|X]
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            (Ref, 0),
            // 10: X -> c
            (Con, c),
        ];
        heap.var_regs = vec![Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());

        //Longer chain X -> Y -> c
        heap.var_regs = vec![Var(1).into(), Addr(10).into()];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());
    }

    /// `[a|A]` vs `[a,[b,c]]` — the arg register records the remaining list,
    /// whose single element is itself a list.
    #[test]
    fn bind_arg_tail_to_mested_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Standard
        heap.cells = vec![
            // 0: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
            // 3: [a,[b,c]]
            LIS,
            (Con, a),
            LIS,
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(5)));
        assert!(sub.bound_vars.is_empty());

        //Switch lhs/rhs
        let sub = unify(&mut heap, 3, 0, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(5)));
        assert!(sub.bound_vars.is_empty());

        //Binding the tail of a nested list: [[a|A],c] vs [[a,b],c]
        heap.cells = vec![
            // 0: [[a|A],c]
            LIS,
            LIS,
            (Con, a),
            (Arg, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 7: [[a,b],c]
            LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert!(sub.bound_vars.is_empty());

        //Through Ref Chain: [a|A] vs [a|X] where X -> [[b,c]]
        heap.cells = vec![
            // 0: [a|A]
            LIS,
            (Con, a),
            (Arg, 0),
            // 3: [a|X]
            LIS,
            (Con, a),
            (Ref, 0),
            // 6: X -> [[b,c]]
            LIS,
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());

        //Longer chain X -> Y -> [[b,c]]
        heap.var_regs = vec![Var(1).into(), Addr(6).into()];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert!(sub.bound_vars.is_empty());
    }

    #[test]
    fn bind_variable_tail() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Arg Tail to Empty List

        //Arg Tail to constant

        //Arg Tail to other list

        //Ref Tail to Empty List

        //Ref Tail to constant

        //Ref Tail to other list
    }

    //-----------------------------------------------------------
    //----- Ref & Args (variable chaining) ----------------------
    //-----------------------------------------------------------

    #[test]
    fn unify_refs() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.cells = vec![(Ref, 0), (Ref, 1)];

        //Simplest
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Var(1).into());
        assert_eq!(heap.var_regs[1], VarReg::UNBOUND);

        //Through chain on rhs
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), Var(2).into(), VarReg::UNBOUND]
        );

        //Through chain on lhs
        heap.var_regs = vec![Var(2).into(), VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[2]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), VarReg::UNBOUND, Var(1).into(),]
        );

        //Through chain on lhs & rhs
        heap.var_regs = vec![
            Var(2).into(),
            Var(3).into(),
            VarReg::UNBOUND,
            VarReg::UNBOUND,
        ];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[2]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), Var(3).into(), Var(3).into(), VarReg::UNBOUND]
        );
    }

    #[test]
    fn arg_to_ref() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Bind arg to ref
        heap.cells = vec![(Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert!(sub.bound_vars.is_empty());
        assert_eq!(sub.get_arg(0).unwrap(), Var(0));

        //Bind arg to ref through chain
        heap.cells = vec![(Arg, 0), (Ref, 0)];
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert!(sub.bound_vars.is_empty());
        assert_eq!(sub.get_arg(0).unwrap(), Var(1));
    }

    #[test]
    fn unify_ref_through_arg() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        // Unify through arg
        heap.cells = vec![(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(1));
        assert_eq!(sub.bound_vars.as_slice(), [0]);
        assert_eq!(heap.var_regs[0], Var(1).into());

        //unify through arg + chain
        heap.cells = vec![(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(2));
        assert_eq!(sub.bound_vars.as_slice(), [0]);
        assert_eq!(heap.var_regs[0], Var(2).into());

        //(A,A,B) / (X,Y,X)
        // A -> X
        // A -> X -> Y
        // B -> X -> Y
        heap.cells = vec![
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 1),
            (Tup, 3),
            (Ref, 0),
            (Ref, 1),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 4, 15).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(1));
        assert_eq!(sub.get_arg(1).unwrap(), Var(1));
        assert_eq!(sub.bound_vars.as_slice(), [0]);
        assert_eq!(heap.var_regs[0], Var(1).into());
    }

    //-----------------------------------------------------------
    //--- Ref & Args (binding to structures) --------------------
    //-----------------------------------------------------------

    #[test]
    fn ref_to_con_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![(Ref, 0), (Comp, 2), (Con, p), (Con, a)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 0, 1, 15).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
        // switch lhs rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 1, 0, 15).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    #[test]
    fn ref_to_con_lis() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![(Ref, 0), LIS, (Con, p), LIS, (Con, a), EMPTY_LIS];
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 0, 1, 15).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    #[test]
    fn ref_to_con_tup_through_ref_jump() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.cells = vec![
            //0: (p,a)
            (Tup, 2),
            (Con, p),
            (Con, a),
            (Ref, 0), // Var(1) -> Addr(0)
            (Ref, 2),
        ];
        heap.var_regs = vec![Var(1).into(), Addr(0).into(), VarReg::UNBOUND];
        let binding = unify(&mut heap, 3, 4, 15).unwrap();
        assert!(binding.bound(2));
        assert!(!binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[2], Addr(0).into());
        // Switch lhs rhs
        heap.var_regs = vec![Var(1).into(), Addr(0).into(), VarReg::UNBOUND];
        let binding = unify(&mut heap, 4, 3, 15).unwrap();
        assert!(binding.bound(2));
        assert!(!binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[2], Addr(0).into());
    }

    #[test]
    fn ref_to_con_tup_through_arg() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            //0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            //3: ((p,a),X)
            (Tup, 2),
            (Tup, 2),
            (Con, p),
            (Con, a),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 0, 3, 15).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(4).into());
    }

    #[test]
    fn bind_arg_to_con_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
    }

    #[test]
    fn bind_arg_to_con_tup() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
    }

    //-----------------------------------------------------------
    //---------- Occurs checks ----------------------------------
    //-----------------------------------------------------------

    #[test]
    fn arg_occurs() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: (A, B)
            (Tup, 2),
            (Arg, 0),
            (Arg, 1),
        ];
        assert!(unify(&mut heap, 0, 1, 31).is_none());

        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: (B, C)
            (Tup, 2),
            (Arg, 1),
            (Arg, 2),
        ];
        assert!(unify(&mut heap, 0, 1, 31).is_some());
    }

    #[test]
    fn ref_occurs() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];
        heap.cells = vec![
            // 0: X
            (Ref, 0),
            // 1: (X, Y)
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];
        assert!(unify(&mut heap, 0, 1, 31).is_none());

        heap.cells = vec![
            // 0: X
            (Ref, 0),
            // 1: (Y, Z)
            (Tup, 2),
            (Ref, 1),
            (Ref, 2),
        ];
        assert!(unify(&mut heap, 0, 1, 31).is_some());
    }

    #[test]
    fn arg_occurs_in_bound_ref() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs.push(VarReg::UNBOUND);

        heap.cells = vec![
            // 0: (A,(A,B))
            (Tup, 2),
            (Arg, 0),
            (Tup, 2),
            (Arg, 0),
            (Arg, 1),
            // 5: (X,X)
            (Tup, 2),
            (Ref, 0),
            (Ref, 0),
        ];
        assert!(unify(&mut heap, 0, 5, 31).is_none());

        heap.cells = vec![
            // 0: (A,(B,C))
            (Tup, 2),
            (Arg, 0),
            (Tup, 2),
            (Arg, 1),
            (Arg, 2),
            // 5: (X,X)
            (Tup, 2),
            (Ref, 0),
            (Ref, 0),
        ];
        assert!(unify(&mut heap, 0, 5, 31).is_some());
    }

    #[test]
    fn ref_occurs_in_bound_arg() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: (X,(X,Y))
            (Tup, 2),
            (Ref, 0),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());

        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: (X,(Y,Z))
            (Tup, 2),
            (Ref, 0),
            (Tup, 2),
            (Ref, 1),
            (Ref, 2),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_some());
    }

    #[test]
    fn occurs_two_args_bound_to_same_var() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A,B,(A,B))
            (Tup, 3),
            (Arg, 0),
            (Arg, 1),
            (Tup, 2),
            (Arg, 0),
            (Arg, 1),
            // 6: (X,X,X)
            (Tup, 3),
            (Ref, 0),
            (Ref, 0),
            (Ref, 0),
        ];
        assert!(unify(&mut heap, 0, 6, 31).is_none());

        heap.cells = vec![
            // 0: (A,B,(C,D))
            (Tup, 3),
            (Arg, 0),
            (Arg, 1),
            (Tup, 2),
            (Arg, 2),
            (Arg, 3),
            // 6: (X,X,X)
            (Tup, 3),
            (Ref, 0),
            (Ref, 0),
            (Ref, 0),
        ];
        assert!(unify(&mut heap, 0, 6, 31).is_some());
    }

    #[test]
    fn occurs_arg_bound_to_structure_then_var() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: ((X,Y),X)
            (Tup, 2),
            (Ref, 0),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());

        heap.cells = vec![
            // 0: (A,A)
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            // 3: ((X,Y),Z)
            (Tup, 2),
            (Ref, 0),
            (Tup, 2),
            (Ref, 1),
            (Ref, 2),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_some());
    }

    /// clause `(A,A,(A,B))`  vs  goal `(X,Y,Y)`
    /// Unification order:
    ///   1. `A = X`                     (arg_reg[0] = X)
    ///   2. `A = Y`  ⟹ `X = Y`        (pushes binding X → Y)
    ///   3. `(A,B) = Y`                 (Y meets the tuple containing A)
    ///
    /// At step 3 the tuple contains `A` (Arg 0). `A` is bound to `X`, and
    /// `X` is bound to `Y` — so `A` transitively *is* `Y`, and binding
    /// `Y → (A,B)` closes a cycle (`Y = (Y,B)`).
    ///
    /// But `occurs` collects `bound_args` by comparing `get_arg(0)` (== X)
    /// directly against `ref_addr` (== Y). It does not chase `X → Y` via
    /// `bound()`, so `A` is NOT added to `bound_args`, the tuple walk finds an
    /// `Arg` that isn't flagged, and the cycle slips through.
    ///
    /// A correct occurs check should return `None`.
    #[test]
    fn arg_occurs_arg_ref_chain() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A, A, (A,B))
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Tup, 2),
            (Arg, 0),
            (Arg, 1),
            // 6: (X, Y, Y)
            (Tup, 3),
            (Ref, 0),
            (Ref, 1),
            (Ref, 1),
        ];

        assert!(unify(&mut heap, 0, 6, 31).is_none());
    }

    #[test]
    fn ref_occurs_arg_ref_chain() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A, B, B)
            (Tup, 3),
            (Arg, 0),
            (Arg, 1),
            (Arg, 1),
            // 4: (X, X, (X,Y))
            (Tup, 3),
            (Ref, 0),
            (Ref, 0),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];

        assert!(unify(&mut heap, 0, 4, 31).is_none());
    }

    //-----------------------------------------------------------
    //---------- needs_rebuild flag -----------------------------
    //-----------------------------------------------------------
    //
    // `Substitution.needs_rebuild[i]` answers one question about
    // `bound_vars[i]`: does the term it is now bound to contain `Arg` cells?
    //
    // `re_build_bound_arg_terms` in `build.rs` is the only consumer. It walks
    // the flagged bindings and rebuilds each one in query space, replacing
    // every `Arg` with the ref or address held in the matching arg register.
    // A binding whose target is already free of `Arg` cells is valid where it
    // sits, so the flag must stay `false` for it — rebuilding would copy the
    // term for nothing.
    //
    // Only `bind_ref_to_complex` can produce `true`; it takes the value from
    // `occurs`, which reports whether the sub-term walk saw any `Arg`. Every
    // other arm of `unify` that pushes a bound var (`Ref`/`Ref`, and the two
    // `Ref`/atomic catch-alls) passes `false` literally. `bind_arg` pushes no
    // bound var at all, so it never contributes an entry.
    //
    // `needs_rebuild` is index-aligned with `bound_vars` — `build.rs` indexes
    // it with `substitution.len()`, which derefs to `bound_vars` — so the two
    // must always have the same length.

    /// A ref bound to a ground structure must NOT be flagged: there are no
    /// `Arg` cells to substitute, so the term on the heap is already correct.
    #[test]
    fn needs_rebuild_false_for_ground_complex() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //X = p(a,b)
        heap.cells = vec![(Ref, 0), (Comp, 3), (Con, p), (Con, a), (Con, b)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());

        //X = (a,b)
        heap.cells = vec![(Ref, 0), (Tup, 2), (Con, a), (Con, b)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());

        //X = [a,b]
        heap.cells = vec![(Ref, 0), LIS, (Con, a), LIS, (Con, b), EMPTY_LIS];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());

        //Nesting changes nothing while the term stays ground: X = p((a,b))
        heap.cells = vec![(Ref, 0), (Comp, 2), (Con, p), (Tup, 2), (Con, a), (Con, b)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    /// A ref bound to a structure containing clause variables must be flagged,
    /// whichever side of `unify` the ref arrives on and whatever the structure
    /// tag is.
    #[test]
    fn needs_rebuild_true_for_complex_with_args() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //p(A) = X  -- ref on the rhs
        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //X = p(A)  -- ref on the lhs, same outcome
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 3, 0, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //(a,A) = X
        heap.cells = vec![(Tup, 2), (Con, a), (Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //[a|A] = X
        heap.cells = vec![LIS, (Con, a), (Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //{a,A} = X  -- sets reach bind_ref_to_complex too
        heap.cells = vec![(Set, 2), (Con, a), (Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //The arg can sit arbitrarily deep: p((a,A)) = X
        heap.cells = vec![(Comp, 2), (Con, p), (Tup, 2), (Con, a), (Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(0).into());
    }

    /// The arms of `unify` that push a bound var without going through
    /// `bind_ref_to_complex` always record `false` — there is no structure to
    /// rebuild.
    #[test]
    fn needs_rebuild_false_for_ref_and_atomic_bindings() {
        let a = SymbolDB::set_const("a");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //X = Y  -- (Ref, Ref)
        heap.cells = vec![(Ref, 0), (Ref, 1)];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Var(1).into());

        //X = a  -- (Ref, _)
        heap.cells = vec![(Ref, 0), (Con, a)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());

        //a = X  -- (_, Ref)
        heap.cells = vec![(Con, a), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(0).into());

        //X = 5  -- integers are atomic
        heap.cells = vec![(Ref, 0), (Int, 5)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());

        //X = []  -- ELis is not in the Lis|Comp|Set|Tup arm, so this is the
        //atomic path rather than bind_ref_to_complex. Either way there is
        //nothing to rebuild.
        heap.cells = vec![(Ref, 0), EMPTY_LIS];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    /// `occurs` scans with `next_cell`, which dereferences bound refs and
    /// descends into their targets. So an `Arg` reachable only through an
    /// already-bound ref still forces a rebuild.
    ///
    /// Here `X` is bound to `q(A)` before the call, and the term being bound
    /// to `Y` is `p(X)`. `p(X)` holds no `Arg` cell directly, but walking it
    /// steps through `X` into `q(A)` and finds one.
    #[test]
    fn needs_rebuild_follows_bound_ref_into_arg_term() {
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: p(X)
            (Comp, 2),
            (Con, p),
            (Ref, 0), // X -> Addr(3)
            // 3: q(A)
            (Comp, 2),
            (Con, q),
            (Arg, 0),
            // 6: Y
            (Ref, 1),
        ];
        heap.var_regs = vec![Addr(3).into(), VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 6, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[1]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[1], Addr(0).into());
        //X is untouched by this unification.
        assert_eq!(heap.var_regs[0], Addr(3).into());

        //Control: the same shape with the inner arg replaced by a constant
        //must not be flagged.
        heap.cells = vec![
            // 0: p(X)
            (Comp, 2),
            (Con, p),
            (Ref, 0), // X -> Addr(3)
            // 3: q(q)
            (Comp, 2),
            (Con, q),
            (Con, q),
            // 6: Y
            (Ref, 1),
        ];
        heap.var_regs = vec![Addr(3).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 6, 15).unwrap();
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[1], Addr(0).into());
    }

    /// The flag tracks the presence of `Arg` cells in the term, not whether
    /// those args are still unresolved. `A` is already bound to `a` by the
    /// time `p(A)` meets `X`, but `p(A)` on the heap still literally contains
    /// `(Arg, 0)`, so it must be rebuilt before it can stand as `X`'s value.
    #[test]
    fn needs_rebuild_true_when_arg_already_bound() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: (A, p(A))
            (Tup, 2),
            (Arg, 0),
            (Comp, 2),
            (Con, p),
            (Arg, 0),
            // 5: (a, X)
            (Tup, 2),
            (Con, a),
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 5, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(6)));
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(2).into());
    }

    /// `needs_rebuild` is positional: entry `i` describes `bound_vars[i]`.
    /// Bind three vars in one call, one flagged and two not, and check the
    /// flags line up rather than merely containing the right multiset.
    #[test]
    fn needs_rebuild_aligns_with_bound_vars() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let p = SymbolDB::set_const("p");
        let q = SymbolDB::set_const("q");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: (p(A), q(a), b)
            (Tup, 3),
            (Comp, 2),
            (Con, p),
            (Arg, 0),
            (Comp, 2),
            (Con, q),
            (Con, a),
            (Con, b),
            // 8: (X, Y, Z)
            (Tup, 3),
            (Ref, 0),
            (Ref, 1),
            (Ref, 2),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        //X -> p(A) needs a rebuild, Y -> q(a) does not, Z -> b is atomic.
        assert_eq!(sub.bound_vars.as_slice(), &[0, 1, 2]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true, false, false]);
        assert_eq!(sub.needs_rebuild.len(), sub.bound_vars.len());
        assert_eq!(heap.var_regs[0], Addr(1).into());
        assert_eq!(heap.var_regs[1], Addr(4).into());
        assert_eq!(heap.var_regs[2], Addr(7).into());
    }

    /// No bound vars means no flags. In particular `bind_arg` never pushes an
    /// entry, even when the arg is bound to a structure that `build` will
    /// later have to expand.
    #[test]
    fn needs_rebuild_empty_when_no_vars_bind() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Ground vs ground: nothing is recorded at all.
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 3, 15).unwrap();
        assert_eq!(sub, Substitution::default());
        assert!(sub.needs_rebuild.is_empty());

        //A = p(a): the arg register is set, but no *variable* was bound, so
        //bound_vars and needs_rebuild both stay empty.
        heap.cells = vec![(Arg, 0), (Comp, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 1, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(1)));
        assert!(sub.bound_vars.is_empty());
        assert!(sub.needs_rebuild.is_empty());
    }

    //-----------------------------------------------------------
    //-- Complex Combinations and Edge Cases ---
    //-----------------------------------------------------------
    //
    // Each case here is laid out the way resolution actually meets it: a
    // clause head on the left, a goal on the right, with `Arg` cells only ever
    // on the head side and `Ref` cells only ever on the goal side. The point
    // is to mix container types (comp / tup / list / set) with the two kinds
    // of indirection (arg registers and bound refs) in a single call, since
    // the earlier sections mostly exercise one of those at a time.

    /// Head `p([a|A], f(A))` vs goal `p([a,b,c], X)`.
    ///
    /// `A` is first bound by the list tail, then reappears inside a compound
    /// that the goal variable `X` has to take as its value. Because the term
    /// `X` binds to still contains `(Arg, 0)`, this is a rebuild case.
    #[test]
    fn head_list_tail_arg_reused_in_comp() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p([a|A], f(A))
            (Comp, 3),
            (Con, p),
            LIS,
            (Con, a),
            (Arg, 0),
            (Comp, 2),
            (Con, f),
            (Arg, 0),
            // 8: goal p([a,b,c], X)
            (Comp, 3),
            (Con, p),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Con, c),
            EMPTY_LIS,
            (Ref, 0),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        //A is the tail [b,c], which starts at the second cons cell.
        assert_eq!(sub.get_arg(0), Some(Addr(12)));
        //X takes the head's f(A) as-is; build must expand the arg later.
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[true]);
        assert_eq!(heap.var_regs[0], Addr(5).into());
    }

    /// Head `p((A,b), [A,c])` vs goal `p((a,b), [X,c])`.
    ///
    /// The same arg spans a tuple and a list. By the time the list element is
    /// reached `A` already derefs to the constant `a` inside the *goal's*
    /// tuple, so the goal variable `X` ends up pointing back into the goal
    /// rather than into the head.
    #[test]
    fn head_arg_shared_between_tuple_and_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p((A,b), [A,c])
            (Comp, 3),
            (Con, p),
            (Tup, 2),
            (Arg, 0),
            (Con, b),
            LIS,
            (Arg, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            // 10: goal p((a,b), [X,c])
            (Comp, 3),
            (Con, p),
            (Tup, 2),
            (Con, a),
            (Con, b),
            LIS,
            (Ref, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 10, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(13)));
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        //X is bound to a plain constant, so nothing needs rebuilding.
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(13).into());

        //Same head against p((a,b), [d,c]) must fail: A is already a.
        let d = SymbolDB::set_const("d");
        heap.cells[16] = (Con, d);
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 10, 31).is_none());
    }

    /// Head `p(f([a|A]), A)` vs goal `p(Y, [b])` where `Y` is already bound to
    /// `f([a,b])`.
    ///
    /// Both indirections fire in one call: the goal side jumps through a bound
    /// ref into a compound, and the head side later jumps through the arg
    /// register into the list tail it picked up inside that compound. No new
    /// variable is bound, so the substitution holds only the arg.
    #[test]
    fn head_arg_jump_meets_goal_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(f([a|A]), A)
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            LIS,
            (Con, a),
            (Arg, 0),
            (Arg, 0),
            // 8: goal p(Y, [b])
            (Comp, 3),
            (Con, p),
            (Ref, 0),
            LIS,
            (Con, b),
            EMPTY_LIS,
            // 14: Y -> f([a,b])
            (Comp, 2),
            (Con, f),
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![Addr(14).into()];

        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        //A is the [b] tail living inside Y's term.
        assert_eq!(sub.get_arg(0), Some(Addr(18)));
        assert!(sub.bound_vars.is_empty());
        assert!(sub.needs_rebuild.is_empty());
        //Y is untouched.
        assert_eq!(heap.var_regs[0], Addr(14).into());

        //If the goal's second argument disagrees with the tail found inside Y
        //the whole thing must fail: p(Y, [c]).
        let c = SymbolDB::set_const("c");
        heap.cells[12] = (Con, c);
        heap.var_regs = vec![Addr(14).into()];
        assert!(unify(&mut heap, 0, 8, 31).is_none());
    }

    /// Head `p(f(a), [f(a)])` vs goal `p(X, [X])`.
    ///
    /// The goal variable is bound by the first argument and then has to be
    /// dereferenced through a list to check the second, so the same structure
    /// is compared once by binding and once by walking.
    #[test]
    fn goal_var_bound_then_rechecked_through_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(f(a), [f(a)])
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            (Con, a),
            LIS,
            (Comp, 2),
            (Con, f),
            (Con, a),
            EMPTY_LIS,
            // 10: goal p(X, [X])
            (Comp, 3),
            (Con, p),
            (Ref, 0),
            LIS,
            (Ref, 0),
            EMPTY_LIS,
        ];
        heap.var_regs = vec![VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 10, 15).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[false]);
        assert_eq!(heap.var_regs[0], Addr(2).into());

        //Head p(f(a), [f(b)]) against the same goal must fail: X cannot be
        //both f(a) and f(b). (Rollback of the binding made on the way in is
        //covered separately by `failed_unify_must_undo_bindings`.)
        heap.cells[8] = (Con, b);
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 10, 31).is_none());
    }

    /// Head `p([f(A)|B])` vs goal `p([f(a), g(b)])`.
    ///
    /// A compound nested inside a partial list: one arg is filled from inside
    /// the list's head, the other swallows the remaining tail.
    #[test]
    fn head_comp_inside_partial_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let f = SymbolDB::set_const("f");
        let g = SymbolDB::set_const("g");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p([f(A)|B])
            (Comp, 2),
            (Con, p),
            LIS,
            (Comp, 2),
            (Con, f),
            (Arg, 0),
            (Arg, 1),
            // 7: goal p([f(a), g(b)])
            (Comp, 2),
            (Con, p),
            LIS,
            (Comp, 2),
            (Con, f),
            (Con, a),
            LIS,
            (Comp, 2),
            (Con, g),
            (Con, b),
            EMPTY_LIS,
        ];

        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(12)));
        //B is the whole [g(b)] tail.
        assert_eq!(sub.get_arg(1), Some(Addr(13)));
        assert!(sub.bound_vars.is_empty());

        //A functor mismatch inside the list head must still fail.
        heap.cells[11] = (Con, g);
        assert!(unify(&mut heap, 0, 7, 31).is_none());
    }

    /// Head `p([{a,b}|A])` vs goal `p([{b,a}, c])`.
    ///
    /// Set unification is equality-only and order-insensitive, and it has to
    /// leave both walks positioned correctly so the list tail still lines up
    /// afterwards.
    #[test]
    fn head_set_inside_list_with_tail_arg() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p([{a,b}|A])
            (Comp, 2),
            (Con, p),
            LIS,
            (Set, 2),
            (Con, a),
            (Con, b),
            (Arg, 0),
            // 7: goal p([{b,a}, c])
            (Comp, 2),
            (Con, p),
            LIS,
            (Set, 2),
            (Con, b),
            (Con, a),
            LIS,
            (Con, c),
            EMPTY_LIS,
        ];

        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(13)));
        assert!(sub.bound_vars.is_empty());

        //{a,b} vs {b,c} is not the same set, so the whole head fails.
        heap.cells[12] = (Con, c);
        assert!(unify(&mut heap, 0, 7, 31).is_none());
    }

    /// Head `p(A, A, f(A))` vs goal `p(X, [a], Y)`.
    ///
    /// The arg is threaded through every kind of target in one call:
    ///   1. `A = X`      — arg register holds `Var(0)`.
    ///   2. `A = [a]`    — `A` derefs to `X`, so `X` binds to the list and
    ///                     `update_arg_regs` rewrites the arg to that address.
    ///   3. `f(A) = Y`   — `Y` binds to a term that still contains `(Arg, 0)`.
    ///
    /// Note the two bindings get different rebuild flags, in order.
    #[test]
    fn head_arg_through_ref_then_into_comp() {
        let a = SymbolDB::set_const("a");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(A, A, f(A))
            (Comp, 4),
            (Con, p),
            (Arg, 0),
            (Arg, 0),
            (Comp, 2),
            (Con, f),
            (Arg, 0),
            // 7: goal p(X, [a], Y)
            (Comp, 4),
            (Con, p),
            (Ref, 0),
            LIS,
            (Con, a),
            EMPTY_LIS,
            (Ref, 1),
        ];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];

        let sub = unify(&mut heap, 0, 7, 15).unwrap();
        //The arg no longer holds Var(0): binding X rewrote it to the list.
        assert_eq!(sub.get_arg(0), Some(Addr(10)));
        assert_eq!(sub.bound_vars.as_slice(), &[0, 1]);
        assert_eq!(sub.needs_rebuild.as_slice(), &[false, true]);
        assert_eq!(heap.var_regs[0], Addr(10).into());
        assert_eq!(heap.var_regs[1], Addr(4).into());
    }

    /// Head `p(f([{a,b}, (c,A)]))` vs goal `p(f([{b,a}, (c,d)]))`.
    ///
    /// Comp wrapping a list holding a set and a tuple, with the arg at the
    /// bottom — mostly a check that the nesting arithmetic survives four
    /// container types stacked on top of each other.
    #[test]
    fn head_deeply_mixed_nesting() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let d = SymbolDB::set_const("d");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(f([{a,b}, (c,A)]))
            (Comp, 2),
            (Con, p),
            (Comp, 2),
            (Con, f),
            LIS,
            (Set, 2),
            (Con, a),
            (Con, b),
            LIS,
            (Tup, 2),
            (Con, c),
            (Arg, 0),
            EMPTY_LIS,
            // 13: goal p(f([{b,a}, (c,d)]))
            (Comp, 2),
            (Con, p),
            (Comp, 2),
            (Con, f),
            LIS,
            (Set, 2),
            (Con, b),
            (Con, a),
            LIS,
            (Tup, 2),
            (Con, c),
            (Con, d),
            EMPTY_LIS,
        ];

        let sub = unify(&mut heap, 0, 13, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(24)));
        assert!(sub.bound_vars.is_empty());

        //Break the innermost tuple and the whole nest must fail.
        heap.cells[23] = (Con, d);
        assert!(unify(&mut heap, 0, 13, 31).is_none());
    }

    /// Head `p(f(A), [A])` vs goal `p(f([b]), [[b]])`.
    ///
    /// The arg's value is itself a list buried in a compound, and its second
    /// occurrence has to be re-matched against a list nested one level deeper
    /// on the goal side.
    #[test]
    fn head_arg_bound_to_list_inside_comp() {
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(f(A), [A])
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            (Arg, 0),
            LIS,
            (Arg, 0),
            EMPTY_LIS,
            // 8: goal p(f([b]), [[b]])
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            LIS,
            (Con, b),
            EMPTY_LIS,
            LIS,
            LIS,
            (Con, b),
            EMPTY_LIS,
            EMPTY_LIS,
        ];

        let sub = unify(&mut heap, 0, 8, 15).unwrap();
        assert_eq!(sub.get_arg(0), Some(Addr(12)));
        assert!(sub.bound_vars.is_empty());

        //p(f([b]), [[c]]) must fail — the two occurrences of A disagree.
        heap.cells[17] = (Con, c);
        assert!(unify(&mut heap, 0, 8, 31).is_none());
    }

    /// Sanity control for the two tag tests below: a plain arity mismatch is
    /// rejected, because the catch-all arm compares `2` against `3` and they
    /// genuinely differ.
    #[test]
    fn mismatched_arity_must_not_unify() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(a)
            (Comp, 2),
            (Con, p),
            (Con, a),
            // 3: goal p(a,a)
            (Comp, 3),
            (Con, p),
            (Con, a),
            (Con, a),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());
    }

    /// Head `p(a)` vs goal `(p,a)`: a compound is not a tuple.
    ///
    /// `unify` has a dedicated arm for `(Comp|Tup, Comp|Tup)` that correctly
    /// demands the whole cell match, so `(Comp, 2)` vs `(Tup, 2)` fails the
    /// guard. But a failed guard just falls through to the later
    /// `_ if heap[addr1].1 == heap[addr2].1 => continue` arm, which compares
    /// only the cell *value*. Both cells carry 2, so the mismatch is accepted;
    /// both tags then increment the walks by the same amount, so the contents
    /// line up and the whole thing reports success.
    ///
    /// KNOWN FAILURE. Same root cause as the `Lis`/`ELis` conflation in
    /// `bind_ref_tail_to_empty_list` — comparing whole cells in that arm
    /// would fix both.
    #[test]
    fn comp_and_tup_must_not_unify() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(a)
            (Comp, 2),
            (Con, p),
            (Con, a),
            // 3: goal (p,a)
            (Tup, 2),
            (Con, p),
            (Con, a),
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());
    }

    /// Head `p(0)` vs goal `p([])`: the integer zero is not the empty list.
    ///
    /// `(Int, 0)` and `(ELis, 0)` both carry the value 0, so the same
    /// value-only catch-all arm accepts them. Neither tag increments the
    /// walks, so the two sides stay in step and unification succeeds.
    ///
    /// KNOWN FAILURE, same root cause as `comp_and_tup_must_not_unify`.
    #[test]
    fn int_zero_and_empty_list_must_not_unify() {
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        heap.cells = vec![
            // 0: head p(0)
            (Comp, 2),
            (Con, p),
            (Int, 0),
            // 3: goal p([])
            (Comp, 2),
            (Con, p),
            EMPTY_LIS,
        ];
        assert!(unify(&mut heap, 0, 3, 31).is_none());
    }

    /// A failed `unify` must leave the heap exactly as it found it.
    ///
    /// Callers rely on this. `env.rs` does
    /// `let Some(sub) = unify(heap, head, self.goal) else { continue };` and
    /// moves straight on to the next clause, and `\=/2` in `defaults.rs` does
    /// `unify(...,31).is_none()` and discards the result. Neither unwinds
    /// anything, so any binding made before the mismatch has to be undone
    /// inside `unify`.
    ///
    /// Only the two `bind_ref_to_complex` arms actually do this — they route
    /// failure through `undo_substitution`, which calls `heap.unbind`. Every
    /// other failure exit is a bare `return None`:
    ///   - the final catch-all `_ => return None`,
    ///   - `(Set, Set) => return None`,
    ///   - both `bind_arg` arms.
    /// Those leave the query variables bound to whatever they matched before
    /// the mismatch was found, which will corrupt the next clause attempt.
    ///
    /// KNOWN FAILURE. Both cases below bind `X` successfully on the first
    /// argument and only then hit a mismatch on the second.
    #[test]
    fn failed_unify_must_undo_bindings() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let f = SymbolDB::set_const("f");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.var_constrained = vec![false; 32];

        //Head p(f(a), b) vs goal p(X, c) -- exits via the catch-all arm.
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            (Con, a),
            (Con, b),
            // 6: goal
            (Comp, 3),
            (Con, p),
            (Ref, 0),
            (Con, c),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 6, 31).is_none());
        let after_con_mismatch = heap.var_regs[0];

        //Head p(f(a), {a,b}) vs goal p(X, {a,c}) -- exits via (Set, Set).
        heap.cells = vec![
            (Comp, 3),
            (Con, p),
            (Comp, 2),
            (Con, f),
            (Con, a),
            (Set, 2),
            (Con, a),
            (Con, b),
            // 8: goal
            (Comp, 3),
            (Con, p),
            (Ref, 0),
            (Set, 2),
            (Con, a),
            (Con, c),
        ];
        heap.var_regs = vec![VarReg::UNBOUND];
        assert!(unify(&mut heap, 0, 8, 31).is_none());
        let after_set_mismatch = heap.var_regs[0];

        //Reported together so one failure doesn't hide the other.
        assert_eq!(
            (after_con_mismatch, after_set_mismatch),
            (VarReg::UNBOUND, VarReg::UNBOUND),
            "failed unification left X bound"
        );
    }
}
