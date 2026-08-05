//! Unification algorithm and substitution management.
use smallvec::SmallVec;
use super::Substitution;
use crate::heap::{
    Cell, DualWalk, Heap, QueryHeap, SubWalk,
    Tag::*,
    TermWalk,
    VarBind::*,
    Walk,
};

pub fn unify(heap: &mut QueryHeap, addr1: usize, addr2: usize) -> Option<Substitution> {
    let mut substitution = Substitution::default();
    let mut walk = DualWalk::new(addr1, addr2);
    while let Some((res1, res2)) =
        walk.next_cells_with_addrs_arg_deref(heap, &substitution.arg_regs)
    {
        println!("----------------------------");
        let (addr1, (tag1, value1)) = res1;
        let (addr2, (tag2, value2)) = res2;

        println!("Addr1: {addr1}, ({tag1}, {value1})");
        println!("Addr2: {addr2}, ({tag2}, {value2})");

        if addr2 == 7{
            walk.walk2.print_jump_stack();
        }
        match (tag1, tag2) {
            (Arg, Arg) => {
                if value1 != value2 {
                    todo!("How to handle two args unifiying")
                }
            }
            (Arg, _) => {
                if !bind_arg(heap, &mut substitution, value1, res2, &mut walk.walk2) {
                    return None;
                }
            }
            (_, Arg) => {
                if !bind_arg(heap, &mut substitution, value2, res1, &mut walk.walk1) {
                    return None;
                }
            }
            (Ref, Ref) => {
                if value1 != value2 {
                    heap.bind(value1, Var(value2));
                    substitution.push_bound_var(value1, false);
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
                substitution.push_bound_var(value1, false);
            }
            (_, Ref) => {
                heap.bind(value2, Addr(addr1));
                substitution.push_bound_var(value2, false);
            }
            (Set, Set) if set_equal(heap, addr1, addr2, &mut walk) => continue,
            (Set, Set) => return None,
            (Comp | Tup, Comp | Tup) if heap[addr1] == heap[addr2] => continue,
            (Lis, Lis) => continue,
            (AVar, _) | (_, AVar) => continue,
            _ if heap[addr1].1 == heap[addr2].1 => continue,
            _ => return None,
        }
        println!("----------------------------");
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
    substitution.push_bound_var(var_id, needs_rebuild);
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
        resolution::unification::{unify},
    };

    //-----------------------------------------------------------
    //-------- Comp/Tup Unification ----------------------------
    //-----------------------------------------------------------

    #[test]
    fn equal_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

        //Constant Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Con, a), (Comp, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Ref Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Ref, 0), (Comp, 2), (Con, p), (Ref, 0)];
        heap.var_regs.push(VarReg::UNBOUND);
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Arg Comp
        heap.cells = vec![(Comp, 2), (Con, p), (Arg, 0), (Comp, 2), (Con, p), (Arg, 0)];
        heap.var_regs.clear();
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_tup() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

        //Constant Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Con, a), (Tup, 2), (Con, p), (Con, a)];
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Ref Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Ref, 0), (Tup, 2), (Con, p), (Ref, 0)];
        heap.var_regs.push(VarReg::UNBOUND);
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());

        //Same Arg Comp
        heap.cells = vec![(Tup, 2), (Con, p), (Arg, 0), (Tup, 2), (Con, p), (Arg, 0)];
        heap.var_regs.clear();
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_comp_ref_jump() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

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
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());

        //Ref chain jump
        heap.var_regs = vec![Var(1).into(), Addr(6).into()];
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_comp_arg_jump() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

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
        let sub = unify(&mut heap, 0, 5).unwrap();
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
        let sub = unify(&mut heap, 0, 5).unwrap();
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
        let sub = unify(&mut heap, 0, 5).unwrap();
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
        let sub = unify(&mut heap, 0, 6).unwrap();
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
        let sub = unify(&mut heap, 0, 4).unwrap();
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
        let sub = unify(&mut heap, 0, 4).unwrap();
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
        let sub = unify(&mut heap, 0, 7).unwrap();
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
        let sub = unify(&mut heap, 0, 5).unwrap();
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
        let sub = unify(&mut heap, 0, 8).unwrap();
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
        let sub = unify(&mut heap, 0, 8).unwrap();
        assert_eq!(sub, Substitution::default());
    }

    #[test]
    fn equal_list_with_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
    }

    #[test]
    fn equal_list_with_arg_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
    }

    #[test]
    fn equal_list_with_arg_ref_jump() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);
    }

    #[test]
    fn unify_tail_variables() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);

        //Same arg

        //Same Ref

        //Bind Arg to Ref

        //Bind Ref to Ref

        //Bind Ref through chain
    }

    #[test]
    fn bind_variable_tail() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let mut heap = QueryHeap::new(&[], None);

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
        heap.cells = vec![(Ref, 0), (Ref, 1)];

        //Simplest
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(heap.var_regs[0], Var(1).into());
        assert_eq!(heap.var_regs[1], VarReg::UNBOUND);

        //Through chain on rhs
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[0]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), Var(2).into(), VarReg::UNBOUND]
        );

        //Through chain on lhs
        heap.var_regs = vec![Var(2).into(), VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1).unwrap();
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
        let sub = unify(&mut heap, 0, 1).unwrap();
        assert_eq!(sub.bound_vars.as_slice(), &[2]);
        assert_eq!(
            heap.var_regs,
            [Var(2).into(), Var(3).into(), Var(3).into(), VarReg::UNBOUND]
        );
    }

    #[test]
    fn arg_to_ref() {
        let mut heap = QueryHeap::new(&[], None);

        //Bind arg to ref
        heap.cells = vec![(Arg, 0), (Ref, 0)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1).unwrap();
        assert!(sub.bound_vars.is_empty());
        assert_eq!(sub.get_arg(0).unwrap(), Var(0));

        //Bind arg to ref through chain
        heap.cells = vec![(Arg, 0), (Ref, 0)];
        heap.var_regs = vec![Var(1).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 1).unwrap();
        assert!(sub.bound_vars.is_empty());
        assert_eq!(sub.get_arg(0).unwrap(), Var(1));
    }

    #[test]
    fn unify_ref_through_arg() {
        let mut heap = QueryHeap::new(&[], None);

        // Unify through arg
        heap.cells = vec![(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(0));
        assert_eq!(sub.bound_vars.as_slice(), [0]);
        assert_eq!(heap.var_regs[0], Var(1).into());

        //unify through arg + chain
        heap.cells = vec![(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Ref, 0), (Ref, 1)];
        heap.var_regs = vec![VarReg::UNBOUND, Var(2).into(), VarReg::UNBOUND];
        let sub = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(0));
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
        let sub = unify(&mut heap, 0, 4).unwrap();
        assert_eq!(sub.get_arg(0).unwrap(), Var(0));
        assert_eq!(sub.get_arg(1).unwrap(), Var(1));
        assert_eq!(sub.bound_vars.as_slice(), [0]);
        assert_eq!(heap.var_regs[0], Var(1).into());
    }

    //-----------------------------------------------------------
    //--- Ref & Args (binding to structures) --------------------
    //-----------------------------------------------------------


    #[test]
    fn ref_to_con_comp(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

        heap.cells = vec![(Ref, 0), (Comp, 2), (Con, p), (Con, a)];
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 0, 1).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
        // switch lhs rhs
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 1, 0).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    #[test]
    fn ref_to_con_lis(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

        heap.cells = vec![(Ref, 0), LIS, (Con, p), LIS, (Con, a), EMPTY_LIS];
        heap.var_regs = vec![VarReg::UNBOUND];
        let binding = unify(&mut heap, 0, 1).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(1).into());
    }

    #[test]
    fn ref_to_con_tup_through_ref_jump(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        heap.cells = vec![
            //0: (p,a)
            (Tup, 2),
            (Con, p),
            (Con, a),
            (Ref, 0), // Var(1) -> Addr(0)
            (Ref, 2),
        ];
        heap.var_regs = vec![Var(1).into(), Addr(0).into(), VarReg::UNBOUND];
        let binding = unify(&mut heap, 3, 4).unwrap();
        assert!(binding.bound(2));
        assert!(!binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[2], Addr(0).into());
        // Switch lhs rhs
        heap.var_regs = vec![Var(1).into(), Addr(0).into(), VarReg::UNBOUND];
        let binding = unify(&mut heap, 4, 3).unwrap();
        assert!(binding.bound(2));
        assert!(!binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[2], Addr(0).into());
    }

    #[test]
    fn ref_to_con_tup_through_arg(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);

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
        let binding = unify(&mut heap, 0, 3).unwrap();
        assert!(binding.bound(0));
        assert!(!binding.needs_rebuild[0]);
        assert_eq!(heap.var_regs[0], Addr(4).into());
    }


    #[test]
    fn bind_arg_to_con_comp() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        
    }

    #[test]
    fn bind_arg_to_con_tup() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");
        let mut heap = QueryHeap::new(&[], None);
        
    }

    //-----------------------------------------------------------
    //---------- Occurs checks ----------------------------------
    //-----------------------------------------------------------

    #[test]
    fn arg_occurs() {
        let mut heap = QueryHeap::new(&[], None);
        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: (A, B)
            (Tup, 2),
            (Arg, 0),
            (Arg, 1),
        ];
        assert!(unify(&mut heap, 0, 1).is_none());

        heap.cells = vec![
            // 0: A
            (Arg, 0),
            // 1: (B, C)
            (Tup, 2),
            (Arg, 1),
            (Arg, 2),
        ];
        assert!(unify(&mut heap, 0, 1).is_some());
    }

    #[test]
    fn ref_occurs() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];
        heap.cells = vec![
            // 0: X
            (Ref, 0),
            // 1: (X, Y)
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];
        assert!(unify(&mut heap, 0, 1).is_none());

        heap.cells = vec![
            // 0: X
            (Ref, 0),
            // 1: (Y, Z)
            (Tup, 2),
            (Ref, 1),
            (Ref, 2),
        ];
        assert!(unify(&mut heap, 0, 1).is_some());
    }

    #[test]
    fn arg_occurs_in_bound_ref() {
        let mut heap = QueryHeap::new(&[], None);
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
        assert!(unify(&mut heap, 0, 5).is_none());

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
        assert!(unify(&mut heap, 0, 5).is_some());
    }

    #[test]
    fn ref_occurs_in_bound_arg() {
        let mut heap = QueryHeap::new(&[], None);
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
        assert!(unify(&mut heap, 0, 3).is_none());

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
        assert!(unify(&mut heap, 0, 3).is_some());
    }

    #[test]
    fn occurs_two_args_bound_to_same_var() {
        let mut heap = QueryHeap::new(&[], None);
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
        assert!(unify(&mut heap, 0, 6).is_none());

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
        assert!(unify(&mut heap, 0, 6).is_some());
    }

    #[test]
    fn occurs_arg_bound_to_structure_then_var() {
        let mut heap = QueryHeap::new(&[], None);
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
        assert!(unify(&mut heap, 0, 3).is_none());

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
        assert!(unify(&mut heap, 0, 3).is_some());
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

        assert!(unify(&mut heap, 0, 6).is_none());
    }

    #[test]
    fn ref_occurs_arg_ref_chain() {
        let mut heap = QueryHeap::new(&[], None);
        heap.var_regs = vec![VarReg::UNBOUND, VarReg::UNBOUND, VarReg::UNBOUND];

        heap.cells = vec![
            // 0: (A, B, B)
            (Tup, 3),
            (Arg, 0),
            (Arg, 1),
            (Arg, 2),
            // 6: (X, X, (X,Y))
            (Tup, 3),
            (Ref, 0),
            (Ref, 0),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
        ];

        assert!(unify(&mut heap, 0, 6).is_none());
    }

    //-----------------------------------------------------------
    //-- Complex Combinations and Edge Cases ---
    //-----------------------------------------------------------

    #[test]
    fn case1() {
        //Program Term: p((Arg0,Arg1),(Arg1,Arg0))
        //Goal Term: p(Ref0,Ref0)
        //How to handle unifying different args?
    }
}
