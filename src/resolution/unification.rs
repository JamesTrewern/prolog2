//! Unification algorithm and substitution management.

use std::{
    ops::{Deref, DerefMut},
    println, todo, usize,
};

use smallvec::SmallVec;

use crate::heap::{
    Cell, DualWalk, Heap, QueryHeap, SubWalk,
    Tag::*,
    TermWalk,
    VarBind::{self, *},
    VarReg, Walk,
};

/// Substitution mapping clause `Arg` cells to heap addresses.
///
/// Tracks argument register bindings and direct heap-to-heap bindings
/// produced during unification.
#[derive(Debug, PartialEq)]
pub struct Substitution {
    pub(crate) arg_regs: [VarReg; 32],
    pub(crate) bound_vars: SmallVec<[usize; 5]>, // List of bound variables
    pub(crate) needs_rebuild: SmallVec<[bool; 5]>, // Are bound variables bound to complex?
}

impl Deref for Substitution {
    type Target = [usize];
    fn deref(&self) -> &Self::Target {
        &self.bound_vars
    }
}

impl DerefMut for Substitution {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bound_vars
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self {
            arg_regs: [VarReg::UNBOUND; 32],
            bound_vars: SmallVec::new(),
            needs_rebuild: SmallVec::new(),
        }
    }
}

impl Substitution {
    pub fn bound(&self, var_id: usize) -> bool {
        self.bound_vars.contains(&var_id)
    }

    pub fn get_arg(&self, arg_id: usize) -> Option<VarBind> {
        self.arg_regs[arg_id].get_bind()
    }

    pub fn set_arg(&mut self, arg_id: usize, binding: VarBind) {
        self.arg_regs[arg_id].bind(binding);
    }

    pub fn get_bound_vars(self) -> Box<[usize]> {
        self.bound_vars.into_boxed_slice()
    }

    pub fn push_bound_var(&mut self, var_id: usize, needs_rebuild: bool) {
        self.bound_vars.push(var_id);
        self.needs_rebuild.push(needs_rebuild);
    }

    // /// Fully dereference an address through both heap references and substitution bindings.
    // pub(crate) fn full_deref(&self, mut addr: usize, heap: &mut QueryHeap) -> usize {
    //     loop {
    //         match heap[addr] {
    //             (Ref, ref_pointer) if addr != ref_pointer => addr = ref_pointer,
    //             (Ref, _) => match self.bound(addr) {
    //                 Some(bound_addr) => addr = bound_addr,
    //                 None => return addr,
    //             }
    //             (Arg, id) => match self.get_arg(id) {
    //                 Some(bound_addr) => addr = bound_addr,
    //                 None => return addr,
    //             },
    //             _ => return addr,
    //         }
    //     }
    // }

    // pub fn full_is_deref(&self, mut addr: usize, heap: &mut QueryHeap) -> Option<usize> {
    //     if heap[addr].0 != Arg && heap[addr].0 != Ref{
    //         return None;
    //     }
    //     let first_addr = addr;
    //     loop {
    //         match heap[addr] {
    //             (Ref, ref_pointer) if addr != ref_pointer => addr = heap.deref_addr(addr),
    //             (Ref, _) => match self.bound(addr) {
    //                 Some(bound_addr) => addr = bound_addr,
    //                 None => break,
    //             }
    //             (Arg, id) => match self.get_arg(id) {
    //                 Some(bound_addr) => addr = bound_addr,
    //                 None => break,
    //             },
    //             _ => break,
    //         }
    //     }
    //     if first_addr == addr {
    //         return None;
    //     } else {
    //         return Some(addr);
    //     }
    // }

    // /// Check that no two constrained aheapddresses are bound to the same final target.
    // /// This prevents different meta-variables from unifying to the same predicate symbol.
    // ///
    // /// The constraint check traces through BOTH:
    // /// 1. The heap's reference chains (via deref_addr)
    // /// 2. The substitution's pending bindings (via bound)
    // ///
    // /// Compares cell VALUES at dereferenced addresses, not the addresses themselves.
    // /// This ensures that the same constant symbol at different heap locations is
    // /// correctly detected as a duplicate.
    // pub fn check_constraints(&self, constraints: &[usize], heap: &mut QueryHeap) -> bool {
    //     const STACK_CAP: usize = 8;
    //     let len = constraints.len();

    //     if len <= STACK_CAP {
    //         // Stack-allocated path: use MaybeUninit to avoid zeroing unused slots
    //         let mut buf: [MaybeUninit<(usize, Cell)>; STACK_CAP] =
    //             unsafe { MaybeUninit::uninit().assume_init() };
    //         for i in 0..len {
    //             let addr = constraints[i];
    //             let cell = heap[self.full_deref(addr, heap)];
    //             buf[i] = MaybeUninit::new((addr, cell));
    //         }
    //         for i in 0..len {
    //             let (addr_i, cell_i) = unsafe { buf[i].assume_init() };
    //             for j in (i + 1)..len {
    //                 let (addr_j, cell_j) = unsafe { buf[j].assume_init() };
    //                 if addr_i != addr_j && cell_i == cell_j {
    //                     return false;
    //                 }
    //             }
    //         }
    //         true
    //     } else {
    //         // Fallback for very large constraint sets
    //         let targets: Vec<(usize, Cell)> = constraints
    //             .iter()
    //             .map(|&addr| (addr, heap[self.full_deref(addr, heap)]))
    //             .collect();
    //         for i in 0..targets.len() {
    //             for j in (i + 1)..targets.len() {
    //                 if targets[i].0 != targets[j].0 && targets[i].1 == targets[j].1 {
    //                     return false;
    //                 }
    //             }
    //         }
    //         true
    //     }
    // }
}

/// Unify two terms on the heap, returning a substitution on success.
pub fn unify(heap: &mut QueryHeap, addr1: usize, addr2: usize) -> Option<Substitution> {
    unify_walk(heap, addr1, addr2)
}

fn unify_walk(heap: &mut QueryHeap, addr1: usize, addr2: usize) -> Option<Substitution> {
    let mut substitution = Substitution::default();
    let mut walk = DualWalk::new(addr1, addr2);
    while let Some((res1, res2)) =
        walk.next_cells_with_addrs_arg_deref(heap, &substitution.arg_regs)
    {
        println!("----------------------------");
        let (addr1, (tag1, value1)) = res1;
        let (addr2, (tag2, value2)) = res2;

        println!("Addr1: {addr1}, ({tag1}, {value1}");
        println!("Addr2: {addr2}, ({tag2}, {value2}");

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
                heap.bind(value1, Var(value2));
                substitution.push_bound_var(value1, false);
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
            (Set, Set) if set_equal(heap, addr1, addr2) => continue,
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
fn set_equal(heap: &mut QueryHeap, addr1: usize, addr2: usize) -> bool {
    let len_1 = heap[addr1].1;
    let len_2 = heap[addr2].1;
    if len_1 != len_2 {
        return false;
    }

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
    let Some(needs_rebuild) = occurs(heap, &substitution, var_id, walk.sub_walk()) else {
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
            if arg_occurs(heap, arg_id, walk.sub_walk()) {
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
    use std::{assert_eq, vec};

    use super::Substitution;
    use crate::{
        heap::{Heap, QueryHeap, SymbolDB, Tag::*, VarBind::*, VarReg, EMPTY_LIS, LIS},
        resolution::unification::unify,
    };

    #[test]
    fn arg_to_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            (Tup, 2),
            (Ref, 0),
            (Ref, 1),
            (Comp, 2),
            (Con, p),
            (Con, a),
        ]);
        heap.var_regs.push(VarReg::UNBOUND);
        heap.var_regs.push(VarReg::UNBOUND);

        let binding = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(binding.arg_regs[0], Var(0).into());
        assert!(binding.bound(0));
        assert_eq!(heap.var_regs[0], Var(1).into());

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 2),
            (Arg, 0),
            (Arg, 0),
            (Tup, 2),
            (Comp, 2),
            (Con, p),
            (Con, a),
            (Ref, 0),
        ]);
        heap.var_regs.push(VarReg::UNBOUND);

        let binding = unify(&mut heap, 0, 3).unwrap();
        assert!(binding.bound(0));
        assert_eq!(heap.var_regs[0], Addr(4).into());

        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 3),
            (Arg, 0),
            (Arg, 0),
            (Arg, 0),
            (Tup, 3),
            (Comp, 2),
            (Con, p),
            (Con, a),
            (Ref, 0),
            (Ref, 1),
        ]);
        heap.var_regs.push(Var(1).into());
        heap.var_regs.push(VarReg::UNBOUND);

        let binding = unify(&mut heap, 0, 4).unwrap();
        assert!(binding.bound(0));
        assert_eq!(heap.bound(1), Addr(5).into());
    }

    #[test]
    fn arg() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([(Arg, 0), (Comp, 2), (Con, p), (Con, a)]);

        let binding = unify(&mut heap, 0, 1).unwrap();
        assert_eq!(binding.get_arg(0), Some(Addr(1)));
    }

    #[test]
    fn unify_refs() {
        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Ref, 0), (Ref, 5)]);

        let binding = unify(&mut heap, 0, 3).unwrap();
        assert_eq!(binding.get_arg(0), Addr(4).into());
        assert!(binding.bound(4));
        // assert_eq!(heap.bound(4))
        // assert_eq!(binding.bound(4), Some(5));

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 3),
            (Arg, 0),
            (Arg, 1),
            (Arg, 1),
            (Tup, 3),
            (Ref, 6),
            (Ref, 6),
            (Ref, 7),
        ]);

        let binding = unify(&mut heap, 0, 4).unwrap();
        // assert_eq!(binding.get_arg(0), Some(6));
        // assert_eq!(binding.get_arg(1), Some(6));
        // assert_eq!(binding.bound(6), Some(7));
    }

    #[test]
    fn bind_ref_through_arg() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Tup, 2), (Arg, 0), (Arg, 0), (Tup, 2), (Con, a), (Ref, 5)]);

        let binding = unify(&mut heap, 0, 3).unwrap();
        // assert_eq!(binding.get_arg(0), Some(4));
        // assert_eq!(binding.bound(5), Some(4));
    }

    #[test]
    fn bind_ref_to_structure() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Tup, 1), (Comp, 2), (Con, p), (Con, a), (Tup, 1), (Ref, 5)]);
        let binding = unify(&mut heap, 0, 4).unwrap();
        assert_eq!(binding.bound(5), true);
        assert_eq!(heap.var_regs[5], Addr(1).into());

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 1),
            LIS,
            (Con, p),
            LIS,
            (Con, a),
            EMPTY_LIS,
            (Tup, 1),
            (Ref, 7),
        ]);
        let binding = unify(&mut heap, 0, 6).unwrap();
        // assert_eq!(binding.bound(7), Some(1));
    }

    #[test]
    fn bind_arg_to_structure() {
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells
            .extend([(Tup, 1), (Arg, 0), (Tup, 1), (Comp, 2), (Con, p), (Con, a)]);
        let binding = unify(&mut heap, 0, 2).unwrap();
        // assert_eq!(binding.get_arg(0), Some(3));

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 2),
            (Arg, 0),
            (Comp, 2),
            (Con, p),
            (Con, a),
            (Tup, 2),
            (Ref, 7),
            (Ref, 7),
        ]);
        let binding = unify(&mut heap, 0, 5).unwrap();
        // assert_eq!(binding.get_arg(0), Some(4));
        // assert_eq!(binding.bound(7), Some(4));
    }

    #[test]
    fn unify_simple_comp() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Comp, 3),
            (Con, p),
            (Con, a),
            (Arg, 0),
            (Comp, 3),
            (Con, p),
            (Ref, 6),
            (Con, a),
        ]);

        let binding = unify(&mut heap, 0, 4).unwrap();
        // assert_eq!(binding.bound(6), Some(2));
        // assert_eq!(binding.get_arg(0), Some(7));
    }

    #[test]
    fn unify_simple_tup() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            (Tup, 3),
            (Con, p),
            (Con, a),
            (Arg, 0),
            (Tup, 3),
            (Con, p),
            (Ref, 6),
            (Con, a),
        ]);

        let binding = unify(&mut heap, 0, 4).unwrap();
        // assert_eq!(binding.bound(6), Some(2));
        // assert_eq!(binding.get_arg(0), Some(7));
    }

    #[test]
    fn unify_proper_list() {
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            LIS,
            (Con, a),
            LIS,
            (Arg, 0),
            LIS,
            (Con, c),
            EMPTY_LIS,
            LIS,
            (Con, a),
            LIS,
            (Con, b),
            LIS,
            (Ref, 12),
            EMPTY_LIS,
        ]);

        let binding = unify(&mut heap, 0, 7).unwrap();
        // assert_eq!(binding.bound(12), Some(5));
        // assert_eq!(binding.get_arg(0), Some(10));
    }

    // ---------------------------------------------------------------------
    // Occurs-check tests.
    //
    // Each test unifies a clause head (left, with `Arg` clause variables)
    // against a goal (right, with `Ref` goal variables). Every pair is chosen
    // so that successful unification would require an infinite/cyclic term, so
    // a correct occurs check must make `unify` return `None`.
    //
    // The clause head is `addr1` (program term), the goal is `addr2`.
    // ---------------------------------------------------------------------

    /// clause `p(Y,(Y,Z))`  vs  goal `p(X,X)`
    ///
    /// `X = (Y,Z)` and `Y = X`  ⟹  `X = (X,Z)` — cyclic.
    /// Here the cycle is reached *indirectly*: the goal var `X` does not appear
    /// literally inside the tuple, but the clause arg `Y` (bound to `X`) does,
    /// so detection relies on the `bound_args` path in `occurs`.
    #[test]
    fn occurs_arg_bound_to_var_in_tuple() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Y,(Y,Z))
            //(Str, 1),  // 0
            (Comp, 3), // 1   p, Y, (Y,Z)
            (Con, p),  // 2
            (Arg, 0),  // 3   Y
            //(Str, 5),  // 4   -> tuple
            (Tup, 2), // 5   (Y,Z)
            (Arg, 0), // 6   Y
            (Arg, 1), // 7   Z
            // goal: p(X,X)
            //(Str, 9),  // 8
            (Comp, 3), // 9   p, X, X
            (Con, p),  // 10
            (Ref, 11), // 11  X (canonical, unbound)
            (Ref, 11), // 12  X
        ]);

        assert_eq!(unify(&mut heap, 0, 8), None);
    }

    /// clause `p(Z,Z)`  vs  goal `p(X,(X,Y))`
    ///
    /// `Z = X` and `Z = (X,Y)`  ⟹  `X = (X,Y)` — cyclic.
    /// The goal var `X` appears literally inside the tuple, so detection relies
    /// on the direct `Ref` path in `occurs`.
    #[test]
    fn occurs_var_directly_in_tuple() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Z,Z)
            //(Str, 1),  // 0
            (Comp, 3), // 1   p, Z, Z
            (Con, p),  // 2
            (Arg, 0),  // 3   Z
            (Arg, 0),  // 4   Z
            // goal: p(X,(X,Y))
            //(Str, 6),  // 5
            (Comp, 3), // 6   p, X, (X,Y)
            (Con, p),  // 7
            (Ref, 11), // 8   X
            //(Str, 10), // 9   -> tuple
            (Tup, 2),  // 10  (X,Y)
            (Ref, 11), // 11  X (canonical, unbound)
            (Ref, 12), // 12  Y (canonical, unbound)
        ]);

        assert_eq!(unify(&mut heap, 0, 5), None);
    }

    /// clause `p(Y,Z,(Y,Z))`  vs  goal `p(X,X,X)`
    ///
    /// `Y = X`, `Z = X`, `X = (Y,Z)`  ⟹  `X = (X,X)` — cyclic.
    /// Both tuple elements are clause args bound to the same goal var, so
    /// detection again exercises the `bound_args` path (with two bound args).
    #[test]
    fn occurs_two_args_bound_to_same_var() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Y,Z,(Y,Z))
            //(Str, 1),  // 0
            (Comp, 4), // 1   p, Y, Z, (Y,Z)
            (Con, p),  // 2
            (Arg, 0),  // 3   Y
            (Arg, 1),  // 4   Z
            //(Str, 6),  // 5   -> tuple
            (Tup, 2), // 6   (Y,Z)
            (Arg, 0), // 7   Y
            (Arg, 1), // 8   Z
            // goal: p(X,X,X)
            //(Str, 10), // 9
            (Comp, 4), // 10  p, X, X, X
            (Con, p),  // 11
            (Ref, 12), // 12  X (canonical, unbound)
            (Ref, 12), // 13  X
            (Ref, 12), // 14  X
        ]);

        assert_eq!(unify(&mut heap, 0, 9), None);
    }

    /// clause `p(Z,Z)`  vs  goal `p((X,Y),X)`
    ///
    /// `Z = (X,Y)` and `Z = X`  ⟹  `X = (X,Y)` — cyclic.
    /// Here the clause arg `Z` is first bound to the *structure*, then later
    /// unified against the bare goal var `X`, so the occurs check fires from
    /// the `(complex, Ref)` branch with the var appearing directly in the tuple.
    #[test]
    fn occurs_arg_bound_to_structure_then_var() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Z,Z)
            //(Str, 1),  // 0
            (Comp, 3), // 1   p, Z, Z
            (Con, p),  // 2
            (Arg, 0),  // 3   Z
            (Arg, 0),  // 4   Z
            // goal: p((X,Y),X)
            //(Str, 6),  // 5
            (Comp, 3), // 6   p, (X,Y), X
            (Con, p),  // 7
            //(Str, 10), // 8   -> tuple
            (Ref, 11), // 9   X
            (Tup, 2),  // 10  (X,Y)
            (Ref, 11), // 11  X (canonical, unbound)
            (Ref, 12), // 12  Y (canonical, unbound)
        ]);

        assert_eq!(unify(&mut heap, 0, 5), None);
    }

    /// EDGE CASE (hypothesised gap): transitive arg → ref → ref chain.
    ///
    /// clause `p(Z,Z,(Z,W))`  vs  goal `p(X1,X2,X2)`
    ///
    /// Unification order:
    ///   1. `Z = X1`                     (arg_reg[0] = X1)
    ///   2. `Z = X2`  ⟹ `X1 = X2`        (pushes binding X1 → X2)
    ///   3. `(Z,W) = X2`                 (X2 meets the tuple containing Z)
    ///
    /// At step 3 the tuple contains `Z` (Arg 0). `Z` is bound to `X1`, and
    /// `X1` is bound to `X2` — so `Z` transitively *is* `X2`, and binding
    /// `X2 → (Z,W)` closes a cycle (`X2 = (X2,W)`).
    ///
    /// But `occurs` collects `bound_args` by comparing `get_arg(0)` (== X1)
    /// directly against `ref_addr` (== X2). It does not chase `X1 → X2` via
    /// `bound()`, so `Z` is NOT added to `bound_args`, the tuple walk finds an
    /// `Arg` that isn't flagged, and the cycle slips through.
    ///
    /// A correct occurs check should return `None`.
    #[test]
    fn occurs_transitive_arg_ref_chain() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Z, Z, (Z,W))
            //(Str, 1),  // 0
            (Comp, 4), // 1   p, Z, Z, (Z,W)
            (Con, p),  // 2
            (Arg, 0),  // 3   Z
            (Arg, 0),  // 4   Z
            //(Str, 6),  // 5   -> tuple
            (Tup, 2), // 6   (Z,W)
            (Arg, 0), // 7   Z
            (Arg, 1), // 8   W
            // goal: p(X1, X2, X2)
            //(Str, 10), // 9
            (Comp, 4), // 10  p, X1, X2, X2
            (Con, p),  // 11
            (Ref, 12), // 12  X1 (canonical, unbound)
            (Ref, 13), // 13  X2 (canonical, unbound)
            (Ref, 13), // 14  X2
        ]);

        assert_eq!(unify(&mut heap, 0, 9), None);
    }

    /// CONTROL: same shape as the test above but WITHOUT the intermediate
    /// ref → ref hop, so the arg is bound directly to the ref that meets the
    /// structure. This is the case the existing `bound_args` path already
    /// handles, so it must return `None`.
    ///
    /// clause `p(Z,(Z,W))`  vs  goal `p(X,X)` — `Z = X`, then `(Z,W) = X`.
    #[test]
    fn occurs_direct_arg_ref_control() {
        let p = SymbolDB::set_const("p");

        let prog_heap = vec![];
        let mut heap = QueryHeap::new(&prog_heap, None);
        heap.cells.extend([
            // clause head: p(Z, (Z,W))
            //(Str, 1),  // 0
            (Comp, 3), // 1   p, Z, (Z,W)
            (Con, p),  // 2
            (Arg, 0),  // 3   Z
            //(Str, 5),  // 4   -> tuple
            (Tup, 2), // 5   (Z,W)
            (Arg, 0), // 6   Z
            (Arg, 1), // 7   W
            // goal: p(X,X)
            //(Str, 9),  // 8
            (Comp, 3), // 9   p, X, X
            (Con, p),  // 10
            (Ref, 11), // 11  X (canonical, unbound)
            (Ref, 11), // 12  X
        ]);

        assert_eq!(unify(&mut heap, 0, 8), None);
    }
}
