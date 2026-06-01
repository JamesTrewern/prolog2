//! Unification algorithm and substitution management.

use std::{
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    usize,
};

use smallvec::SmallVec;

use crate::heap::heap::{Cell, Heap, Tag};

/// Substitution mapping clause `Arg` cells to heap addresses.
///
/// Tracks argument register bindings and direct heap-to-heap bindings
/// produced during unification.
#[derive(Debug, PartialEq)]
pub struct Substitution {
    arg_regs: [usize; 32],
    binding_array: [(usize, usize, bool); 32], //(From, To, ComplexTerm?)
    binding_len: usize,
}

impl Deref for Substitution {
    type Target = [(usize, usize, bool)];
    fn deref(&self) -> &Self::Target {
        &self.binding_array[..self.binding_len]
    }
}

impl DerefMut for Substitution {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.binding_array[..self.binding_len]
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self {
            arg_regs: [usize::MAX; 32],
            binding_array: Default::default(),
            binding_len: Default::default(),
        }
    }
}

impl Substitution {
    pub fn bound(&self, addr: usize) -> Option<usize> {
        // println!("{addr}");
        match self.iter().find(|(a1, _, _)| *a1 == addr) {
            Some((_, a2, _)) => match self.bound(*a2) {
                Some(a2) => Some(a2),
                None => Some(*a2),
            },
            None => None,
        }
    }

    pub fn push(mut self, binding: (usize, usize, bool)) -> Self {
        self.binding_array[self.binding_len] = binding;
        self.binding_len += 1;
        self
    }

    pub fn get_arg(&self, arg_idx: usize) -> Option<usize> {
        if self.arg_regs[arg_idx] == usize::MAX {
            None
        } else {
            Some(self.arg_regs[arg_idx])
        }
    }

    pub fn set_arg(&mut self, arg_idx: usize, addr: usize) {
        self.arg_regs[arg_idx] = addr;
    }

    pub fn get_bindings(&self) -> Box<[(usize, usize)]> {
        let mut bindings = Vec::<(usize, usize)>::with_capacity(self.binding_len);
        for i in 0..self.binding_len {
            bindings.push((self.binding_array[i].0, self.binding_array[i].1));
        }
        bindings.into_boxed_slice()
    }

    /// Fully dereference an address through both heap references and substitution bindings.
    pub(crate) fn full_deref(&self, mut addr: usize, heap: &impl Heap) -> usize {
        loop {
            // First, dereference through the heap
            let heap_deref = heap.deref_addr(addr);

            // Then check if there's a pending binding in the substitution
            match self.bound(heap_deref) {
                Some(bound_to) => {
                    let next = heap.deref_addr(bound_to);
                    if next == heap_deref {
                        return heap_deref;
                    }
                    addr = next;
                }
                None => return heap_deref,
            }
        }
    }

    /// Check that no two constrained addresses are bound to the same final target.
    /// This prevents different meta-variables from unifying to the same predicate symbol.
    ///
    /// The constraint check traces through BOTH:
    /// 1. The heap's reference chains (via deref_addr)
    /// 2. The substitution's pending bindings (via bound)
    ///
    /// Compares cell VALUES at dereferenced addresses, not the addresses themselves.
    /// This ensures that the same constant symbol at different heap locations is
    /// correctly detected as a duplicate.
    pub fn check_constraints(&self, constraints: &[usize], heap: &impl Heap) -> bool {
        const STACK_CAP: usize = 8;
        let len = constraints.len();

        if len <= STACK_CAP {
            // Stack-allocated path: use MaybeUninit to avoid zeroing unused slots
            let mut buf: [MaybeUninit<(usize, Cell)>; STACK_CAP] =
                unsafe { MaybeUninit::uninit().assume_init() };
            for i in 0..len {
                let addr = constraints[i];
                let cell = heap[self.full_deref(addr, heap)];
                buf[i] = MaybeUninit::new((addr, cell));
            }
            for i in 0..len {
                let (addr_i, cell_i) = unsafe { buf[i].assume_init() };
                for j in (i + 1)..len {
                    let (addr_j, cell_j) = unsafe { buf[j].assume_init() };
                    if addr_i != addr_j && cell_i == cell_j {
                        return false;
                    }
                }
            }
            true
        } else {
            // Fallback for very large constraint sets
            let targets: Vec<(usize, Cell)> = constraints
                .iter()
                .map(|&addr| (addr, heap[self.full_deref(addr, heap)]))
                .collect();
            for i in 0..targets.len() {
                for j in (i + 1)..targets.len() {
                    if targets[i].0 != targets[j].0 && targets[i].1 == targets[j].1 {
                        return false;
                    }
                }
            }
            true
        }
    }
}

/// Unify two terms on the heap, returning a substitution on success.
pub fn unify(heap: &impl Heap, addr_1: usize, addr_2: usize) -> Option<Substitution> {
    unify_rec(heap, Substitution::default(), addr_1, addr_2)
}

///Recursive unification function \
///@addr_1: Address of program term \
///@addr_2: Address of goal term
fn unify_rec(
    heap: &impl Heap,
    mut binding: Substitution,
    mut addr_1: usize,
    mut addr_2: usize,
) -> Option<Substitution> {
    addr_1 = heap.deref_addr(addr_1);
    addr_2 = heap.deref_addr(addr_2);
    if heap[addr_1].0 == Tag::Ref {
        if let Some(addr) = binding.bound(addr_1) {
            addr_1 = addr;
        }
    }
    if heap[addr_2].0 == Tag::Ref {
        if let Some(addr) = binding.bound(addr_2) {
            addr_2 = addr;
        }
    }

    if addr_1 == addr_2 {
        return Some(binding);
    }

    match (heap[addr_1].0, heap[addr_2].0) {
        (Tag::AVar, _) | (_,Tag::AVar) | (Tag::ELis, Tag::ELis) => Some(binding),
        (Tag::Str, Tag::Str) => unify_rec(heap, binding, heap[addr_1].1, heap[addr_2].1),
        (_, Tag::Str) => unify_rec(heap, binding, addr_1, heap[addr_2].1),
        (Tag::Str, _) => unify_rec(heap, binding, heap[addr_1].1, addr_2),
        (_, Tag::Arg) => unreachable!("unification: Arg cell in non-Arg position — clause args should only appear on the left"),
        (Tag::Arg, _) => match binding.get_arg(heap[addr_1].1) {
            Some(addr) => unify_rec(heap, binding, addr, addr_2),
            None => {
                binding.set_arg(heap[addr_1].1, addr_2);
                Some(binding)
            }
        },
        (Tag::Ref, Tag::Lis | Tag::Comp | Tag::Set | Tag::Tup) => {
            if occurs(heap, &binding, addr_1, addr_2) {
                None
            } else {
                Some(binding.push((addr_1, addr_2, true)))
            }
        }
        (Tag::Ref, _) => Some(binding.push((addr_1, addr_2, false))),
        (Tag::Lis | Tag::Comp | Tag::Set | Tag::Tup, Tag::Ref) => {
            if occurs(heap, &binding, addr_2, addr_1) {
                None
            } else {
                Some(binding.push((addr_2, addr_1, true)))
            }
        }
        (_, Tag::Ref) => Some(binding.push((addr_2, addr_1, false))),
        (Tag::Con, Tag::Con) | (Tag::Int, Tag::Int) | (Tag::Flt, Tag::Flt)
            if heap[addr_1].1 == heap[addr_2].1 =>
        {
            Some(binding)
        }
        (Tag::Comp, Tag::Comp) | (Tag::Tup, Tag::Tup) => {
            unify_func_or_tup(heap, binding, addr_1, addr_2)
        }
        (Tag::Set, Tag::Set) => unfiy_set(heap, binding, addr_1, addr_2),
        (Tag::Lis, Tag::Lis) => unify_list(heap, binding, addr_1, addr_2),
        _ => None,
    }
}

fn unify_func_or_tup(
    heap: &impl Heap,
    mut binding: Substitution,
    addr_1: usize,
    addr_2: usize,
) -> Option<Substitution> {
    if heap[addr_1].1 != heap[addr_2].1 {
        return None;
    };

    for i in 1..heap[addr_1].1 + 1 {
        binding = unify_rec(heap, binding, addr_1 + i, addr_2 + i)?;
    }

    Some(binding)
}

/// Set unification: equality check only.
///
/// Two sets unify iff they have the same length and every element in one has a
/// structurally equal counterpart in the other. No variable bindings are
/// created — this is a deliberate design choice because with two or more
/// unbound variables the lack of element ordering makes correct binding
/// impossible.
fn unfiy_set(
    heap: &impl Heap,
    binding: Substitution,
    addr_1: usize,
    addr_2: usize,
) -> Option<Substitution> {
    let len_1 = heap[addr_1].1;
    let len_2 = heap[addr_2].1;
    if len_1 != len_2 {
        return None;
    }

    let mut r1 = addr_1 + 1..=addr_1 + len_1;
    let r2 = addr_2 + 1..=addr_2 + len_2;

    // Every element in set1 must match some element in set2.
    if r1.all(|a| r2.clone().any(|b| heap.term_equal(a, b))) {
        Some(binding)
    } else {
        None
    }
}

/**Unfiy two lists together */
fn unify_list(
    heap: &impl Heap,
    mut binding: Substitution,
    addr_1: usize,
    addr_2: usize,
) -> Option<Substitution> {
    // println!("List:({addr_1},{addr_2})");
    let addr_1 = heap[addr_1].1;
    let addr_2 = heap[addr_2].1;
    binding = unify_rec(heap, binding, addr_1, addr_2)?;
    unify_rec(heap, binding, addr_1 + 1, addr_2 + 1)
}

fn occurs(heap: &impl Heap, binding: &Substitution, ref_addr: usize, complex_addr: usize) -> bool {
    let mut bound_args = SmallVec::<[usize; 2]>::new();
    let mut arg_idx = 0;
    //TODO check this is true, args should appear and be bound in order
    while let Some(addr) = binding.get_arg(arg_idx) {
        if addr == ref_addr {
            bound_args.push(arg_idx);
        }
        arg_idx += 1;
    }
    heap.occurs(complex_addr, ref_addr, &bound_args)
}

#[cfg(test)]
mod tests {
    use super::Substitution;
    use crate::{
        heap::{heap::Tag, query_heap::QueryHeap, symbol_db::SymbolDB},
        resolution::unification::{unify, unify_rec},
    };

    #[test]
    fn arg_to_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("p");

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Str, 4),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let mut binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.arg_regs[0], 1);
        assert_eq!(binding.arg_regs[1..32], [usize::MAX; 31]);

        binding = unify_rec(&heap, binding, 0, 2).unwrap();
        assert_eq!(binding.arg_regs[0], 1);
        assert_eq!(binding.arg_regs[1..32], [usize::MAX; 31]);
        assert_eq!(binding.bound(1), Some(2));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 3;
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(4));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 4;
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(4));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 5;
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(5));
    }

    #[test]
    fn arg() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("p");

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Str, 2),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.get_arg(0), Some(2));
    }

    #[test]
    fn binding_chain_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Ref, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Str, 4),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let mut binding = Substitution::default();
        binding = binding.push((1, 2, false));

        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(0), Some(2));

        let mut binding = Substitution::default();
        binding = binding.push((1, 3, false));
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(0), Some(4));

        let mut binding = Substitution::default();
        binding = binding.push((1, 4, false));
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(0), Some(4));

        let mut binding = Substitution::default();
        binding = binding.push((1, 5, false));
        binding = unify_rec(&heap, binding, 0, 1).unwrap();
        assert_eq!(binding.bound(0), Some(5));
    }

    #[test]
    fn func() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Ref, 6),
            (Tag::Lis, 8),
            (Tag::Con, p),
            (Tag::ELis, 0),
        ];

        assert_eq!(unify(&heap, 0, 3), None);
        assert_eq!(unify(&heap, 0, 4), None);
        let binding = unify(&heap, 0, 6).unwrap();
        assert_eq!(binding.bound(6), Some(0));
        assert_eq!(unify(&heap, 0, 7), None);
    }

    #[test]
    fn tup() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Tup, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Ref, 6),
            (Tag::Lis, 8),
            (Tag::Con, p),
            (Tag::ELis, 0),
        ];

        assert_eq!(unify(&heap, 0, 3), None);
        assert_eq!(unify(&heap, 0, 4), None);
        let binding = unify(&heap, 0, 6).unwrap();
        assert_eq!(binding.bound(6), Some(0));
        assert_eq!(unify(&heap, 0, 7), None);
    }

    #[test]
    fn list() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");
        let t = SymbolDB::set_const("t");

        let heap = vec![
            (Tag::Lis, 1),  //0
            (Tag::Con, a),  //1
            (Tag::Lis, 3),  //2
            (Tag::Con, b),  //3
            (Tag::Lis, 5),  //4
            (Tag::Con, c),  //5
            (Tag::ELis, 0), //6
            (Tag::Lis, 8),  //7
            (Tag::Con, a),  //8
            (Tag::Lis, 10), //9
            (Tag::Ref, 10), //10
            (Tag::Lis, 12), //11
            (Tag::Ref, 12), //12
            (Tag::ELis, 0), //13
        ];

        let binding = unify(&heap, 0, 7).unwrap();
        assert_eq!(binding.bound(10), Some(3));
        assert_eq!(binding.bound(12), Some(5));

        let heap = vec![
            (Tag::Lis, 1),  //0
            (Tag::Arg, 0),  //1
            (Tag::Lis, 3),  //2
            (Tag::Arg, 1),  //3
            (Tag::Lis, 5),  //4
            (Tag::Arg, 2),  //5
            (Tag::Con, t),  //6
            (Tag::Lis, 8),  //7
            (Tag::Con, a),  //8
            (Tag::Lis, 10), //9
            (Tag::Con, b),  //10
            (Tag::Lis, 12), //11
            (Tag::Ref, 12), //12
            (Tag::Con, t),  //13
        ];

        let binding = unify(&heap, 0, 7).unwrap();
        assert_eq!(binding.get_arg(0), Some(8));
        assert_eq!(binding.get_arg(1), Some(10));
        assert_eq!(binding.get_arg(2), Some(12));

        let heap = vec![
            (Tag::Lis, 1),  //0
            (Tag::Arg, 0),  //1
            (Tag::Lis, 3),  //2
            (Tag::Arg, 1),  //3
            (Tag::Lis, 5),  //4
            (Tag::Arg, 2),  //5
            (Tag::Arg, 3),  //6
            (Tag::Lis, 8),  //7
            (Tag::Ref, 8),  //8
            (Tag::Lis, 10), //9
            (Tag::Ref, 10), //10
            (Tag::Lis, 12), //11
            (Tag::Ref, 12), //12
            (Tag::Ref, 13), //13
        ];

        let binding = unify(&heap, 0, 7).unwrap();
        assert_eq!(binding.get_arg(0), Some(8));
        assert_eq!(binding.get_arg(1), Some(10));
        assert_eq!(binding.get_arg(2), Some(12));
        assert_eq!(binding.get_arg(3), Some(13));

        let heap = vec![
            (Tag::Comp, 2), //0
            (Tag::Con, p),  //1
            (Tag::Lis, 6),  //2
            (Tag::Comp, 2), //3
            (Tag::Con, p),  //4
            (Tag::Lis, 12), //5
            (Tag::Arg, 0),  //6
            (Tag::Lis, 8),  //7
            (Tag::Arg, 1),  //8
            (Tag::Lis, 10), //9
            (Tag::Arg, 2),  //10
            (Tag::ELis, 0), //11
            (Tag::Ref, 12), //12
            (Tag::Lis, 14), //13
            (Tag::Ref, 14), //14
            (Tag::Lis, 16), //15
            (Tag::Ref, 16), //16
            (Tag::ELis, 0), //17
        ];

        let binding = unify(&heap, 0, 3).unwrap();
        assert_eq!(binding.get_arg(0), Some(12));
        assert_eq!(binding.get_arg(1), Some(14));
        assert_eq!(binding.get_arg(2), Some(16));

        let heap = vec![
            (Tag::Lis, 1),  //0
            (Tag::Lis, 12), //1
            (Tag::Lis, 3),  //2
            (Tag::Lis, 14), //3
            (Tag::Lis, 5),  //4
            (Tag::Lis, 16), //5
            (Tag::ELis, 0), //6
            (Tag::Lis, 8),  //7
            (Tag::Lis, 18), //8
            (Tag::Lis, 10), //9
            (Tag::Lis, 20), //10
            (Tag::Ref, 11), //11
            (Tag::Con, a),  //12
            (Tag::ELis, 0), //13
            (Tag::Arg, 0),  //14
            (Tag::ELis, 0), //15
            (Tag::Con, c),  //16
            (Tag::ELis, 0), //17
            (Tag::Con, a),  //18
            (Tag::ELis, 0), //19
            (Tag::Con, b),  //20
            (Tag::ELis, 0), //21
        ];

        let binding = unify(&heap, 0, 7).unwrap();
        assert_eq!(binding.get_arg(0), Some(20));
        assert_eq!(binding.bound(11), Some(4));
    }

    #[test]
    fn integers() {
        let prev = SymbolDB::set_const("prev".to_string());
        let prog = vec![
            (Tag::Comp, 3),
            (Tag::Con, prev),
            (Tag::Int, 4),
            (Tag::Int, 3),
        ];
        let mut heap = QueryHeap::new(&prog, None);
        //possible failure to deref before comparing numbers
        heap.cells.extend(vec![
            (Tag::Comp, 3),
            (Tag::Ref, 5),
            (Tag::Int, 4),
            (Tag::Ref, 7),
        ]);

        let binding = unify(&heap, 0, 4).unwrap();
        assert_eq!(binding.bound(5), Some(1));
        assert_eq!(binding.bound(7), Some(3));
    }

    // ---------------------------------------------------------------------
    // Occurs-check tests.
    //
    // Each test unifies a clause head (left, with `Arg` clause variables)
    // against a goal (right, with `Ref` goal variables). Every pair is chosen
    // so that successful unification would require an infinite/cyclic term, so
    // a correct occurs check must make `unify` return `None`.
    //
    // The clause head is `addr_1` (program term), the goal is `addr_2`.
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

        let heap = vec![
            // clause head: p(Y,(Y,Z))
            (Tag::Str, 1),   // 0
            (Tag::Comp, 3),  // 1   p, Y, (Y,Z)
            (Tag::Con, p),   // 2
            (Tag::Arg, 0),   // 3   Y
            (Tag::Str, 5),   // 4   -> tuple
            (Tag::Tup, 2),   // 5   (Y,Z)
            (Tag::Arg, 0),   // 6   Y
            (Tag::Arg, 1),   // 7   Z
            // goal: p(X,X)
            (Tag::Str, 9),   // 8
            (Tag::Comp, 3),  // 9   p, X, X
            (Tag::Con, p),   // 10
            (Tag::Ref, 11),  // 11  X (canonical, unbound)
            (Tag::Ref, 11),  // 12  X
        ];

        assert_eq!(unify(&heap, 0, 8), None);
    }

    /// clause `p(Z,Z)`  vs  goal `p(X,(X,Y))`
    ///
    /// `Z = X` and `Z = (X,Y)`  ⟹  `X = (X,Y)` — cyclic.
    /// The goal var `X` appears literally inside the tuple, so detection relies
    /// on the direct `Ref` path in `occurs`.
    #[test]
    fn occurs_var_directly_in_tuple() {
        let p = SymbolDB::set_const("p");

        let heap = vec![
            // clause head: p(Z,Z)
            (Tag::Str, 1),   // 0
            (Tag::Comp, 3),  // 1   p, Z, Z
            (Tag::Con, p),   // 2
            (Tag::Arg, 0),   // 3   Z
            (Tag::Arg, 0),   // 4   Z
            // goal: p(X,(X,Y))
            (Tag::Str, 6),   // 5
            (Tag::Comp, 3),  // 6   p, X, (X,Y)
            (Tag::Con, p),   // 7
            (Tag::Ref, 11),  // 8   X
            (Tag::Str, 10),  // 9   -> tuple
            (Tag::Tup, 2),   // 10  (X,Y)
            (Tag::Ref, 11),  // 11  X (canonical, unbound)
            (Tag::Ref, 12),  // 12  Y (canonical, unbound)
        ];

        assert_eq!(unify(&heap, 0, 5), None);
    }

    /// clause `p(Y,Z,(Y,Z))`  vs  goal `p(X,X,X)`
    ///
    /// `Y = X`, `Z = X`, `X = (Y,Z)`  ⟹  `X = (X,X)` — cyclic.
    /// Both tuple elements are clause args bound to the same goal var, so
    /// detection again exercises the `bound_args` path (with two bound args).
    #[test]
    fn occurs_two_args_bound_to_same_var() {
        let p = SymbolDB::set_const("p");

        let heap = vec![
            // clause head: p(Y,Z,(Y,Z))
            (Tag::Str, 1),   // 0
            (Tag::Comp, 4),  // 1   p, Y, Z, (Y,Z)
            (Tag::Con, p),   // 2
            (Tag::Arg, 0),   // 3   Y
            (Tag::Arg, 1),   // 4   Z
            (Tag::Str, 6),   // 5   -> tuple
            (Tag::Tup, 2),   // 6   (Y,Z)
            (Tag::Arg, 0),   // 7   Y
            (Tag::Arg, 1),   // 8   Z
            // goal: p(X,X,X)
            (Tag::Str, 10),  // 9
            (Tag::Comp, 4),  // 10  p, X, X, X
            (Tag::Con, p),   // 11
            (Tag::Ref, 12),  // 12  X (canonical, unbound)
            (Tag::Ref, 12),  // 13  X
            (Tag::Ref, 12),  // 14  X
        ];

        assert_eq!(unify(&heap, 0, 9), None);
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

        let heap = vec![
            // clause head: p(Z,Z)
            (Tag::Str, 1),   // 0
            (Tag::Comp, 3),  // 1   p, Z, Z
            (Tag::Con, p),   // 2
            (Tag::Arg, 0),   // 3   Z
            (Tag::Arg, 0),   // 4   Z
            // goal: p((X,Y),X)
            (Tag::Str, 6),   // 5
            (Tag::Comp, 3),  // 6   p, (X,Y), X
            (Tag::Con, p),   // 7
            (Tag::Str, 10),  // 8   -> tuple
            (Tag::Ref, 11),  // 9   X
            (Tag::Tup, 2),   // 10  (X,Y)
            (Tag::Ref, 11),  // 11  X (canonical, unbound)
            (Tag::Ref, 12),  // 12  Y (canonical, unbound)
        ];

        assert_eq!(unify(&heap, 0, 5), None);
    }
}
