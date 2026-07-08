//! Unification algorithm and substitution management.

use std::{
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    usize,
};

use smallvec::SmallVec;

use crate::heap::{Cell, DualWalk, Heap, Tag};

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

    pub fn push(&mut self, binding: (usize, usize, bool)) {
        self.binding_array[self.binding_len] = binding;
        self.binding_len += 1;
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

    pub fn full_is_deref(&self, mut addr: usize, heap: &impl Heap) -> Option<usize> {
        if heap[addr].0 != Tag::Arg && heap[addr].0 != Tag::Ref{
            return None;
        }
        let first_addr = addr;
        loop {
            match heap[addr] {
                (Tag::Ref, ref_pointer) if addr != ref_pointer => addr = heap.deref_addr(addr),
                (Tag::Ref, _) => match self.bound(addr) {
                    Some(bound_addr) => addr = bound_addr,
                    None => break,
                }
                (Tag::Arg, id) => match self.get_arg(id) {
                    Some(bound_addr) => addr = bound_addr,
                    None => break,
                },
                _ => break,
            }
        }
        if first_addr == addr {
            return None;
        } else {
            return Some(addr);
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
pub fn unify(heap: &impl Heap, addr1: usize, addr2: usize) -> Option<Substitution> {
    unify_walk(heap, addr1, addr2)
}

fn unify_walk(heap: &impl Heap, addr1: usize, addr2: usize) -> Option<Substitution> {
    let mut substitution = Substitution::default();
    let mut walk = DualWalk::new(addr1, addr2);
    loop {
        let Some((mut addr1, mut addr2)) = walk.next_addrs() else{
            return Some(substitution)
        };

        if let Some(deref_addr) = substitution.full_is_deref(addr1, heap) {
            walk.add_deref_frame(deref_addr, true);
            addr1 = deref_addr;
        }
        if let Some(deref_addr) = substitution.full_is_deref(addr2, heap) {
            walk.add_deref_frame(deref_addr, false);
            addr2 = deref_addr;
        }

        println!("addr1: {addr1}, addr2: {addr2}");
        match (heap[addr1].0, heap[addr2].0) {
            (_, Tag::Arg) => unreachable!("unification: Arg cell in non-Arg position — clause args should only appear on the left"),
            (Tag::Arg, _) => {
                //TO DO advance walk past bound term if complex
                println!("set_arg(arg_idx: {}, addr: {addr2})", heap[addr1].1);
                substitution.set_arg(heap[addr1].1, addr2)
            },
            (Tag::Ref, Tag::Lis | Tag::Comp | Tag::Set | Tag::Tup) => {
                if occurs(heap, &substitution, addr1, addr2) {
                    return None;
                } else {
                    substitution.push((addr1, addr2, true))
                }
            }
            (Tag::Lis | Tag::Comp | Tag::Set | Tag::Tup, Tag::Ref) => {
                if occurs(heap, &substitution, addr1, addr2) {
                    return None;
                } else {
                    substitution.push((addr1, addr2, true))
                }
            }
            (Tag::Ref, _) => substitution.push((addr1, addr2, false)),
            (_, Tag::Ref) => substitution.push((addr2, addr1, false)),
            (Tag::Comp|Tag::Tup, Tag::Comp|Tag::Tup) if heap[addr1] == heap[addr2] => {
                walk.increment_cells_left(heap[addr1].1);
            }
            (Tag::Set, Tag::Set) => if set_equal(heap, addr1, addr2){
                continue;
            }else{
                return None;
            },
            (Tag::Lis, Tag::Lis) => walk.increment_cells_left(2),
            (Tag::AVar, _) | (_, Tag::AVar) => continue,
            _ if heap[addr1].1 == heap[addr2].1 => continue,
            _ => return None
            
        }
    }
}

/// Set unification: equality check only.
///
/// Two sets unify iff they have the same length and every element in one has a
/// structurally equal counterpart in the other. No variable bindings are
/// created — this is a deliberate design choice because with two or more
/// unbound variables the lack of element ordering makes correct binding
/// impossible.
fn set_equal(
    heap: &impl Heap,
    addr1: usize,
    addr2: usize,
) -> bool {
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


fn occurs(heap: &impl Heap, binding: &Substitution, ref_addr: usize, complex_addr: usize) -> bool {
    let mut bound_args = SmallVec::<[usize; 2]>::new();
    let mut arg_idx = 0;
    //TODO check this is true, args should appear and be bound in order
    while let Some(mut addr) = binding.get_arg(arg_idx) {
        if let Some(new_addr) = binding.bound(addr) {
            addr = new_addr
        }

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
        heap::{EMPTY_LIS, LIS, QueryHeap, SymbolDB, Tag}, resolution::unification::unify,
    };

    #[test]
    fn arg_to_ref() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let mut binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.arg_regs[0], 1);
        assert_eq!(binding.arg_regs[1..32], [usize::MAX; 31]);

        binding = unify(&heap, 0, 2).unwrap();
        assert_eq!(binding.arg_regs[0], 1);
        assert_eq!(binding.arg_regs[1..32], [usize::MAX; 31]);
        assert_eq!(binding.bound(1), Some(2));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 3;
        binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(4));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 4;
        binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(4));

        binding.binding_array[0] = (0, 0, false);
        binding.binding_len = 0;
        binding.arg_regs[0] = 5;
        binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.bound(1), Some(5));
    }

    #[test]
    fn arg() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.get_arg(0), Some(1));
    }

    #[test]
    fn unify_refs(){
        let heap = vec![
            (Tag::Tup, 2),
            (Tag::Arg, 0),
            (Tag::Arg, 0),
            (Tag::Tup, 2),
            (Tag::Ref, 4),
            (Tag::Ref, 5),
        ];

        let binding = unify(&heap, 0, 3).unwrap();
        assert_eq!(binding.get_arg(0), Some(4));
        assert_eq!(binding.bound(4), Some(5));

        let heap = vec![
            (Tag::Tup, 3),
            (Tag::Arg, 0),
            (Tag::Arg, 1),
            (Tag::Arg, 1),
            (Tag::Tup, 3),
            (Tag::Ref, 6),
            (Tag::Ref, 6),
            (Tag::Ref, 7),
        ];

        let binding = unify(&heap, 0, 4).unwrap();
        assert_eq!(binding.get_arg(0), Some(6));
        assert_eq!(binding.get_arg(1), Some(6));
        assert_eq!(binding.bound(6), Some(7));
    }

    #[test]
    fn bind_ref_through_arg(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let heap = vec![
            (Tag::Tup, 2),
            (Tag::Arg, 0),
            (Tag::Arg, 0),
            (Tag::Tup, 2),
            (Tag::Con, a),
            (Tag::Ref, 5),
        ];

        let binding = unify(&heap, 0, 3).unwrap();
        assert_eq!(binding.get_arg(0), Some(4));
        assert_eq!(binding.bound(5), Some(4));
    }

    #[test]
    fn bind_ref_to_structure(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let heap = vec![
            (Tag::Tup, 1),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Tup, 1),
            (Tag::Ref, 5),
        ];
        let binding = unify(&heap, 0, 4).unwrap();
        assert_eq!(binding.bound(5), Some(1));

        let heap = vec![
            (Tag::Tup, 1),
            LIS,
            (Tag::Con, p),
            LIS,
            (Tag::Con, a),
            EMPTY_LIS,
            (Tag::Tup, 1),
            (Tag::Ref, 7),
        ];
        let binding = unify(&heap, 0, 6).unwrap();
        assert_eq!(binding.bound(7), Some(1));
    }

    #[test]
    fn bind_arg_to_structure(){
        let a = SymbolDB::set_const("a");
        let p = SymbolDB::set_const("p");

        let heap = vec![
            (Tag::Tup, 1),
            (Tag::Arg, 0),
            (Tag::Tup, 1),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];
        let binding = unify(&heap, 0, 2).unwrap();
        assert_eq!(binding.get_arg(0), Some(3));

        let heap = vec![
            (Tag::Tup, 2),
            (Tag::Arg, 0),
            (Tag::Comp, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Tup, 2),
            (Tag::Ref, 7),
            (Tag::Ref, 7),
        ];
        let binding = unify(&heap, 0, 5).unwrap();
        assert_eq!(binding.get_arg(0), Some(4));
        assert_eq!(binding.bound(7), Some(4));
    }

    #[test]
    fn unify_simple_comp() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Arg, 0),
            (Tag::Comp, 3),
            (Tag::Con, p),
            (Tag::Ref, 6),
            (Tag::Con, a),
        ];

        let binding = unify(&heap, 0, 4).unwrap();
        assert_eq!(binding.bound(6), Some(2));
        assert_eq!(binding.get_arg(0), Some(7));
    }

    #[test]
    fn unify_simple_tup() {
        let p = SymbolDB::set_const("p");
        let a = SymbolDB::set_const("a");

        let heap = vec![
            (Tag::Tup, 3),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Arg, 0),
            (Tag::Tup, 3),
            (Tag::Con, p),
            (Tag::Ref, 6),
            (Tag::Con, a),
        ];

        let binding = unify(&heap, 0, 4).unwrap();
        assert_eq!(binding.bound(6), Some(2));
        assert_eq!(binding.get_arg(0), Some(7));
    }

    #[test]
    fn unify_proper_list(){
        let a = SymbolDB::set_const("a");
        let b = SymbolDB::set_const("b");
        let c = SymbolDB::set_const("c");

        let heap = vec![
            LIS,
            (Tag::Con, a),
            LIS,
            (Tag::Arg, 0),
            LIS,
            (Tag::Con, c),
            EMPTY_LIS,
            LIS,
            (Tag::Con, a),
            LIS,
            (Tag::Con, b),
            LIS,
            (Tag::Ref, 12),
            EMPTY_LIS,
        ];

        let binding = unify(&heap, 0, 7).unwrap();
        assert_eq!(binding.bound(12), Some(5));
        assert_eq!(binding.get_arg(0), Some(10));
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

        let heap = vec![
            // clause head: p(Y,(Y,Z))
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 3), // 1   p, Y, (Y,Z)
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Y
            //(Tag::Str, 5),  // 4   -> tuple
            (Tag::Tup, 2), // 5   (Y,Z)
            (Tag::Arg, 0), // 6   Y
            (Tag::Arg, 1), // 7   Z
            // goal: p(X,X)
            //(Tag::Str, 9),  // 8
            (Tag::Comp, 3), // 9   p, X, X
            (Tag::Con, p),  // 10
            (Tag::Ref, 11), // 11  X (canonical, unbound)
            (Tag::Ref, 11), // 12  X
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
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 3), // 1   p, Z, Z
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Z
            (Tag::Arg, 0),  // 4   Z
            // goal: p(X,(X,Y))
            //(Tag::Str, 6),  // 5
            (Tag::Comp, 3), // 6   p, X, (X,Y)
            (Tag::Con, p),  // 7
            (Tag::Ref, 11), // 8   X
            //(Tag::Str, 10), // 9   -> tuple
            (Tag::Tup, 2),  // 10  (X,Y)
            (Tag::Ref, 11), // 11  X (canonical, unbound)
            (Tag::Ref, 12), // 12  Y (canonical, unbound)
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
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 4), // 1   p, Y, Z, (Y,Z)
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Y
            (Tag::Arg, 1),  // 4   Z
            //(Tag::Str, 6),  // 5   -> tuple
            (Tag::Tup, 2), // 6   (Y,Z)
            (Tag::Arg, 0), // 7   Y
            (Tag::Arg, 1), // 8   Z
            // goal: p(X,X,X)
            //(Tag::Str, 10), // 9
            (Tag::Comp, 4), // 10  p, X, X, X
            (Tag::Con, p),  // 11
            (Tag::Ref, 12), // 12  X (canonical, unbound)
            (Tag::Ref, 12), // 13  X
            (Tag::Ref, 12), // 14  X
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
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 3), // 1   p, Z, Z
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Z
            (Tag::Arg, 0),  // 4   Z
            // goal: p((X,Y),X)
            //(Tag::Str, 6),  // 5
            (Tag::Comp, 3), // 6   p, (X,Y), X
            (Tag::Con, p),  // 7
            //(Tag::Str, 10), // 8   -> tuple
            (Tag::Ref, 11), // 9   X
            (Tag::Tup, 2),  // 10  (X,Y)
            (Tag::Ref, 11), // 11  X (canonical, unbound)
            (Tag::Ref, 12), // 12  Y (canonical, unbound)
        ];

        assert_eq!(unify(&heap, 0, 5), None);
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

        let heap = vec![
            // clause head: p(Z, Z, (Z,W))
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 4), // 1   p, Z, Z, (Z,W)
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Z
            (Tag::Arg, 0),  // 4   Z
            //(Tag::Str, 6),  // 5   -> tuple
            (Tag::Tup, 2), // 6   (Z,W)
            (Tag::Arg, 0), // 7   Z
            (Tag::Arg, 1), // 8   W
            // goal: p(X1, X2, X2)
            //(Tag::Str, 10), // 9
            (Tag::Comp, 4), // 10  p, X1, X2, X2
            (Tag::Con, p),  // 11
            (Tag::Ref, 12), // 12  X1 (canonical, unbound)
            (Tag::Ref, 13), // 13  X2 (canonical, unbound)
            (Tag::Ref, 13), // 14  X2
        ];

        assert_eq!(unify(&heap, 0, 9), None);
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

        let heap = vec![
            // clause head: p(Z, (Z,W))
            //(Tag::Str, 1),  // 0
            (Tag::Comp, 3), // 1   p, Z, (Z,W)
            (Tag::Con, p),  // 2
            (Tag::Arg, 0),  // 3   Z
            //(Tag::Str, 5),  // 4   -> tuple
            (Tag::Tup, 2), // 5   (Z,W)
            (Tag::Arg, 0), // 6   Z
            (Tag::Arg, 1), // 7   W
            // goal: p(X,X)
            //(Tag::Str, 9),  // 8
            (Tag::Comp, 3), // 9   p, X, X
            (Tag::Con, p),  // 10
            (Tag::Ref, 11), // 11  X (canonical, unbound)
            (Tag::Ref, 11), // 12  X
        ];

        assert_eq!(unify(&heap, 0, 8), None);
    }
}
