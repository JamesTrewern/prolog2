use std::{ops::{Deref, DerefMut}, usize};

use crate::heap::heap::{Heap, Tag, CON_PTR};

#[derive(Debug, PartialEq)]
pub struct Substitution {
    arg_regs: [usize; 32],
    binding_array: [(usize, usize, bool); 32],
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

    pub fn get_bindings(&self) -> Box<[(usize,usize)]>{
        let mut bindings = Vec::<(usize,usize)>::with_capacity(self.binding_len);
        for i in 0..self.binding_len{
            bindings.push((self.binding_array[i].0, self.binding_array[i].1));
        }
        bindings.into_boxed_slice()
    }

    pub fn check_constraints(&self, constraints: &[usize], heap: &impl Heap) -> bool{
        for i in 0..self.binding_len{
            let binding = (self.binding_array[i].0,self.binding_array[i].1);
            if constraints.contains(&heap.deref_addr(binding.0)) && constraints.contains(&heap.deref_addr(binding.1)){
                return false;
            }
        }
        
        true
    }
}

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
        (Tag::Str, Tag::Str) => unify_rec(heap, binding, heap[addr_1].1, heap[addr_2].1),
        (_, Tag::Str) => unify_rec(heap, binding, addr_1, heap[addr_2].1),
        (Tag::Str, _) => unify_rec(heap, binding, heap[addr_1].1, addr_2),
        (_, Tag::Arg) => panic!("Undefined Unification behaviour"),
        (Tag::Arg, _) => match binding.get_arg(heap[addr_1].1) {
            Some(addr) => unify_rec(heap, binding, addr, addr_2),
            None => {
                binding.set_arg(heap[addr_1].1, addr_2);
                Some(binding)
            }
        },
        (Tag::Ref, Tag::Lis | Tag::Func | Tag::Set | Tag::Tup | Tag::Lis) => {
            Some(binding.push((addr_1, addr_2, true)))
        }
        (Tag::Ref, _) => Some(binding.push((addr_1, addr_2, false))),
        (Tag::Lis | Tag::Func | Tag::Set | Tag::Tup | Tag::Lis, Tag::Ref) => {
            Some(binding.push((addr_2, addr_1, true)))
        }
        (_, Tag::Ref) => Some(binding.push((addr_2, addr_1, false))),
        (Tag::Con, Tag::Con) if heap[addr_1].1 == heap[addr_2].1 => Some(binding),
        (Tag::Func, Tag::Func) => unify_func_or_tup(heap, binding, addr_1, addr_2),
        (Tag::Tup, Tag::Tup) => unify_func_or_tup(heap, binding, addr_1, addr_2),
        (Tag::Set, Tag::Set) => unfiy_set(heap, binding, addr_1, addr_2),
        (Tag::Lis, Tag::Lis) => unify_list(heap, binding, addr_1, addr_2),
        (Tag::ELis, Tag::ELis) => Some(binding),
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

fn unfiy_set(
    heap: &impl Heap,
    mut binding: Substitution,
    addr_1: usize,
    addr_2: usize,
) -> Option<Substitution> {
    todo!()
}

/**Unfiy two lists together */
fn unify_list(
    heap: &impl Heap,
    mut binding: Substitution,
    addr_1: usize,
    addr_2: usize,
) -> Option<Substitution> {
    println!("List:({addr_1},{addr_2})");
    let addr_1 = heap[addr_1].1;
    let addr_2 = heap[addr_2].1;
    binding = unify_rec(heap, binding, addr_1, addr_2)?;
    unify_rec(heap, binding, addr_1 + 1, addr_2 + 1)
}

#[cfg(test)]
mod tests {
    use super::Substitution;
    use crate::{
        heap::{
            heap::{Cell, Tag},
            symbol_db::SymbolDB,
        },
        resolution::unification::{unify, unify_rec},
    };

    #[test]
    fn arg_to_ref() {
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("p".into());

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Str, 4),
            (Tag::Func, 2),
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
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("p".into());

        let heap = vec![
            (Tag::Arg, 0),
            (Tag::Str, 2),
            (Tag::Func, 2),
            (Tag::Con, p),
            (Tag::Con, a),
        ];

        let binding = unify(&heap, 0, 1).unwrap();
        assert_eq!(binding.get_arg(0), Some(2));
    }

    #[test]
    fn binding_chain_ref() {
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());

        let mut heap = vec![
            (Tag::Ref, 0),
            (Tag::Ref, 1),
            (Tag::Ref, 2),
            (Tag::Str, 4),
            (Tag::Func, 2),
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
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());

        let heap = vec![
            (Tag::Func, 2),
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
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());

        let heap = vec![
            (Tag::Tup, 2),
            (Tag::Con, p),
            (Tag::Con, a),
            (Tag::Func, 2),
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
    fn set() {
        todo!()
    }

    #[test]
    fn list() {
        let p = SymbolDB::set_const("p".into());
        let a = SymbolDB::set_const("a".into());
        let b = SymbolDB::set_const("b".into());
        let c = SymbolDB::set_const("c".into());
        let t = SymbolDB::set_const("t".into());

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
            (Tag::Func, 2), //0
            (Tag::Con, p),  //1
            (Tag::Lis, 6),  //2
            (Tag::Func, 2), //3
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
}
