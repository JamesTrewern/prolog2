use std::collections::HashMap;

use crate::{
    heap::{
        ArgRegs, Heap, QueryHeap,
        VarBind::{Addr, Var},
        VarReg,
    },
    program::clause::BitFlag64,
};

#[derive(Debug, Clone)]
pub struct MetaSub {
    pub meta_clause_id: usize,
    pub subs: Vec<VarReg>,
}

impl MetaSub {
    /// Build MetaSub from argument registers after unification and meta vars bitflags
    pub fn from_arg_regs(arg_regs: &ArgRegs, meta_clause_id: usize, meta_vars: BitFlag64) -> Self {
        let subs = arg_regs
            .into_iter()
            .enumerate()
            .filter_map(|(i, reg)| if meta_vars.get(i) { Some(*reg) } else { None })
            .collect();
        Self {
            meta_clause_id,
            subs,
        }
    }

    /// Shift any subs that are addresses by step
    pub fn shift_addrs(&mut self, step: isize) {
        for sub in &mut self.subs {
            if sub.addr() {
                sub.0 = ((sub.0 as isize) + step).try_into().unwrap();
            }
        }
    }

    pub fn map_vars(&mut self, var_map: HashMap<usize, usize>) {
        todo!()
    }

    pub fn unify(&self, other: &Self, heap: &mut QueryHeap) -> Option<Vec<usize>> {
        let mut binding = Vec::with_capacity(self.subs.len());
        for (msub1, msub2) in self.subs.iter().zip(other.subs.iter()) {
            if *msub1 == *msub2 {
                continue;
            }
            let b1 = if msub1.var() {
                heap.var_deref(msub1.value())
            } else {
                Addr(msub1.value())
            };
            let b2 = if msub2.var() {
                heap.var_deref(msub2.value())
            } else {
                Addr(msub2.value())
            };
            match (b1, b2) {
                (Var(var_id), other) | (other, Var(var_id)) => {
                    binding.push(var_id);
                    heap.bind(var_id, other);
                }
                (Addr(addr1), Addr(addr2)) => {
                    if !heap.term_equal(addr1, addr2) {
                        heap.unbind(&binding);
                        return None;
                    }
                }
            }
        }
        Some(binding)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn meta_sub_unification() {
        // lhs all addr, rhs all var
        // lhs all var, rhs all addr
        // lhs mixed, rhs mixed
        todo!()
    }

    #[test]
    fn meta_sub_unification_chain() {
        // Var set to other var: match var, match addr
        // Var set to addr: match var, match addr
        todo!()
    }
}
