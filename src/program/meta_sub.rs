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
    use super::MetaSub;
    use crate::heap::{
        Cell, Heap, QueryHeap, SymbolDB,
        Tag::Con,
        VarBind::{Addr, Var},
        VarReg,
    };

    fn make_addr(heap: &mut QueryHeap, name: &str) -> usize {
        let sym = SymbolDB::set_const(name);
        heap.heap_push((Con, sym))
    }

    fn fresh_meta_sub(meta_clause_id: usize, subs: Vec<VarReg>) -> MetaSub {
        MetaSub {
            meta_clause_id,
            subs,
        }
    }

    #[test]
    fn meta_sub_unification() {
        let prog_heap: Vec<Cell> = vec![];

        // lhs all addr, rhs all var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);

            let lhs = fresh_meta_sub(
                0,
                vec![VarReg::from_addr(addr_p), VarReg::from_addr(addr_q)],
            );
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x), VarReg::from_var(var_y)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("lhs addrs should unify with rhs unbound vars");
            assert_eq!(binding, vec![var_x, var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
            assert_eq!(heap.var_deref(var_y), Addr(addr_q));
        }

        // lhs all var, rhs all addr
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x), VarReg::from_var(var_y)]);
            let rhs = fresh_meta_sub(
                0,
                vec![VarReg::from_addr(addr_p), VarReg::from_addr(addr_q)],
            );

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("lhs unbound vars should unify with rhs addrs");
            assert_eq!(binding, vec![var_x, var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
            assert_eq!(heap.var_deref(var_y), Addr(addr_q));
        }

        // lhs mixed, rhs mixed (also covers the already-equal shared-var fast path)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            let shared = heap.new_var(VarReg::UNBOUND);

            // position 0: lhs addr <-> rhs unbound var
            // position 1: lhs unbound var <-> rhs addr
            // position 2: lhs/rhs share the same unbound var (already equal, no binding needed)
            let lhs = fresh_meta_sub(
                0,
                vec![
                    VarReg::from_addr(addr_p),
                    VarReg::from_var(var_x),
                    VarReg::from_var(shared),
                ],
            );
            let rhs = fresh_meta_sub(
                0,
                vec![
                    VarReg::from_var(var_y),
                    VarReg::from_addr(addr_q),
                    VarReg::from_var(shared),
                ],
            );

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("mixed addr/var positions should unify");
            assert_eq!(binding, vec![var_y, var_x]);
            assert_eq!(heap.var_deref(var_y), Addr(addr_p));
            assert_eq!(heap.var_deref(var_x), Addr(addr_q));
            // Shared var was already equal on both sides, so it's left untouched
            assert_eq!(heap.var_deref(shared), Var(shared));
        }
    }

    #[test]
    fn meta_sub_unification_chain() {
        let prog_heap: Vec<Cell> = vec![];

        // Var set to other var: match var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND); // chain target of var_x, still unbound
            let var_z = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Var(var_y)); // var_x -> var_y

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_z)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to another var should unify with a fresh var");
            // The end of the chain (var_y) is what gets bound, not var_x itself
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_x), Var(var_z));
        }

        // Var set to other var: match addr
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Var(var_y)); // var_x -> var_y

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_addr(addr_p)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to another var should unify with an addr");
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_x), Addr(addr_p));
        }

        // Var set to addr: match var
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p)); // var_x -> addr_p directly

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_var(var_y)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to an addr should unify with a fresh var");
            assert_eq!(binding, vec![var_y]);
            assert_eq!(heap.var_deref(var_y), Addr(addr_p));
        }

        // Var set to addr: match addr (equal addrs -> success, no new bindings)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let var_x = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p));

            let lhs = fresh_meta_sub(0, vec![VarReg::from_var(var_x)]);
            let rhs = fresh_meta_sub(0, vec![VarReg::from_addr(addr_p)]);

            let binding = lhs
                .unify(&rhs, &mut heap)
                .expect("a var chained to an addr should unify with the same addr");
            assert!(binding.is_empty());
        }

        // Var set to addr: match addr (different addrs -> failure, prior bindings unwound)
        {
            let mut heap = QueryHeap::new(&prog_heap, None);
            let addr_p = make_addr(&mut heap, "p");
            let addr_q = make_addr(&mut heap, "q");
            let var_x = heap.new_var(VarReg::UNBOUND);
            let var_y = heap.new_var(VarReg::UNBOUND);
            heap.bind(var_x, Addr(addr_p));

            // position 0 binds var_y to addr_p, position 1 then fails on mismatched
            // addrs, so the position-0 binding should be unwound before returning None.
            let lhs = fresh_meta_sub(
                0,
                vec![VarReg::from_var(var_x), VarReg::from_var(var_x)],
            );
            let rhs = fresh_meta_sub(
                0,
                vec![VarReg::from_var(var_y), VarReg::from_addr(addr_q)],
            );

            assert!(lhs.unify(&rhs, &mut heap).is_none());
            assert_eq!(heap.var_deref(var_y), Var(var_y)); // binding was undone
        }
    }
}
