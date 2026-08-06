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
    arg_id: usize,
) {
    match meta_vars {
        Some(bit_flags) if !bit_flags.get(arg_id) => _ = heap.heap_push((Arg, arg_id)),
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
mod tests {}
