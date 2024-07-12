use crate::heap::{
    heap::Heap,
    store::{Store, Tag},
};

use super::{build::build, unification::*};

pub fn match_head(
    head: usize,
    goal: usize,
    store: &mut Store,
    arg_regs: &mut [usize; 64],
) -> Option<Binding> {
    let mut binding: Binding = Binding::new();
    let len: usize = store.cells.len();
    if !match_rec(head, goal, store, &mut binding, arg_regs) {
        store.cells.truncate(len);
        None
    } else {
        Some(binding)
    }
}

fn match_rec(
    mut head: usize,
    mut goal: usize,
    store: &mut Store,
    binding: &mut Binding,
    arg_regs: &mut [usize; 64],
) -> bool {
    goal = store.deref_addr(goal);
    head = store.deref_addr(head);
    match (store[head], store[goal]) {
        ((Tag::Arg | Tag::ArgA, arg), _) => set_arg(arg, goal, store, binding, arg_regs),
        ((Tag::Func, _), (Tag::Func, _)) => match_funcs(head, goal, store, binding, arg_regs),
        ((Tag::Str, addr1), (Tag::Str, addr2)) => match_rec(addr1, addr2, store, binding, arg_regs),
        (Store::EMPTY_LIS, Store::EMPTY_LIS) => true,
        (Store::EMPTY_LIS, (Tag::Lis, _)) => false,
        ((Tag::Lis, _), Store::EMPTY_LIS) => false,
        ((Tag::Lis, addr1), (Tag::Lis, addr2)) => {
            match_rec(addr1, addr2, store, binding, arg_regs)
                && match_rec(addr1 + 1, addr2 + 1, store, binding, arg_regs)
        }
        ((Tag::Lis | Tag::Str, _), (Tag::Ref, _)) => {
            binding.push((goal, build(head, store, false, arg_regs)));
            true
        }
        (_, (Tag::Ref, _)) => {
            binding.push((goal, head));
            true
        }
        (c1, c2) => c1 == c2,
    }
}

fn set_arg(
    arg: usize,
    goal: usize,
    store: &mut Store,
    binding: &mut Binding,
    arg_regs: &mut [usize; 64],
) -> bool {
    if arg_regs[arg] == usize::MAX {
        arg_regs[arg] = goal;
        true
    } else {
        unify(arg_regs[arg], goal, store, binding)
    }
}

fn match_funcs(
    head: usize,
    goal: usize,
    store: &mut Store,
    binding: &mut Binding,
    arg_regs: &mut [usize; 64],
) -> bool {
    if store[head].1 != store[goal].1 {
        return false;
    }
    for (ct, gt) in store.str_iterator(head).zip(store.str_iterator(goal)) {
        if !match_rec(ct, gt, store, binding, arg_regs) {
            return false;
        }
    }
    true
}
