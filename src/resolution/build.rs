use crate::heap::{heap::Heap, store::{Store, Tag}};

pub fn build_goals(body_literals: &[usize], store: &mut Store) -> Box<[usize]> {
    body_literals
        .iter()
        .map(|l| build(*l, store, false))
        .collect::<Box<[usize]>>()
}

pub fn build_clause(clause: &[usize], store: &mut Store) -> Box<[usize]> {
    clause
    .iter()
    .map(|l| build(*l, store, true))
    .collect::<Box<[usize]>>()
}

pub fn build(src_addr: usize, store: &mut Store, clause: bool) -> usize {
    match store[src_addr] {
        (Tag::Lis, _) => {let (pointer, con) = build_list(src_addr, store, clause);
            store.heap_push((Tag::Lis, pointer));
            store.heap_len()-1
        },
        (Tag::Func, _) => build_str(src_addr, store, clause).0,
        _ => {store.print_heap(); panic!("src_addr: {src_addr}, {}", store.term_string(src_addr))}
    }
}

/**This function serves two purposes
 * firstly if a sub term to a structure is itself a structure, we need to pre build this before attempting to build the original strucure with a binding
 * Secondly through this process of potentially building new sub structures we can discover if these are constant sub structures
 * @binding: Binding that informs us how to handle the source term
 * @sub_term: The source term used to build a new term on heap
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
fn build_complex_subterm(
    sub_term: usize,
    store: &mut Store,
    clause: bool,
    update_addr: &mut usize,
) -> bool {
    match store[sub_term] {
        (Tag::ArgA | Tag::Arg, _) => false, //If address points to ref this is not a constant value
        (Tag::Str, func_addr) => {
            let (addr, constant) = build_str(func_addr, store, clause);
            *update_addr = addr;
            constant
        }
        Store::EMPTY_LIS => true,
        (Tag::Lis, _) => {
            let (addr, constant) = build_list(sub_term, store, clause);
            *update_addr = addr;
            constant
        }
        _ => true,
    }
}

/** Used after build subterm, all complex structures have been rebuilt if needed, we can now reconstruct orignal structure using the binding
 * @term_addr: The source term used to build a new term on heap
 * @binding: Binding that informs us how to handle the source term
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
fn build_subterm(sub_term: usize, store: &mut Store, clause: bool, update_addr: usize) {
    match store[sub_term] {
        (Tag::ArgA, arg) if clause => store.heap_push((Tag::Arg, arg)), //We are building a new clause and the cell is universally quantified
        (Tag::Arg | Tag::ArgA, arg) => {
            if store.arg_regs[arg] == usize::MAX {
                store.arg_regs[arg] = store.set_ref(None);
            } else {
                store.heap_push(store[store.arg_regs[arg]]);
            }
        }
        (Tag::Str, _) => store.heap_push((Tag::Str, update_addr)),
        Store::EMPTY_LIS => store.heap_push(Store::EMPTY_LIS),
        (Tag::Lis, _) => store.heap_push((Tag::Lis, update_addr)),
        _ => store.heap_push(store[sub_term]),
    }
}

/**Use a binding and an list address to create a new list, unless source list is constant, then return src address and true
 * @binding: Binding that informs us how to handle the source term
 * @src_lis: The source list used to build a new term on heap
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
fn build_list(src_lis: usize, store: &mut Store, clause: bool) -> (usize, bool) {
    let pointer = store[src_lis].1;
    let mut constant = true;

    let mut update_addrs = [usize::MAX;2];

    for i in 0..=1{
        if !build_complex_subterm(pointer+i, store, clause, &mut update_addrs[i]) {
            constant = false
        }
    }

    if constant {
        return (pointer, true);
    }

    let new_lis = store.heap_len();
    
    for i in 0..=1{
        build_subterm(pointer+i, store, clause, update_addrs[i]) 
    }

    (new_lis, false)
}

/**Use a binding and an str address to create a new list, unless the source structure is constant, then return src address and true
 * @binding: Binding that informs us how to handle the source term
 * @src_str: The source structure used to build a new term on heap
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
pub fn build_str(func_addr: usize, store: &mut Store, clause: bool) -> (usize, bool) {
    let mut constant: bool = true;
    let arity = store[func_addr].1;

    let mut update_addrs: Box<[usize]> = (0..arity).collect();
    //Iterate over structure subterms
    for (i, addr) in store.str_iterator(func_addr).enumerate() {
        if !build_complex_subterm(addr, store, clause, &mut update_addrs[i]) {
            constant = false
        }
    }

    //If all subterms are constant then the structure is constant
    if constant {
        return (func_addr, true);
    }

    let new_str = store.heap_len();
    store.heap_push((Tag::Func, arity));

    for (i, addr) in store.str_iterator(func_addr).enumerate() {
        build_subterm(addr, store, clause, update_addrs[i])
    }

    (new_str, false)
}
