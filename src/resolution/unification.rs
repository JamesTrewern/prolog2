use std::ops::Deref;

use crate::heap::heap::{Heap, Tag};

/**Array of pair of memory addresses, binding from left to right  */
#[derive(Debug)]
pub struct Binding(pub Vec<(usize, usize)>);

impl Binding {
    pub fn new() -> Binding {
        Binding(Vec::new())
    }

    /**Is addr bound to some new value. Uses recursion to compute binding chains */
    pub fn bound(&self, addr: usize) -> Option<usize> {
        // println!("{addr}");
        match self.iter().find(|(a1, _)| *a1 == addr) {
            Some((_, a2)) => match self.bound(*a2) {
                Some(a2) => Some(a2),
                None => Some(*a2),
            },
            None => None,
        }
    }

    pub fn to_string(&self, heap: &Heap) -> String {
        let mut buffer = String::from("{");
        for binding in self.iter() {
            if let Some(symbol) = heap.symbols.get_var(binding.0) {
                buffer += symbol;
            } else {
                buffer += &format!("_{}", binding.0);
            }
            buffer += "/";
            if binding.1 < Heap::CON_PTR {
                buffer += &heap.term_string(binding.1)
            } else {
                buffer += heap.symbols.get_const(binding.1)
            };
            buffer += ",";
        }
        buffer.pop();
        buffer += "}";
        buffer
    }

    pub fn push(&mut self, bind: (usize, usize)) {
        self.0.push(bind)
    }
}

impl Deref for Binding {
    type Target = [(usize, usize)];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/**Unify two ref cells */
fn unify_vars(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    // Create binding between vars
    match binding.bound(addr1) {
        //If addr1 is already bound attempt to unfiy it's binding and addr 2
        Some(addr1) => unify_rec(addr1, addr2, heap, binding),
        None => {
            binding.push((addr1, addr2));
            true
        }
    }
}

/**Unify ref cell with non ref cell
 * @ref_addr: heap address to reference cell
 * @non_ref_addr: heap address to a constant or structure cell
 */
fn unify_ref(ref_addr: usize, non_ref_addr: usize, heap: &Heap, binding: &mut Binding) -> bool {
    match binding.bound(ref_addr) {
        Some(addr1) => {
            if addr1 == non_ref_addr {
                true
            } else {
                //if ref_addr is already bound attempt to unify it's binding with non-ref_addr
                unify_rec(addr1, non_ref_addr, heap, binding)
            }
        }
        None => {
            //ref_addr is not bound so create binding from ref_addr to non_ref_addr
            binding.push((ref_addr, non_ref_addr));
            true
        }
    }
}

/**Unify two structures together */
fn unify_struct(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //Arity
    let a1 = heap[addr1].1;
    let a2 = heap[addr2].1;

    //Fail if arity doesn't match
    if a1 != a2 {
        return false;
    }

    //iterate over struct terms including Pred/Func symbol
    for i in 1..=a1 + 1 {
        if !unify_rec(addr1 + i, addr2 + i, heap, binding) {
            return false;
        }
    }

    true
}

/**Unfiy two lists together */
fn unify_list(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //Check for empty list
    if addr1 == Heap::CON_PTR && addr2 == Heap::CON_PTR {
        return true;
    } else if addr1 == Heap::CON_PTR || addr2 == Heap::CON_PTR {
        return false;
    }
    //unify head and tail, if both succeed return true
    unify_rec(addr1, addr2, heap, binding) && unify_rec(addr1 + 1, addr2 + 1, heap, binding)
}

/**Branching point for unification of two cells. Uses tag of each cell to determine how to unify */
fn unify_rec(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //Firstly deref cells
    let (addr1, addr2) = (heap.deref_addr(addr1), heap.deref_addr(addr2));
    //TO DO check at this point if binding already exists as deref cell could have already been considered
    match (heap[addr1].0, heap[addr2].0) {
        (Tag::REF | Tag::REFC | Tag::REFA, Tag::REF | Tag::REFC | Tag::REFA) => {
            unify_vars(addr1, addr2, heap, binding)
        }
        (Tag::REF | Tag::REFA | Tag::REFC, _) => unify_ref(addr1, addr2, heap, binding),
        (_, Tag::REF | Tag::REFA | Tag::REFC) => unify_ref(addr2, addr1, heap, binding),
        (Tag::STR, Tag::STR) => unify_struct(addr1, addr2, heap, binding),
        (Tag::LIS, Tag::LIS) => unify_list(heap[addr1].1, heap[addr2].1, heap, binding),
        (Tag::CON | Tag::INT | Tag::FLT, Tag::CON | Tag::INT | Tag::FLT) => {
            heap[addr1] == heap[addr2]
        }
        (Tag::CON | Tag::INT | Tag::FLT, _) => {
            panic!(
                "Undefined unifiction behaviour {addr1}:{:?}, {addr2}{:?}",
                heap[addr1], heap[addr2]
            )
        }
        (_, Tag::CON | Tag::INT | Tag::FLT) => panic!(
            "Undefined unifiction behaviour {addr1}:{:?}, {addr2}:{:?}",
            heap[addr1], heap[addr2]
        ),
        _ => panic!("Undefined unifiction behaviour"),
    }
}

/** Top function of recursive unify functions. If unification fails return None
 * @addr1: Heap address to the first term, this is normally the head of a clause
 * @addr2: Heap address to second term, normally a goal
*/
pub fn unify(addr1: usize, addr2: usize, heap: &Heap) -> Option<Binding> {
    let mut binding = Binding::new();
    if unify_rec(addr1, addr2, heap, &mut binding) {
        Some(binding)
    } else {
        None
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
fn build_subterm(
    binding: &mut Binding,
    sub_term: usize,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) -> bool {
    let addr = heap.deref_addr(sub_term);
    match heap[addr] {
        (Tag::REF | Tag::REFA | Tag::REFC, _) => return false, //If address points to ref this is not a constant value
        (Tag::STR, _) => {
            if let (new_addr, false) = build_str(binding, addr, heap, uqvar_binding) {
                //If we need to create a new structure add it to the binding, and return false as this is not constant
                binding.push((addr, new_addr));
                return false;
            }
        }

        (Tag::LIS, _) => {
            if let (new_addr, false) = build_list(binding, sub_term, heap, uqvar_binding) {
                //The source list was not constant
                binding.push((sub_term, new_addr)); // This maps from the address containg the list tag to the address of the first element in the new list
                return false;
            } else {
                println!("const list")
            }
        }
        _ => (),
    }
    true
}

/** Used after build subterm, all complex structures have been rebuilt if needed, we can now reconstruct orignal structure using the binding
 * @term_addr: The source term used to build a new term on heap
 * @binding: Binding that informs us how to handle the source term
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
fn add_term_binding(
    term_addr: usize,
    binding: &mut Binding,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) {
    let addr = heap.deref_addr(term_addr);
    match heap[addr] {
        (Tag::REFA, addr) if uqvar_binding.is_some() => {
            //We are building a new clause and the cell is universally quantified
            let binding = uqvar_binding.as_mut().unwrap();
            if let Some(new_addr) = binding.bound(addr) {
                heap.push((Tag::REFC, new_addr))
            } else {
                //This is the first intance of the var in the new clause so we add bind to update other instances to this address
                binding.push((addr, heap.len()));
                heap.push((Tag::REFC, heap.len()));
            }
        }
        (Tag::REF | Tag::REFC | Tag::REFA, addr) => {
            //Non UQ var or we are building goal
            if let Some(new_addr) = binding.bound(addr) {
                if heap[new_addr].0 == Tag::CON {
                    heap.push(heap[new_addr])
                } else {
                    heap.push((Tag::REF, new_addr))
                }
            } else {
                //This is the first intance of the var in the new clause so we add bind to update other instances to this address
                binding.push((addr, heap.len()));
                heap.push((Tag::REF, heap.len()));
            }
        }
        (Tag::STR, _) => {
            //If the structure had vars it will be in binding, otherwise we can refernce the same constant structure
            if let Some(addr) = binding.bound(addr) {
                heap.push((Tag::StrRef, addr))
            } else {
                heap.push((Tag::StrRef, addr))
            }
        }
        (Tag::LIS, addr) => {
            //If the list had vars it will be in binding, otherwise we can reference the same constant list
            if let Some(new_addr) = binding.bound(term_addr) {
                heap.push((Tag::LIS, new_addr))
            } else {
                heap.push((Tag::LIS, addr))
            }
        }
        (Tag::CON, _) => heap.push(heap[term_addr]),
        _ => panic!(),
    }
}

/**Use a binding and an list address to create a new list, unless source list is constant, then return src address and true
 * @binding: Binding that informs us how to handle the source term
 * @src_lis: The source list used to build a new term on heap
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
fn build_list(
    binding: &mut Binding,
    src_lis: usize,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) -> (usize, bool) {
    let mut addr = src_lis;
    let mut constant = true;

    //Iterate over all list elements
    loop {
        match heap[addr] {
            Heap::EMPTY_LIS => break,
            (Tag::LIS, list_ptr) => {
                addr = list_ptr + 1;
                if !build_subterm(binding, list_ptr, heap, uqvar_binding) {
                    constant = false
                }
            }
            _ => {
                if !build_subterm(binding, addr, heap, uqvar_binding) {
                    constant = false;
                }
                break;
            }
        }
    }

    if constant {
        return (src_lis, true);
    }

    let new_lis = heap.len();
    addr = src_lis;

    //Build elements in the new list
    loop {
        println!("{addr} -> {}", heap.len());
        match heap[addr] {
            Heap::EMPTY_LIS => {
                heap.push(Heap::EMPTY_LIS);
                break;
            }
            (Tag::LIS, list_ptr) => {
                add_term_binding(list_ptr, binding, heap, uqvar_binding);
                heap.push((Tag::LIS, heap.len() + 1));
                addr = list_ptr + 1;
            }
            _ => {
                add_term_binding(heap.deref_addr(addr), binding, heap, uqvar_binding);
                break;
            }
        }
    }

    (new_lis, false)
}

/**Use a binding and an str address to create a new list, unless the source structure is constant, then return src address and true
 * @binding: Binding that informs us how to handle the source term
 * @src_str: The source structure used to build a new term on heap
 * @heap: The heap
 * @uqvar_binding: Optional value that tracks the first instance of a uq var when it is added. If None we are building goal
 */
pub fn build_str(
    binding: &mut Binding,
    src_str: usize,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) -> (usize, bool) {
    let mut constant: bool = true;
    let arity = heap[src_str].1;

    //Iterate over structure subterms
    for addr in heap.str_iterator(src_str) {
        if !build_subterm(binding, addr, heap, uqvar_binding) {
            constant = false
        }
    }

    //If all subterms are constant then the structure is constant
    if constant {
        return (src_str, true);
    }

    let new_str = heap.len();
    heap.push((Tag::STR, arity));

    //Build new structure with bindings
    for addr in heap.str_iterator(src_str) {
        add_term_binding(addr, binding, heap, uqvar_binding)
    }

    (new_str, false)
}
