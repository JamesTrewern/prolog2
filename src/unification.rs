use crate::heap::Heap;

pub type Binding = Vec<(usize, usize)>;
pub trait BindingTraits {
    fn bound(&self, addr: usize) -> Option<usize>;
    fn to_string(&self, heap: &Heap) -> String;
}

impl BindingTraits for Binding {
    fn bound(&self, addr: usize) -> Option<usize> {
        // println!("{addr}");
        match self.iter().find(|(a1, _)| *a1 == addr) {
            Some((_, a2)) => match self.bound(*a2) {
                Some(a2) => Some(a2),
                None => Some(*a2),
            },
            None => None,
        }
    }



    fn to_string(&self, heap: &Heap) -> String {
        let mut buffer = String::from("{");
        for binding in self.iter() {
            buffer += &heap.term_string(binding.0);
            buffer += "/";
            buffer += &heap.term_string(binding.1);
            buffer += ",";
        }
        buffer.pop();
        buffer += "}";
        buffer
    }
}


fn unify_vars(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    // Create binding between vars
    match binding.bound(addr1) {
        Some(addr1) => unify_rec(addr1, addr2, heap, binding),
        None => {
            binding.push((addr1, addr2));
            true
        }
    }
}

//Unify ref cell with non ref cell
fn unify_ref(ref_addr: usize, non_ref_addr: usize, heap: &Heap, binding: &mut Binding) -> bool {
    match binding.bound(ref_addr) {
        Some(addr1) => {
            if addr1 == non_ref_addr {
                true
            } else {
                unify_rec(addr1, non_ref_addr, heap, binding)
            }
        }
        None => {
            binding.push((ref_addr, non_ref_addr));
            true
        }
    }
}

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

fn unify_list(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    //Check for empty list
    if addr1 == Heap::CON && addr2 == Heap::CON {
        return true;
    } else if addr1 == Heap::CON || addr2 == Heap::CON {
        return false;
    }
    unify_rec(addr1, addr2, heap, binding) && unify_rec(addr1 + 1, addr2 + 1, heap, binding)
}

pub fn unify_rec(addr1: usize, addr2: usize, heap: &Heap, binding: &mut Binding) -> bool {
    let (cell1, cell2) = (heap.get_deref(addr1), heap.get_deref(addr2));

    match (cell1.0, cell2.0) {
        (Heap::REF | Heap::REFC | Heap::REFA, Heap::REF | Heap::REFC | Heap::REFA) => {
            unify_vars(addr1, addr2, heap, binding)
        }
        (Heap::REF | Heap::REFA | Heap::REFC, _) => unify_ref(addr1, addr2, heap, binding),
        (_, Heap::REF | Heap::REFA | Heap::REFC) => unify_ref(addr2, addr1, heap, binding),
        (Heap::STR, Heap::STR) => unify_struct(addr1, addr2, heap, binding),
        (Heap::LIS, Heap::LIS) => unify_list(cell1.1, cell2.1, heap, binding),
        (Heap::CON | Heap::INT | Heap::FLT, Heap::CON | Heap::INT | Heap::FLT) => cell1 == cell2,
        (Heap::CON | Heap::INT | Heap::FLT, _) => panic!("Undefined unifiction behaviour"),
        (_, Heap::CON | Heap::INT | Heap::FLT) => panic!("Undefined unifiction behaviour"),
        _ => panic!("Undefined unifiction behaviour"),
    }
}

pub fn unify(addr1: usize, addr2: usize, heap: &Heap) -> Option<Binding> {
    let mut binding: Binding = vec![];
    if unify_rec(addr1, addr2, heap, &mut binding) {
        Some(binding)
    } else {
        None
    }
}

pub fn build_str_from_binding(
    binding: &mut Binding,
    src_str: usize,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) -> Option<usize> {
    let mut constant: bool = true;
    let arity = heap[src_str].1;
    for i in 1..=arity{
        match heap[src_str+1+i] {
            (Heap::REF | Heap::REFA | Heap::REFC, _) => constant = false,
            (Heap::STR, addr) => {
                if let Some(new_addr) = build_str_from_binding(binding, addr, heap, uqvar_binding) {
                    binding.push((addr, new_addr));
                    constant = false;
                }
            }
            (Heap::LIS, addr) => todo!("Consider list when building goal"),
            _ => (),
        }
    }

    for i in 1..=arity + 1 {
        let arg = src_str+i;
        let (tag, addr) = &mut heap[arg];
        match *tag {
            Heap::REFC => {
                *tag = Heap::REF;
                match binding.bound(*addr) {
                    Some(new_ref) => {
                        if new_ref >= Heap::CON_PTR {
                            *tag = Heap::CON
                        }
                        *addr = new_ref
                    }
                    None => binding.push((*addr, arg)),
                }
            }
            Heap::REFA => {
                if let Some(uqvar_binding) = uqvar_binding {
                    *tag = Heap::REFC;
                    match uqvar_binding.bound(*addr) {
                        Some(new_ref) => {
                            if new_ref >= Heap::CON_PTR {
                                *tag = Heap::CON
                            }
                            *addr = new_ref
                        }
                        None => {
                            uqvar_binding.push((*addr, arg));
                            *addr = arg;
                        }
                    }
                } else {
                    *tag = Heap::REF;
                    match binding.bound(*addr) {
                        Some(new_ref) => *addr = new_ref,
                        None => {binding.push((*addr, arg)); *addr = arg},
                    }
                }
            }
            Heap::REF => {
                if let Some(new_addr) = binding.bound(*addr) {
                    *addr = new_addr
                }
            }
            Heap::LIS => todo!("Consider list"),
            Heap::CON => (),
            _ => panic!("undefined tag or improperly formated heap {tag}"),
        }
    }

    Some(src_str)
}