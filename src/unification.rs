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
    let (addr1, addr2) = (heap.deref(addr1), heap.deref(addr2));
    match (heap[addr1].0, heap[addr2].0) {
        (Heap::REF | Heap::REFC | Heap::REFA, Heap::REF | Heap::REFC | Heap::REFA) => {
            unify_vars(addr1, addr2, heap, binding)
        }
        (Heap::REF | Heap::REFA | Heap::REFC, _) => unify_ref(addr1, addr2, heap, binding),
        (_, Heap::REF | Heap::REFA | Heap::REFC) => unify_ref(addr2, addr1, heap, binding),
        (Heap::STR, Heap::STR) => unify_struct(addr1, addr2, heap, binding),
        (Heap::LIS, Heap::LIS) => unify_list(heap[addr1].1, heap[addr2].1, heap, binding),
        (Heap::CON | Heap::INT | Heap::FLT, Heap::CON | Heap::INT | Heap::FLT) => {
            heap[addr1] == heap[addr2]
        }
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
) -> (usize, bool) {
    let mut constant: bool = true;
    let arity = heap[src_str].1;
    for i in 1..=arity {
        match heap[src_str + 1 + i] {
            (Heap::REF | Heap::REFA | Heap::REFC, addr) => constant = false,
            (Heap::STR_REF, addr) => {
                if let (new_addr, false) =
                    build_str_from_binding(binding, addr, heap, uqvar_binding)
                {
                    binding.push((addr, new_addr));
                    constant = false;
                }
            }
            (Heap::LIS, addr) => todo!("Consider list when building goal"),
            _ => (),
        }
    }

    if constant {
        return (src_str, true);
    }

    let new_str = heap.len();
    heap.push((Heap::STR, arity));

    for i in 1..=arity + 1 {
        match heap[src_str + i] {
            (Heap::REFA, addr) if uqvar_binding.is_some() => {
                let binding = uqvar_binding.as_mut().unwrap();
                if let Some(new_addr) = binding.bound(addr) {
                    heap.push((Heap::REFA, new_addr))
                } else {
                    binding.push((addr, heap.len()));
                    heap.push((Heap::REFC, heap.len()));
                }
            }
            (Heap::REF | Heap::REFC | Heap::REFA, addr) => {
                if let Some(new_addr) = binding.bound(addr) {
                    if heap[new_addr].0 == Heap::CON {
                        heap.push(heap[new_addr])
                    } else {
                        if uqvar_binding.is_some() {
                            heap.push((Heap::REFC, new_addr))
                        } else {
                            heap.push((Heap::REF, new_addr))
                        };
                    }
                } else {
                    binding.push((addr, heap.len()));
                    heap.push((Heap::REFC, heap.len()));
                }
            }
            (Heap::STR_REF, addr) => {
                if let Some(addr) = binding.bound(addr) {
                    heap.push((Heap::STR_REF, addr))
                } else {
                    heap.push((Heap::STR_REF, addr))
                }
            }
            (Heap::LIS, addr) => {
                todo!("Consider list when building")
            }
            (Heap::CON, _) => heap.push(heap[src_str + i]),
            _ => panic!(),
        }
    }

    (new_str, false)
}

fn build_list(
    binding: &mut Binding,
    src_str: usize,
    heap: &mut Heap,
    uqvar_binding: &mut Option<Binding>,
) {

    
}
