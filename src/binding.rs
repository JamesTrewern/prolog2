use crate::heap::Heap;

//TO DO consider removing dangling const behaviour, maybe this isn't needed

pub type Binding = Vec<(usize, usize)>;
pub trait BindingTraits {
    fn build_str(
        &mut self,
        str_addr: usize,
        heap: &mut Heap,
        uqvar_binding: &mut Option<Binding>,
    ) -> Option<usize>;
    fn bound(&self, addr: usize) -> Option<usize>;
    fn update_dangling_const(&mut self, dangling_const: usize, con_addr: usize);
    fn undangle_const(&mut self, heap: &mut Heap);
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

    fn update_dangling_const(&mut self, dangling_const: usize, con_addr: usize) {
        for i in 0..self.len() {
            let bind = &mut self[i];
            if bind.1 == dangling_const {
                *bind = (bind.0, con_addr);
            }
        }
    }

    fn undangle_const(&mut self, heap: &mut Heap) {
        let mut mapped: Vec<(usize, usize)> = vec![];
        for i in 0..self.len() {
            let (_, rhs) = &mut self[i];
            if *rhs >= Heap::CON_PTR {
                if !mapped.iter().any(|(id, addr)| rhs == id) {
                    let addr = heap.set_const(*rhs);
                    mapped.push((*rhs, addr));
                    *rhs = addr;
                }
            }
        }
    }

    fn build_str(
        &mut self,
        str_addr: usize,
        heap: &mut Heap,
        uqvar_binding: &mut Option<Binding>,
    ) -> Option<usize> {
        let mut constant: bool = true;
        let arity = heap[str_addr].1;
        for i in 1..=arity{
            match heap[str_addr+1+i] {
                (Heap::REF | Heap::REFA | Heap::REFC, _) => constant = false,
                (Heap::STR, addr) => {
                    if let Some(new_addr) = self.build_str(addr, heap, uqvar_binding) {
                        self.push((addr, new_addr));
                        constant = false;
                    }
                }
                (Heap::LIS, addr) => todo!("Consider list when building goal"),
                _ => (),
            }
        }

        for i in 1..=arity + 1 {
            let arg = str_addr+i;
            let (tag, addr) = &mut heap[arg];
            // if *tag == Heap::REFA{ *tag = Heap::REF}
            match *tag {
                Heap::REFC => {
                    *tag = Heap::REF;
                    match self.bound(*addr) {
                        Some(new_ref) => {
                            if new_ref >= Heap::CON_PTR {
                                *tag = Heap::CON
                            }
                            *addr = new_ref
                        }
                        None => self.push((*addr, arg)),
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
                        match self.bound(*addr) {
                            Some(new_ref) => *addr = new_ref,
                            None => {self.push((*addr, arg)); *addr = arg},
                        }
                    }
                }
                Heap::STR => {
                    if let Some(new_addr) = self.bound(*addr) {
                        *addr = new_addr
                    }
                }
                Heap::LIS => todo!("Consider list"),
                Heap::REF => (),
                _ => panic!("undefined tag or improperly formated heap"),
            }
        }

        Some(str_addr)
    }

    fn to_string(&self, heap: &Heap) -> String {
        let mut buffer = String::from("{");
        for binding in self.iter() {
            buffer += &heap.symbols.get_symbol(binding.0);
            buffer += "/";
            buffer += &heap.symbols.get_symbol(binding.1);
            buffer += ",";
        }
        buffer.pop();
        buffer += "}";
        buffer
    }
}
