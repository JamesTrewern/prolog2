use crate::{heap::Heap, program::Clause};

pub type Binding = Vec<(usize, usize)>;
pub trait BindingTraits {
    fn build_atom(&mut self, heap: &Heap, src_literal: usize) -> usize;
    fn build_clause(&mut self, heap: &mut Heap, src_clause: &Clause) -> Clause;
    fn heap_bind(&self, heap: &mut Heap);
    fn build_goal(&mut self, atom_addr: usize, heap: &mut Heap) -> Option<usize>;
    fn bound(&self, addr: usize) -> Option<usize>;
    fn update_dangling_const(&mut self, dangling_const: usize, con_addr: usize);
    fn undangle_const(&mut self, heap: &mut Heap);
    fn to_string(&self, heap: &Heap) -> String;
}

impl BindingTraits for Binding {
    fn bound(&self, addr: usize) -> Option<usize> {
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
            if *rhs >= isize::MAX as usize {
                if !mapped.iter().any(|(id, addr)| rhs == id) {
                    let addr = heap.set_const(*rhs);
                    mapped.push((*rhs, addr));
                    *rhs = addr;
                }
            }
        }
    }

    fn build_goal(&mut self, atom_addr: usize, heap: &mut Heap) -> Option<usize> {
        let mut constant: bool = true;
        let arity = heap[atom_addr].1;
        for arg in atom_addr + 1..atom_addr + 1 + arity {
            match heap[arg] {
                (Heap::REF, _) => constant = false,
                (Heap::STR, addr) => {
                    if let Some(new_addr) = self.build_goal(addr, heap) {
                        self.push((addr, new_addr));
                        constant = false;
                    }
                }
                (Heap::LIS, addr) => todo!(),
                _ => ()
            }
        }
        //TO DO
        //Consider var symbol
        if constant {
            return None;
        }

        let diff = heap.duplicate(atom_addr, arity+1);

        for arg in atom_addr+1 + diff..atom_addr + arity + diff +1 {
            match &mut heap[arg] {
                (Heap::REF,addr) => match self.bound(*addr) {
                    Some(new_ref) => *addr = new_ref,
                    None => self.push((*addr, arg)),
                },
                (Heap::STR,addr) => {
                    if let Some(new_addr) = self.bound(*addr) {
                        *addr = new_addr
                    }
                },
                (Heap::LIS,addr) => (),
                _ => ()
            }
        }

        Some(atom_addr+diff)
    }
    
    //update refs in query space
    fn heap_bind(&self, heap: &mut Heap){
        todo!()
    }

    fn build_clause(&mut self, heap: &mut Heap, src_clause: &Clause) -> Clause{
        // let new_clause:Box<[usize]> = Box::new_uninit_slice(src_clause.len());
        let mut new_clause:Clause = src_clause.clone();
        for i in 0..src_clause.len(){
            new_clause[i] = self.build_atom(heap, src_clause[i])
        }
        new_clause
    }

    fn build_atom(&mut self, heap: &Heap, src_atom: usize) -> usize{
        for arg in src_atom + 1 .. src_atom + 1 + heap[src_atom].1{
            
        }
        todo!()
    }

    fn to_string(&self, heap: &Heap) -> String {
        format!("{{ }}")
    }
}
