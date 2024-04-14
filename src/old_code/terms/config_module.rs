use crate::{
    program::{Program, PredModule},
    terms::{
        atoms::AtomHandler, heap::Heap, substitution::SubstitutionHandler, terms::Term
    },
};


pub struct ConfigMod;

impl PredModule for ConfigMod {
    fn build(&self, heap: &mut Heap, prog: &mut Program) {
        prog.add_pred(
            "share_preds",
            1,
            heap,
            Box::new({
                |config, heap, _body_preds, _bindings, atom| {
                    if let Term::Constant(str) = heap.get_term(atom[1]) {
                        match heap.get_string(str) {
                            "true" => {
                                config.share_preds = true;
                                true
                            }
                            "false" => {
                                config.share_preds = false;
                                true
                            }
                            _ => false,
                        }
                    } else {
                        false
                    }
                }
            }),
        );
    
        prog.add_pred(
            "max_clause",
            1,
            heap,
            Box::new({
                |config, heap, _body_preds, _bindings, atom| {
                    if let Term::Number(value) = heap.get_term(atom[1]) {
                        config.max_clause = value as usize;
                        true
                    } else {
                        false
                    }
                }
            }),
        );
    
        prog.add_pred(
            "max_invented",
            1,
            heap,
            Box::new({
                |config, heap, _body_preds, _bindings, atom| {
                    if let Term::Number(value) = heap.get_term(atom[1]) {
                        config.max_invented = value as usize;
                        true
                    } else {
                        false
                    }
                }
            }),
        );
    
        prog.add_pred(
            "body_pred",
            2,
            heap,
            Box::new({
                |_config, heap, body_preds, _bindings, atom| {
                    if let Term::Number(arity) = heap.get_term(atom[2]) {
                        let arity = arity as usize;
                        body_preds.push((atom[1], arity));
                        true
                    } else {
                        false
                    }
                }
            }),
        );
    
        prog.add_pred(
            "heap",
            2,
            heap,
            Box::new({
                |_config, heap, _body_preds, bindings, atom| {
                    println!("SDG  {}", atom.to_string(heap));
                    if let Term::Number(addr) = heap.get_term(atom[1]) {
                        let addr1 = addr as usize;
                        println!("addr1: {addr1}");
                        println!(": {}", heap.term_string(atom[2]));
                        if let Term::REF(addr2) = heap.get_term(atom[2]) {
                            println!("addr2: {addr2}");
                            bindings.insert_sub(addr2, addr1);
                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
            }),
        );
    
        prog.add_pred(
            "heap",
            1,
            heap,
            Box::new({
                |_config, heap, _body_preds, _bindings, atom| {
                    if let Term::Number(addr) = heap.get_term(atom[1]) {
                        let addr = addr as usize;
                        println!("HEAP[{addr}]: {:?}", heap[addr]);
                        true
                    } else {
                        false
                    }
                }
            }),
        );
    }
}

