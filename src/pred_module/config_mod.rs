use super::{get_module, PredModule, PredReturn};
use crate::{
    heap::{
        heap::Heap,
        store::{self, ListIter, Store, Tag},
        symbol_db::SymbolDB,
    },
    resolution::solver::Proof,
};
use std::mem;

fn body_pred(call: usize, proof: &mut Proof) -> PredReturn {
    unsafe { proof.prog.prog.early_release() };

    let symbol = if let (Tag::Con, symbol) = proof.store[call + 2] {
        symbol
    } else {
        return PredReturn::False;
    };
    let arity: isize = if let (Tag::Int, arity) = &proof.store[call + 3] {
        unsafe { mem::transmute_copy(arity) }
    } else {
        return PredReturn::False;
    };
    proof.state.program.write().unwrap().add_body_pred(
        symbol,
        (arity + 1) as usize,
        &*proof.state.heap.try_read().unwrap(),
    );
    unsafe { proof.prog.prog.reobtain().unwrap() };
    PredReturn::True
}

fn max_h_preds(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Int, value) = proof.store[call + 2] {
        proof.state.config.write().unwrap().max_h_pred = value;
        PredReturn::True
    } else {
        PredReturn::False
    }
}

fn max_h_clause(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Int, value) = proof.store[call + 2] {
        proof.state.config.write().unwrap().max_h_clause = value;
        PredReturn::True
    } else {
        PredReturn::False
    }
}

fn share_preds(call: usize, proof: &mut Proof) -> PredReturn {
    let value = match proof.store[call + 2] {
        Store::TRUE => true,
        Store::FALSE => false,
        _ => {
            println!("Value passed to share_preds wasn't true/false");
            return PredReturn::False;
        }
    };
    proof.state.config.write().unwrap().share_preds = value;
    PredReturn::True
}

fn debug(call: usize, proof: &mut Proof) -> PredReturn {
    let value = match proof.store[call + 2] {
        Store::TRUE => true,
        Store::FALSE => false,
        _ => {
            println!("Value passed to debug wasn't true/false");
            return PredReturn::False;
        }
    };
    proof.state.config.write().unwrap().debug = value;
    PredReturn::True
}

fn max_depth(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Int, value) = proof.store[call + 2] {
        proof.state.config.write().unwrap().max_depth = value;
        PredReturn::True
    } else {
        PredReturn::False
    }
}

pub fn load_module(call: usize, proof: &mut Proof) -> PredReturn {
    unsafe { proof.prog.prog.early_release() };

    let name = match proof.store[call + 2] {
        (Tag::Con, _) => proof.store.term_string(call + 2),
        _ => return PredReturn::False,
    };
    match get_module(&name.to_lowercase()) {
        Some(pred_module) => {
            // pred_module.1(self);
            proof
                .state
                .program
                .try_write()
                .unwrap()
                .add_pred_module(pred_module.0)
        }
        None => println!("{name} is not a recognised module"),
    }

    unsafe { proof.prog.prog.reobtain().unwrap() };
    PredReturn::True
}

pub fn load_file(call: usize, proof: &mut Proof) -> PredReturn {
    unsafe {
        proof.prog.prog.early_release();
        proof.store.prog_cells.early_release()
    };
    let res = if let (Tag::Lis, addr) = proof.store[call] {
        let file_path = SymbolDB::get_symbol(proof.store[addr].1);
        println!("load: {file_path}");
        match proof.state.load_file(&file_path) {
            Ok(_) => PredReturn::True,
            Err(error) => {
                println!("{error}");
                PredReturn::False
            }
        }
    } else {
        let file_path = SymbolDB::get_symbol(proof.store[call + 2].1);
        match proof.state.load_file(&file_path) {
            Ok(_) => PredReturn::True,
            Err(error) => {
                println!("{error}");
                PredReturn::False
            }
        }
    };
    unsafe {
        proof.prog.prog.reobtain().unwrap();
        proof.store.prog_cells.reobtain().unwrap();
    };

    res
}

fn background_knowledge(call: usize, proof: &mut Proof) -> PredReturn {
    unsafe { proof.prog.prog.early_release() };
    let slash = SymbolDB::set_const("/");
    if let (Tag::Lis, _) = proof.store[call + 2] {
        let mut list_iter = ListIter {
            store: &proof.store,
            index: call + 2,
        };
        while let Some(((Tag::Str, pointer), false)) = list_iter.next() {
            if let [(Tag::Func, 3), (Tag::Con, s), (Tag::Con, symbol), (Tag::Int, arity)] =
                proof.store[pointer..pointer + 4]
            {
                if s == slash {
                    proof.state.program.write().unwrap().add_body_pred(
                        symbol,
                        (arity + 1) as usize,
                        &*proof.state.heap.try_read().unwrap(),
                    );
                }
            }
        }
        unsafe { proof.prog.prog.reobtain().unwrap() };
        PredReturn::True
    } else {
        PredReturn::False
    }
}

pub static CONFIG_MOD: PredModule = &[
    ("body_pred", 2, body_pred),
    ("max_h_preds", 1, max_h_preds),
    ("max_h_clause", 1, max_h_clause),
    ("share_preds", 1, share_preds),
    ("debug", 1, debug),
    ("max_depth", 1, max_depth),
    ("load_module", 1, load_module),
    ("load_file", 1, load_file),
    ("background_knowledge", 1, background_knowledge),
];
