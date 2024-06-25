use crate::{
    heap::{
        store::{Store, Tag},
        symbol_db::SymbolDB,
    },
    interface::{config::Config, state},
    program::program::PROGRAM,
    resolution::solver::Proof,
};
use std::mem;

use super::{get_module, PredModule, PredReturn};

fn body_pred(call: usize, proof: &mut Proof) -> PredReturn {
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
    PROGRAM
        .write()
        .unwrap()
        .add_body_pred(symbol, (arity + 1) as usize, &proof.store);
    PredReturn::True
}

fn max_h_preds(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Int, value) = proof.store[call + 2] {
        Config::set_max_h_pred(value);
        PredReturn::True
    } else {
        PredReturn::False
    }
}

fn max_h_clause(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Int, value) = proof.store[call + 2] {
        Config::set_max_h_clause(value);
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
    Config::set_share_preds(value);
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
    Config::set_debug (value);
    PredReturn::True
}

fn max_depth(call: usize, proof: &mut Proof) -> PredReturn{
    if let (Tag::Int, value) = proof.store[call + 2] {
        Config::set_max_depth(value);
        PredReturn::True
    } else {
        PredReturn::False
    }
}

pub fn load_module(call: usize, proof: &mut Proof) -> PredReturn {
    let name = match proof.store[call + 2] {
        (Tag::Con, _) => proof.store.term_string(call + 2),
        _ => return PredReturn::False,
    };
    match get_module(&name.to_lowercase()) {
        Some(pred_module) => {
            // pred_module.1(self);
            PROGRAM.write().unwrap().add_pred_module(pred_module.0)
        }
        None => println!("{name} is not a recognised module"),
    }
    PredReturn::True
}

pub fn load_file(call: usize, proof: &mut Proof) -> PredReturn {
    if let (Tag::Lis, addr) = proof.store[call] {
        let file_path = SymbolDB::get_symbol(proof.store[addr].1);
        println!("load: {file_path}");
        match state::load_file(&file_path) {
            Ok(_) => PredReturn::True,
            Err(error) => {
                println!("{error}");
                PredReturn::False
            }
        }
    } else {
        let file_path = SymbolDB::get_symbol(proof.store[call + 2].1);
        match state::load_file(&file_path) {
            Ok(_) => PredReturn::True,
            Err(error) => {
                println!("{error}");
                PredReturn::False
            }
        }
    }
}

pub static CONFIG_MOD: PredModule = &[
    ("body_pred", 3, body_pred),
    ("max_h_preds", 2, max_h_preds),
    ("max_h_clause", 2, max_h_clause),
    ("share_preds", 2, share_preds),
    ("debug", 2, debug),
    ("max_depth",2,max_depth),
    ("load_module", 2, load_module),
    ("load_file", 2, load_file),
];
