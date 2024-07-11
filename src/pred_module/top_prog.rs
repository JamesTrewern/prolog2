use super::{PredModule, PredReturn};
use crate::{
    heap::{
        self,
        heap::Heap,
        store::{Cell, Store, Tag},
        symbol_db::SymbolDB,
    },
    interface::state::State,
    program::{
        clause::{Clause, ClauseType},
        clause_table::ClauseTable,
        dynamic_program::Hypothesis,
        program::Predicate,
    },
    resolution::solver::Proof,
};
use lazy_static::lazy_static;
use std::{
    mem::ManuallyDrop,
    sync::{
        mpsc::{channel, Sender},
        Mutex,
    },
    time::Instant,
};

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

fn extract_clause_terms(
    main_heap: &mut Store,
    sub_heap: &Store,
    hypothesis: ClauseTable,
) -> ClauseTable {
    let mut newh = ClauseTable::new();
    for c in hypothesis.iter() {
        {
            let new_literals: Box<[usize]> = c
                .iter()
                .map(|l| main_heap.copy_term(sub_heap, *l))
                .collect();

            // main_heap.print_heap();
            let new_c = Clause {
                clause_type: c.clause_type,
                literals: ManuallyDrop::new(new_literals),
            };

            newh.add_clause(new_c);
        }
    }
    newh
}

fn generalise_thread(
    state: &State,
    main_heap: &Mutex<&mut Store>,
    top_prog: &Mutex<Vec<ClauseTable>>,
    goal: usize,
    tx: Sender<bool>,
) {
    let store = Store::new(state.heap.read().unwrap());
    let mut proof = Proof::new(&[goal], store, Hypothesis::None, None, &state);
    //Iterate over proof tree leaf nodes and collect hypotheses
    while let Some(hypothesis) = proof.next() {
        let mut main_heap = main_heap.lock().unwrap();
        let mut top_prog = top_prog.lock().unwrap();
        let hypothesis = extract_clause_terms(*main_heap, &proof.store, hypothesis);
        if !top_prog.iter().any(|h2| hypothesis.equal(h2, *main_heap)) {
            top_prog.push(hypothesis);
        }
    }
    tx.send(true).unwrap();
}

fn generalise(goals: Box<[usize]>, proof: &mut Proof) -> Vec<ClauseTable> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let main_heap = Mutex::new(&mut proof.store);
    let top_prog: Mutex<Vec<ClauseTable>> = Mutex::new(Vec::new());

    let rx = {
        let (tx, rx) = channel();
        for goal in goals.into_vec() {
            pool.scope(|_| generalise_thread(&proof.state, &main_heap, &top_prog, goal, tx.clone()))
        }
        rx
    };

    while let Ok(true) = rx.recv() {}
    return top_prog.into_inner().unwrap();
}

fn specialise_thread(
    state: &State,
    neg_ex: &[usize],
    hypothesis: &ClauseTable,
    idx: usize,
    tx: Sender<(usize, bool)>,
) {
    let store = Store::new(state.heap.try_read().unwrap());

    let mut config = *state.config.read().unwrap();
    config.learn = false;

    for goal in neg_ex.iter() {
        let store = store.clone();
        if Proof::new(
            &[*goal],
            store,
            Hypothesis::Static(hypothesis),
            Some(config),
            state,
        )
        .next()
        .is_some()
        {
            tx.send((idx, false)).unwrap();
            return;
        }
    }
    tx.send((idx, true)).unwrap();
}

fn specialise(neg_ex: &[usize], hypotheses: Vec<ClauseTable>, proof: &Proof) -> ClauseTable {
    let n_jobs = hypotheses.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let rx = {
        let (tx, rx) = channel();
        for (idx, h) in hypotheses.iter().enumerate() {
            pool.scope(|_| specialise_thread(&proof.state, neg_ex, h, idx, tx.clone()))
        }
        rx
    };

    let mut retain = vec![true; hypotheses.len()].into_boxed_slice();
    while let Ok((idx, keep)) = rx.recv() {
        retain[idx] = keep;
    }

    let mut res = ClauseTable::new();

    //Check for duplicate clauses before adding
    for i in 0..hypotheses.len() {
        if retain[i] {
            for clause in hypotheses[i].iter() {
                if !res.contains(&clause, &proof.store) {
                    res.add_clause(Clause {
                        clause_type: ClauseType::HYPOTHESIS,
                        literals: clause.literals.clone(),
                    })
                }
            }
        }
    }

    return res;
}

fn collect_examples(mut addr: usize, store: &Store) -> Box<[usize]> {
    let mut examples = Vec::new();
    addr = store.deref_addr(addr);
    loop {
        match store[addr] {
            Store::EMPTY_LIS => return examples.into_boxed_slice(),
            (Tag::Lis, pointer) => {
                addr = pointer + 1;
                if let (Tag::Str, p) = store[pointer] {
                    examples.push(p)
                } else {
                    examples.push(pointer)
                }
            }
            _ => panic!("Examples incorrectly formatted"),
        }
    }
}

fn top_prog(pos_ex: Box<[usize]>, neg_ex: Box<[usize]>, proof: &mut Proof) -> PredReturn {
    let now = Instant::now();

    let top = generalise(pos_ex, proof);

    // for (i, h) in top.iter().enumerate() {
    //     println!("Hypothesis [{i}]");
    //     for c in h.iter() {
    //         println!("\t{}", c.to_string(&proof.store))
    //     }
    // }
    //Drain current heap to static heap.
    unsafe {
        proof.store.prog_cells.early_release();
    }
    proof
        .state
        .heap
        .write()
        .unwrap()
        .append(&mut proof.store.cells);
    unsafe {
        proof.store.prog_cells.reobtain();
    }

    let top = specialise(&neg_ex, top, proof);

    println!("Top Program:");
    let mut i = 0;
    for c in top.iter() {
        i += 1;
        println!("\t{}", c.to_string(&proof.store));
    }

    println!("{i}");
    let elapsed = now.elapsed();
    println!("Time ms: {}", elapsed.as_millis());
    PredReturn::True
}

fn top_prog_no_id(call: usize, proof: &mut Proof) -> PredReturn {
    let pos_ex = if let Some(Predicate::Clauses(clauses)) = proof
        .prog
        .prog
        .predicates
        .get(&(SymbolDB::set_const("pos_examples"), 2))
    {
        let examples_list = proof.prog.get(clauses.clone().next().unwrap())[0] + 2;
        collect_examples(examples_list, &proof.store)
    } else {
        return PredReturn::False;
    };

    let neg_ex = if let Some(Predicate::Clauses(clauses)) = proof
        .prog
        .prog
        .predicates
        .get(&(SymbolDB::set_const("neg_examples"), 2))
    {
        let examples_list = proof.prog.get(clauses.clone().next().unwrap())[0] + 2;
        collect_examples(examples_list, &proof.store)
    } else {
        [].into()
    };
    top_prog(pos_ex, neg_ex, proof)
}

fn top_prog_id(call: usize, proof: &mut Proof) -> PredReturn {
    println!("{}",proof.store.term_string(call));
    let id = if let (Tag::Con, id) = proof.store[call + 2] {
        id
    } else {
        return PredReturn::False;
    };

    let pos_ex = if let Some(Predicate::Clauses(clauses)) = proof
        .prog
        .prog
        .predicates
        .get(&(SymbolDB::set_const("pos_examples"), 3))
    {
        match clauses
            .clone()
            .map(|c| proof.prog.get(c))
            .find(|clause| proof.store[clause[0] + 2] == (Tag::Con, id))
        {
            Some(clause) => collect_examples(clause[0] + 3, &proof.store),
            None => return PredReturn::False,
        }
    } else {
        return PredReturn::False;
    };

    let neg_ex = if let Some(Predicate::Clauses(clauses)) = proof
        .prog
        .prog
        .predicates
        .get(&(SymbolDB::set_const("neg_examples"), 3))
    {
        match clauses
            .clone()
            .map(|c| proof.prog.get(c))
            .find(|clause| proof.store[clause[0] + 2] == (Tag::Con, id))
        {
            Some(clause) => collect_examples(clause[0] + 3, &proof.store),
            None => return PredReturn::False,
        }
    } else {
        return PredReturn::False;
    };

    top_prog(pos_ex, neg_ex, proof)
}
pub static TOP_PROGRAM: PredModule = &[("learn", 1, top_prog_no_id), ("learn", 2, top_prog_id)];
