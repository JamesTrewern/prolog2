use super::{PredModule, PredReturn};
use crate::{
    heap::{
        self,
        heap::Heap,
        store::{Cell, Store, Tag},
    },
    interface::state::State,
    program::{clause::{Clause, ClauseType}, clause_table::ClauseTable, dynamic_program::Hypothesis},
    resolution::solver::Proof,
};
use lazy_static::lazy_static;
use std::{
    mem::ManuallyDrop,
    sync::{
        mpsc::{channel, Sender}, Arc, Mutex
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
    state: State,
    main_heap: &Mutex<&mut Store>,
    goal: usize,
    tx: Sender<ClauseTable>,
) {
    let store = Store::new(state.heap.try_read().unwrap());
    // let goal = goal.build_to_heap(&mut store, &mut HashMap::new(), false);
    let mut proof = Proof::new(&[goal], store, Hypothesis::None, None, &state);

    //Iterate over proof tree leaf nodes and collect hypotheses
    while let Some(hypothesis) = proof.next() {
        tx.send(extract_clause_terms(
            &mut main_heap.try_lock().unwrap(),
            &proof.store,
            hypothesis,
        )).unwrap();
    }
}

fn generalise(goals: Box<[usize]>, proof: &mut Proof) -> Vec<ClauseTable> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let main_heap = Mutex::new(&mut proof.store);

    let rx = {
        let (tx, rx) = channel();
        for goal in goals.into_vec() {
            let state = proof.state.clone();
            let tx = tx.clone();
            pool.scope(|_| generalise_thread(state, &main_heap, goal, tx))
        }
        rx
    };

    let mut res = Vec::new();
    while let Ok(h) = rx.recv() {
        res.push(h);
    }
    return res;
}

fn specialise_thread(
    state: State,
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
            &state,
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
            let state = proof.state.clone();
            let tx = tx.clone();
            pool.scope(|_| specialise_thread(state, neg_ex, h, idx, tx))
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
                res.add_clause(Clause {
                    clause_type: ClauseType::HYPOTHESIS,
                    literals: clause.literals.clone(),
                })
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

fn top_prog(call: usize, proof: &mut Proof) -> PredReturn {
    let now = Instant::now();

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

    let pos_ex = collect_examples(call + 2, &proof.store);
    // for (i, ex) in pos_ex.iter().enumerate() {
    //     println!("{i}: {:?}", proof.store.term_string(*ex));
    // }
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

    let neg_ex = collect_examples(call + 3, &proof.store);
    // println!("Neg: {neg_ex:?}");

    let top = specialise(&neg_ex, top, proof);

    println!("Top Program:");
    for c in top.iter() {
        println!("\t{}", c.to_string(&proof.store));
    }
    let elapsed = now.elapsed();
    println!("Time ms: {}", elapsed.as_millis());
    PredReturn::True
}

pub static TOP_PROGRAM: PredModule = &[("learn", 3, top_prog)];
