use super::{PredModule, PredReturn};
use crate::{
    heap::{
        self,
        heap::Heap,
        store::{Cell, Store, Tag},
    },
    interface::state::State,
    pred_module::top_prog,
    program::{
        clause::{Clause, ClauseType},
        clause_table::ClauseTable,
        dynamic_program::Hypothesis,
    },
    resolution::solver::Proof,
};
use lazy_static::lazy_static;
use std::{
    mem::ManuallyDrop,
    sync::{
        mpsc::{channel, Sender},
        Arc, Mutex, MutexGuard,
    },
    time::Instant,
};

lazy_static! {
    static ref CPU_COUNT: usize = num_cpus::get();
}

fn extract_h_terms(
    src_heap: &Store,
    hypothesis: ClauseTable,
    other_heap: &mut impl Heap,
) -> ClauseTable {
    let mut new_hypothesis = ClauseTable::new();
    for c in hypothesis.iter() {
        {
            let new_literals: Box<[usize]> = c
                .iter()
                .map(|l| other_heap.copy_term(src_heap, *l))
                .collect();
            new_hypothesis.add_clause(Clause {
                clause_type: c.clause_type,
                literals: ManuallyDrop::new(new_literals),
            });
        }
    }
    new_hypothesis
}

fn generalise_example2(
    state: State,
    main_heap: &Mutex<&mut Store>,
    top_prog: &Mutex<Vec<ClauseTable>>,
    goal: usize,
    tx: Sender<bool>,
) {
    let store = Store::new(state.heap.try_read().unwrap());
    let mut proof = Proof::new(&[goal], store, Hypothesis::None, None, &state);
    //Iterate over proof tree leaf nodes and collect hypotheses
    while let Some(hypothesis) = proof.next() {
        let mut top_prog = top_prog.lock().unwrap();
        let mut other_heap = main_heap.lock().unwrap();

        //If hypothesis does not equal another hypothesis, add it to the top program and duplicate cells to main heap
        if top_prog
            .iter()
            .all(|h| !hypothesis.equal(h, &proof.store, *other_heap))
        {
            top_prog.push(extract_h_terms(&proof.store, hypothesis, *other_heap))
        }
    }
    tx.send(true).unwrap()
}

fn generalise_example(state: State, goal: usize, tx: Sender<(Vec<Cell>, Vec<ClauseTable>)>) {
    let store = Store::new(state.heap.try_read().unwrap());
    let mut proof = Proof::new(&[goal], store, Hypothesis::None, None, &state);
    //Iterate over proof tree leaf nodes and collect hypotheses
    let mut h_cells: Vec<Cell> = Vec::new();
    let mut hypotheses = Vec::<ClauseTable>::with_capacity(5);
    while let Some(hypothesis) = proof.next() {
        if hypotheses
            .iter()
            .all(|h| !h.equal(&hypothesis, &h_cells, &proof.store))
        {
            hypotheses.push(extract_h_terms(&proof.store, hypothesis, &mut h_cells))
        }
    }
    tx.send((h_cells, hypotheses)).unwrap()
}

fn generalise(goals: Box<[usize]>, proof: &mut Proof) -> (Vec<ClauseTable>) {
    let n_jobs = goals.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let rx = {
        let (tx, rx) = channel();
        for goal in goals.into_vec() {
            let state = proof.state.clone();
            let tx = tx.clone();
            pool.scope(|_| generalise_example(state, goal, tx))
        }
        rx
    };

    let top_prog = Vec::<ClauseTable>::with_capacity(n_jobs);
    for (mut h_cells, hypotheses) in rx.iter().take(n_jobs) {
        let offset = proof.store.heap_len();

        for mut h1 in hypotheses.into_iter().filter(|h1| {
            top_prog
                .iter()
                .all(|h2| !h1.equal(h2, &h_cells, &proof.store))
        }) {
            h1.add_offset(offset)
        }

        proof.store.cells.append(&mut h_cells);
    }
    println!("After colect H");
    top_prog
}

fn specialise_thread(
    state: State,
    neg_ex: Arc<[usize]>,
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

fn specialise(neg_ex: Arc<[usize]>, hypotheses: Vec<ClauseTable>, proof: &Proof) -> ClauseTable {
    let n_jobs = hypotheses.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let rx = {
        let (tx, rx) = channel();
        for (idx, h) in hypotheses.iter().enumerate() {
            let state = proof.state.clone();
            let neg_ex = neg_ex.clone();
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
                examples.push(pointer)
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
        proof.store.prog_cells.reobtain().unwrap();
    }

    let pos_ex = collect_examples(call + 2, &proof.store);

    let top = generalise(pos_ex, proof);

    let elapsed = now.elapsed();
    println!("Generalise Time ms: {}", elapsed.as_millis());

    for (i, h) in top.iter().enumerate() {
        println!("Hypothesis [{i}]");
        for c in h.iter() {
            println!("\t{}", c.to_string(&proof.store))
        }
    }
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
        proof.store.prog_cells.reobtain().unwrap();
    }

    let neg_ex: Arc<[usize]> = collect_examples(call + 3, &proof.store).into();
    // println!("Neg: {neg_ex:?}");

    let top = specialise(neg_ex, top, proof);
    //Plotkin Reduce

    println!("Top Program:");
    for c in top.iter() {
        println!("\t{}", c.to_string(&proof.store));
    }
    let elapsed = now.elapsed();
    println!("Time ms: {}", elapsed.as_millis());
    PredReturn::True
}

pub static TOP_PROGRAM: PredModule = &[("learn", 3, top_prog)];
