use super::{PredModule, PredReturn};
use crate::{
    heap::{
        self,
        heap::Heap,
        store::{Cell, Store, Tag},
    },
    interface::state::State,
    program::{clause::Clause, clause_table::ClauseTable, dynamic_program::Hypothesis},
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
    main_heap: &mut Vec<Cell>,
    sub_heap: &Store,
    hypotheses: Vec<ClauseTable>,
) -> Vec<ClauseTable> {
    hypotheses
        .into_iter()
        .map(|h| {
            let mut newh = ClauseTable::new();
            for c in h.iter() {
                {
                    let new_literals: Box<[usize]> = c
                        .iter()
                        .map(|l| main_heap.copy_term(sub_heap, *l))
                        .collect();
                    newh.add_clause(Clause {
                        clause_type: c.clause_type,
                        literals: ManuallyDrop::new(new_literals),
                    });
                }
            }
            newh
        })
        .collect()
}

fn generalise_thread(
    state: State,
    main_heap: &Mutex<&mut Vec<Cell>>,
    goal: usize,
    tx: Sender<Vec<ClauseTable>>,
) {
    let store = Store::new(state.heap.try_read().unwrap());
    // let goal = goal.build_to_heap(&mut store, &mut HashMap::new(), false);
    let mut proof = Proof::new(&[goal], store, Hypothesis::None, None, &state);

    //Iterate over proof tree leaf nodes and collect hypotheses
    let mut hs = Vec::<ClauseTable>::new();
    while let Some(hypothesis) = proof.next() {
        hs.push(hypothesis);
    }

    tx.send(extract_clause_terms(
        &mut main_heap.try_lock().unwrap(),
        &proof.store,
        hs,
    ))
    .unwrap();
}

fn generalise(goals: Box<[usize]>, proof: &mut Proof) -> (Vec<ClauseTable>) {
    let n_jobs = goals.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let (tx, rx) = channel();

    let main_heap = Mutex::new(&mut proof.store.cells);

    for goal in goals.into_vec() {
        let state = proof.state.clone();
        let tx = tx.clone();
        pool.scope(|_| generalise_thread(state, &main_heap, goal, tx))
    }

    let mut res = Vec::new();
    for mut h in rx.iter().take(n_jobs) {
        res.append(&mut h);
    }

    println!("After colect H");
    return res;
}

fn specialise_thread(
    state: State,
    neg_ex: &[usize],
    hypothesis: ClauseTable,
    tx: Sender<Option<ClauseTable>>,
) {
    let store = Store::new(state.heap.try_read().unwrap());

    let mut config = *state.config.read().unwrap();
    config.learn = false;

    for goal in neg_ex.iter() {
        let store = store.clone();
        if Proof::new(
            &[*goal],
            store,
            Hypothesis::Static(&hypothesis),
            Some(config),
            &state,
        )
        .next()
        .is_some()
        {
            tx.send(None);
            return;
        }
    }
    tx.send(Some(hypothesis));
}

fn specialise(neg_ex: Box<[usize]>, hypotheses: Vec<ClauseTable>, proof: &Proof) -> ClauseTable {
    let n_jobs = hypotheses.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    // let neg_ex: Arc<[Term]> = neg_ex
    //     .iter()
    //     .map(|g| Term::build_from_heap(*g, &proof.store))
    //     .collect();

    let (tx, rx) = channel();

    for h in hypotheses {
        let state = proof.state.clone();
        let neg_ex = neg_ex.clone();
        let tx = tx.clone();
        pool.scope(|_| specialise_thread(state, &neg_ex, h, tx))
    }

    let mut res: ClauseTable = ClauseTable::new();
    for hypothesis in rx.iter().take(n_jobs) {
        if let Some(hypothesis) = hypothesis {
            for clause in hypothesis.iter() {
                res.add_clause(clause)
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
        proof.store.prog_cells.reobtain();
    }

    let pos_ex = collect_examples(call + 2, &proof.store);
    // println!("Pos: {pos_ex:?}");
    let top = generalise(pos_ex, proof);


    for (i,h) in top.iter().enumerate(){
        println!("Hypothesis [{i}]");
        for c in h.iter(){
            println!("\t{}", c.to_string(&*proof.state.heap.read().unwrap()))
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
        proof.store.prog_cells.reobtain();
    }

    let neg_ex = collect_examples(call + 3, &proof.store);
    // println!("Neg: {neg_ex:?}");

    let top = specialise(neg_ex, top, proof);

    println!("Top Program:");
    for c in top.iter() {
        println!("\t{}", c.to_string(&proof.store));
    }
    let elapsed = now.elapsed();
    println!("Time ms: {}", elapsed.as_millis());
    PredReturn::True
}

pub static TOP_PROGRAM: PredModule = &[("learn", 3, top_prog)];
