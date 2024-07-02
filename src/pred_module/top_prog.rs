use super::{PredModule, PredReturn};
use crate::{
    heap::store::{Store, Tag},
    interface::{
        state::{self, State},
        term::{Term, TermClause},
    },
    program::{hypothesis::Hypothesis, program::ProgH},
    resolution::solver::Proof,
};
use rayon::ThreadPool;
use std::{
    collections::{HashMap, HashSet},
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc,
    },
};

#[derive(Default)]
struct GeneraliseWorker;

fn generalise_thread(state: State, goal: Term, tx: Sender<Vec<Box<[TermClause]>>>) {
    let mut store = Store::new(state.heap.try_read_slice().unwrap());
    let goal = goal.build_to_heap(&mut store, &mut HashMap::new(), false);
    let proof = Proof::new(&[goal], store, ProgH::None, None, &state);
    tx.send(proof.collect());
}

fn specialise_thread(
    state: State,
    neg_ex: Arc<[Term]>,
    hypothesis: Box<[TermClause]>,
    tx: Sender<Option<Box<[TermClause]>>>,
) {
    let mut store = Store::new(state.heap.try_read_slice().unwrap());
    let mut h = Hypothesis::new();
    for clause in hypothesis.iter() {
        let clause = clause.to_heap(&mut store);
        h.add_h_clause(clause, &mut store);
    }

    for goal in neg_ex.iter() {
        let mut store = store.clone();
        let goal = goal.build_to_heap(&mut store, &mut HashMap::new(), false);

        if Proof::new(&[goal], store, ProgH::Static(&h), None, &state)
            .next()
            .is_some()
        {
            tx.send(None);
            return;
        }
    }
    tx.send(Some(hypothesis));
}

fn collect_examples(mut addr: usize, store: &Store) -> Box<[usize]> {
    let mut examples = Vec::new();
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
    let pos_ex = collect_examples(call + 2, &proof.store);
    println!("Pos: {pos_ex:?}");

    let top = generalise(pos_ex, proof);

    let neg_ex = collect_examples(call + 3, &proof.store);
    println!("Neg: {neg_ex:?}");

    let top = specialise(neg_ex, top, proof);

    println!("Top Program:");
    for c in top {
        println!("\t{c}");
    }

    PredReturn::True
}

fn generalise(goals: Box<[usize]>, proof: &Proof) -> Vec<Box<[TermClause]>> {
    let n_workers = 8;
    let n_jobs = goals.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(n_workers)
        .build()
        .unwrap();

    let goals: Vec<Term> = goals
        .iter()
        .map(|g| Term::build_from_heap(*g, &proof.store))
        .collect();

    let (tx, rx) = channel();

    for goal in goals {
        let state = proof.state.clone();
        let tx = tx.clone();
        pool.scope(|_| generalise_thread(state, goal, tx))
    }

    let mut res = Vec::new();
    for mut h in rx.iter().take(n_jobs) {
        res.append(&mut h);
    }

    return res;
}

fn specialise(
    neg_ex: Box<[usize]>,
    hypotheses: Vec<Box<[TermClause]>>,
    proof: &Proof,
) -> Vec<TermClause> {
    let n_workers = 8;
    let n_jobs = hypotheses.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(n_workers)
        .build()
        .unwrap();

    let neg_ex: Arc<[Term]> = neg_ex
        .iter()
        .map(|g| Term::build_from_heap(*g, &proof.store))
        .collect();

    let (tx, rx) = channel();

    for h in hypotheses {
        let state = proof.state.clone();
        let neg_ex = neg_ex.clone();
        let tx = tx.clone();
        pool.scope(|_| specialise_thread(state, neg_ex, h, tx))
    }

    let mut res = Vec::<TermClause>::new();
    for h in rx.iter().take(n_jobs) {
        if let Some(h) = h {
            for c in h.into_vec() {
                if !res.contains(&c) {
                    println!("Insert: {c}");
                    res.push(c);
                }
            }
        }
    }

    return res;
}

pub static TOP_PROGRAM: PredModule = &[("learn", 3, top_prog)];
