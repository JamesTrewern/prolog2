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
use rayon::iter::Split;
use std::{
    fs,
    io::Write,
    mem::ManuallyDrop,
    sync::{
        mpsc::{channel, Sender},
        Mutex,
    },
    time::Instant,
};

use rand::seq::SliceRandom;
use rand::thread_rng;
use rand_split::{train_test_split, PartsSplit};

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

fn generalise(goals: Box<[usize]>, store: &mut Store, state: &State) -> Vec<ClauseTable> {
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let main_heap = Mutex::new(store);
    let top_prog: Mutex<Vec<ClauseTable>> = Mutex::new(Vec::new());

    let rx = {
        let (tx, rx) = channel();
        for goal in goals.into_vec() {
            pool.scope(|_| generalise_thread(state, &main_heap, &top_prog, goal, tx.clone()))
        }
        rx
    };

    while let Ok(true) = rx.recv() {}
    return top_prog.into_inner().unwrap();
}

fn specialise_thread(
    state: &State,
    store: Store,
    neg_ex: &[usize],
    hypothesis: &ClauseTable,
    idx: usize,
    tx: Sender<(usize, bool)>,
) {
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

fn specialise(
    neg_ex: &[usize],
    hypotheses: Vec<ClauseTable>,
    store: &mut Store,
    state: &State,
) -> ClauseTable {
    let n_jobs = hypotheses.len();
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(*CPU_COUNT)
        .build()
        .unwrap();

    let rx = {
        let (tx, rx) = channel();
        for (idx, h) in hypotheses.iter().enumerate() {
            pool.scope(|_| specialise_thread(state, store.clone(), neg_ex, h, idx, tx.clone()))
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
                if !res.contains(&clause, store) {
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

fn top_prog(
    pos_ex: Box<[usize]>,
    neg_ex: Box<[usize]>,
    store: &mut Store,
    state: &State,
) -> ClauseTable {
    let top = generalise(pos_ex, store, state);

    // for (i, h) in top.iter().enumerate() {
    //     println!("Hypothesis [{i}]");
    //     for c in h.iter() {
    //         println!("\t{}", c.to_string(&proof.store))
    //     }
    // }
    //Drain current heap to static heap.

    let top = specialise(&neg_ex, top, store, state);

    // println!("Top Program:");
    // for c in top.iter() {
    //     println!("\t{}", c.to_string(store));
    // }
    top
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
    top_prog(pos_ex, neg_ex, &mut proof.store, &proof.state);
    PredReturn::True
}

fn top_prog_id(call: usize, proof: &mut Proof) -> PredReturn {
    println!("{}", proof.store.term_string(call));
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

    top_prog(pos_ex, neg_ex, &mut proof.store, &proof.state);
    PredReturn::True
}

fn test_h(
    pos_ex: Box<[usize]>,
    neg_ex: Box<[usize]>,
    store: &mut Store,
    state: &State,
    h: &ClauseTable,
) -> f64 {
    let mut correct: usize = 0;
    let total = (pos_ex.len() + neg_ex.len()) as f64;
    let mut config = state.config.read().unwrap().clone();
    config.learn = false;

    for ex in pos_ex.iter() {
        let mut proof = Proof::new(
            &[*ex],
            store.clone(),
            Hypothesis::Static(h),
            Some(config),
            state,
        );
        if proof.next().is_some() {
            correct += 1;
        }
    }

    for ex in neg_ex.iter() {
        let mut proof = Proof::new(&[*ex], store.clone(), Hypothesis::Static(h), None, state);
        if proof.next().is_none() {
            correct += 1;
        }
    }

    correct as f64 / total
}

fn mean_std_sterr(values: &[f64]) -> (f64, f64, f64) {
    let len = values.len() as f64;
    let avg = values.iter().sum::<f64>() / len;

    let sd = (values.iter().map(|v| (*v - avg).powi(2)).sum::<f64>() / len).sqrt();

    (avg, sd, sd / len.sqrt())
}

fn top_prog_test(pos_ex: Box<[usize]>, neg_ex: Box<[usize]>, proof: &Proof) {
    const SPLITS: [f32; 9] = [0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9];
    const STEPS: usize = 10;
    const SAVE_FILE: &str = "results.csv";

    unsafe { proof.store.prog_cells.early_release() }

    let (mut time_avg, mut time_std, mut time_std_err) = (
        [0.0; SPLITS.len()],
        [0.0; SPLITS.len()],
        [0.0; SPLITS.len()],
    );
    let (mut acc_avg, mut acc_std, mut acc_sd_err) = (
        [0.0; SPLITS.len()],
        [0.0; SPLITS.len()],
        [0.0; SPLITS.len()],
    );

    for (i, split) in SPLITS.into_iter().enumerate() {
        println!("\nSplit: {split}\n----------------------------------");
        let mut times = [0.0; STEPS];
        let mut accuracies = [0.0; STEPS];
        for step in 0..STEPS {
            print!("Step {}/{STEPS}", step + 1);
            let (mut train_pos, mut test_pos) = (Vec::new(), Vec::new());
            pos_ex
                .iter()
                .split_parts(&[split, 1.0 - split])
                .for_each(|sp| {
                    if let Some(ex) = sp[0] {
                        train_pos.push(*ex)
                    }
                    if let Some(ex) = sp[1] {
                        test_pos.push(*ex)
                    }
                });
            let (mut train_neg, mut test_neg) = (Vec::new(), Vec::new());
            neg_ex
                .iter()
                .split_parts(&[split, 1.0 - split])
                .for_each(|sp| {
                    if let Some(ex) = sp[0] {
                        train_neg.push(*ex)
                    }
                    if let Some(ex) = sp[1] {
                        test_neg.push(*ex)
                    }
                });

            let [train_pos, train_neg, test_pos, test_neg]: [Box<[usize]>; 4] = [
                train_pos.into(),
                train_neg.into(),
                test_pos.into(),
                test_neg.into(),
            ];

            let mut store = Store::new(proof.state.heap.read().unwrap());
            let now = Instant::now();
            let h = top_prog(train_pos, train_neg, &mut store, &proof.state);
            times[step] = now.elapsed().as_millis() as f64 / 1000.0;
            accuracies[step] = test_h(test_pos, test_neg, &mut store, &proof.state, &h);
            println!("\tTime: {}, Accuracy: {}", times[step], accuracies[step]);
        }

        (time_avg[i], time_std[i], time_std_err[i]) = mean_std_sterr(&times);
        (acc_avg[i], acc_std[i], acc_sd_err[i]) = mean_std_sterr(&accuracies);

        println!(
            "mean time: {}, deviation: {}, error: {}",
            time_avg[i], time_std[i], time_std_err[i]
        );
        println!(
            "mean accuracy: {}, deviation: {}, error: {} \n",
            acc_avg[i], acc_std[i], time_std_err[i]
        );
    }

    let mut buf = String::from(
        "split, mean_time, sd_time, std_err_time, mean_accuracy, sd_accuracy, std_err_accuracy\n",
    );
    for (i, split) in SPLITS.iter().enumerate() {
        buf += &format!(
            "{split}, {}, {}, {}, {}, {}, {}\n",
            time_avg[i], time_std[i], time_std_err[i], acc_avg[i], acc_std[i], acc_sd_err[i]
        );
    }
    let mut file = fs::File::create(SAVE_FILE).unwrap();
    file.write_all(buf.as_bytes()).unwrap();

    unsafe {
        proof.store.prog_cells.reobtain().unwrap();
    }
}

fn top_prog_no_id_test(call: usize, proof: &mut Proof) -> PredReturn {
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
    top_prog_test(pos_ex, neg_ex, &proof);
    PredReturn::True
}
pub static TOP_PROGRAM: PredModule = &[
    ("learn", 1, top_prog_no_id),
    ("learn", 2, top_prog_id),
    ("test_learn", 1, top_prog_no_id_test),
];
