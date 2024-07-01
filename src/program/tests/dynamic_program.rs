use crate::{
    heap::{heap::Heap, store::Store},
    interface::{
        parser::{parse_clause, tokenise},
        state::State,
    },
    program::{clause::ClauseType, hypothesis::Hypothesis, program::DynamicProgram},
};

fn setup<'a>() -> State {
    let state = State::new(None);
    // let mut store = Store::new(empty.read_slice().unwrap());

    let clauses = [
        (ClauseType::META, "e(X,Y)"),
        (ClauseType::CLAUSE, "a(X,Y)"),
        (ClauseType::BODY, "c(X,Y)"),
        (ClauseType::META, "f(X,Y)"),
        (ClauseType::BODY, "d(X,Y)"),
        (ClauseType::CLAUSE, "b(X,Y)"),
    ];

    for (clause_type, clause_string) in clauses {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut *state.heap.try_write().unwrap());
        clause.clause_type = clause_type;
        state
            .program
            .write()
            .unwrap()
            .add_clause(clause, &*state.heap.try_read().unwrap())
    }

    state
        .program
        .write()
        .unwrap()
        .organise_clause_table(&*state.heap.try_read().unwrap());

    // let mut hypothesis = Hypothesis::new();
    // for clause_string in [("g(X,Y)")] {
    //     let mut clause = parse_clause(&tokenise(&clause_string))
    //         .unwrap()
    //         .to_heap(&mut store);
    //     clause.clause_type = ClauseType::HYPOTHESIS;
    //     hypothesis.add_h_clause(clause, &mut store);
    // }

    state
}

#[test]
fn iter_clause_body() {
    let state = setup();
    let store = Store::new(state.heap.try_read_slice().unwrap());
    let prog = DynamicProgram::new(None, state.program.try_read().unwrap());
    let expected = ['d', 'c', 'b', 'a'];
    for i in prog.iter([true, true, false, false]) {
        assert!(expected.contains(&store.term_string(prog.get(i)[0]).chars().next().unwrap()));
    }
}

#[test]
fn iter_body_meta_hypothesis() {
    let state = setup();
    let mut store = Store::new(state.heap.read_slice().unwrap());
    let mut hypothesis = Hypothesis::new();
    for clause_string in [("g(X,Y)")] {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut store.cells);
        clause.clause_type = ClauseType::HYPOTHESIS;
        hypothesis.add_h_clause(clause, &mut store);
    }
    let prog = DynamicProgram::new(Some(hypothesis), state.program.read().unwrap());
    let expected = ['g', 'f', 'e', 'd', 'c'];
    for i in prog.iter([false, true, true, true]) {
        assert!(
            expected.contains(&store.term_string(prog.get(i)[0]).chars().next().unwrap()),
            "failed on [{i}] {}",
            store.term_string(prog.get(i)[0])
        );
    }
}

#[test]
fn iter_meta_hypothesis() {
    let state = setup();
    let mut store = Store::new(state.heap.read_slice().unwrap());
    let mut hypothesis = Hypothesis::new();
    for clause_string in [("g(X,Y)")] {
        let mut clause = parse_clause(&tokenise(&clause_string))
            .unwrap()
            .to_heap(&mut store.cells);
        clause.clause_type = ClauseType::HYPOTHESIS;
        hypothesis.add_h_clause(clause, &mut store);
    }
    let prog = DynamicProgram::new(Some(hypothesis), state.program.read().unwrap());
    let expected = ['g', 'f', 'e'];
    for i in prog.iter([false, false, true, true]) {
        assert!(expected.contains(&store.term_string(prog.get(i)[0]).chars().next().unwrap()));
    }
}

// #[test]
// fn call_meta_with_con() {
//     let empty: MrwLock<Vec<Cell>> = MrwLock::new(Vec::new());

//     let mut state = State::new(None);
//     let mut store = Store::new(empty.read_slice().unwrap());
//     for clause in ["P(X,Y,Z):-Q(X,Y,Z)\\X,Y"] {
//         let clause = parse_clause(&tokenise(clause)).unwrap().to_heap(&mut store.cells);
//         state.program.write().unwrap().add_clause(clause, &store);
//     }

//     let mut prog = DynamicProgram::new(None, state.program.read().unwrap());

//     let goal = parse_goals(&tokenise("p(a,B,[c])")).unwrap()[0].build_to_heap(
//         &mut store.cells,
//         &mut HashMap::new(),
//         false,
//     );

//     if let CallRes::Clauses(mut choices) = prog.call(goal, &mut store, Config::get_config()) {
//         if let Some(clause) = choices.next() {
//             let clause = prog.get(clause);
//         } else {
//             panic!()
//         }
//     } else {
//         panic!()
//     }
// }
