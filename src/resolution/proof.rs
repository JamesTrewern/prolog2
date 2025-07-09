use crate::{
    heap::query_heap::QueryHeap,
    program::{clause::Clause, hypothesis::Hypothesis},
};

pub type Binding = (usize, usize);

pub(super) struct Env {
    pub(super) goal: usize, // Pointer to heap literal
    pub(super) bindings: Vec<Binding>,
    pub(super) choices: Vec<Clause>, //Array of choices which have not been tried
    pub(super) new_clause: bool,     //Was a new clause created by this enviroment
    pub(super) invent_pred: bool,    //If there was a new clause was a new predicate symbol invented
    pub(super) children: usize,      //How many child goals were created
    pub(super) depth: usize,
}

impl Env {
    pub fn new(goal: usize, depth: usize) -> Self {
        Env {
            goal,
            bindings: Vec::new(),
            choices: Vec::new(),
            new_clause: false,
            invent_pred: false,
            children: 0,
            depth,
        }
    }
}

pub struct Proof<'a> {
    stack: Vec<Env>,
    pointer: usize,
    hypothesis: Hypothesis,
    heap: QueryHeap<'a>,
    root_goals: u8, //How many goals were in initial query
}

impl<'a> Proof<'a> {
    // pub fn new();
}
