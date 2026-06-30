use crate::{
    heap::query_heap::QueryHeap,
    resolution::env,
    slg::{consumer::Consumer, Answer},
};
use boxcar::Vec as BVec;
use smallvec::SmallVec;
use std::{
    collections::HashMap,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc, Condvar, Mutex,
    },
};

pub struct EntryManager<'a> {
    generators: Vec<Generator<'a>>,
    active: Arc<(Mutex<bool>, Condvar)>,
    answers: Arc<BVec<Answer>>,
    answer_reciever: Receiver<Answer>,
}

pub struct Generator<'a> {
    heap: QueryHeap<'a>,
    literals: SmallVec<[usize; 3]>,
    answer_sender: Sender<Answer>,
}

impl<'a> Generator<'a> {
    pub fn generate(mut self) {
        let mut consumers = Vec::<Consumer>::with_capacity(self.literals.len());
        let mut answers = Vec::<usize>::with_capacity(self.literals.len());
        let mut literal_idx = 0;
        loop {
            if literal_idx < consumers.len() {
                let undo_answer = consumers[literal_idx].read_answer(answers[literal_idx]);
                // TODO undo answer
                answers[literal_idx] += 1;
            } else {
                consumers.push(todo!("New consumer from table"));
                answers.push(0);
            }
            if let Some(answer) = consumers[literal_idx].consume_answer(answers[literal_idx]) {
                if literal_idx == self.literals.len() - 1 {
                    // If final literal, send new answer
                    let new_answer = Answer::new(); //TODO create actual answer
                    self.answer_sender.send(new_answer).unwrap();
                } else {
                    literal_idx += 1;
                }
            } else {
                consumers.pop();
                answers.pop();
                if literal_idx > 0 {
                    literal_idx -= 1;
                } else {
                    return;
                }
            }
        }
    }
}
