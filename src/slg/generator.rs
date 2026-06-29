use crate::{heap::query_heap::QueryHeap, resolution::env, slg::{Answer, consumer::Consumer}};
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
    answer_sender: Sender<Answer>
}


impl<'a> Generator<'a> {
    pub fn generate(&mut self){
        let mut consumers = Vec::<Consumer>::with_capacity(self.literals.len());
        let mut consumed_answers = Vec::<Answer>::with_capacity(self.literals.len());
        let mut idx = 0;
        loop {
            if let Some(consumer) = consumers.get(idx){
                //undo answer
                //answers[idx]
            }else{
                consumers.push(todo!("New consumer from table"));
            }
            if let Some(answer) =  consumers[idx].next(){
                // Update State with answer
                consumed_answers.push(answer);
                if idx == self.literals.len() - 1{
                    // If final literal, send new answer
                    let new_answer: Answer = 0; //TODO create actual answer
                    self.answer_sender.send(new_answer).unwrap();
                }else{
                    idx += 1;
                }
            }else{
                consumers.pop();
                if idx > 0 {
                    idx -= 1;
                }else{
                    return;
                }
            }

        }
    }
}