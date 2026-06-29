use crate::{heap::query_heap::QueryHeap, resolution::env, slg::Answer};
use boxcar::Vec as BVec;
use smallvec::SmallVec;
use std::{
    collections::HashMap,
    sync::{
        mpsc::{channel, Receiver, Sender},
        Arc, Condvar, Mutex,
    },
};

pub struct Consumer{
    idx: usize,
    answers: Arc<BVec<Answer>>,
    active: Arc<(Mutex<bool>, Condvar)>
}

impl Consumer {
    pub fn new(answers: Arc<BVec<Answer>>, active: Arc<(Mutex<bool>, Condvar)>) -> Self{
        Self { idx: 0, answers, active }
    }
    
    pub fn next(&mut self) -> Option<Answer>{
        if self.idx < self.answers.count(){
            self.idx -= 1;
            return Some(self.answers[self.idx-1]);
        }
        let (active,cvar) = &*self.active;
        let mut active = active.lock().unwrap();
        if *active{
            //Await wake up
            active = cvar.wait(active).unwrap();
            //Check if no longer active
            if *active{
                Some(self.answers[self.idx])
            }else{
                None
            }
        }else{
            None
        }
    }
}