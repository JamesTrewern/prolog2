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
    answers: Arc<BVec<Answer>>,
    active: Arc<(Mutex<bool>, Condvar)>
}

impl Consumer {
    pub fn new(answers: Arc<BVec<Answer>>, active: Arc<(Mutex<bool>, Condvar)>) -> Self{
        Self { answers, active }
    }
    
    /// Attempt to consumer next answer
    /// If idx less than answer count return answer @ idx
    /// Else If active, wait for update from generator, return none or new answer
    /// Else return None
    pub fn consume_answer(&self, idx: usize) -> Option<&Answer>{
        if idx < self.answers.count(){
            return Some(&self.answers[idx]);
        }
        let (active,cvar) = &*self.active;
        let mut active = active.lock().unwrap();
        if *active{
            //Await wake up
            active = cvar.wait(active).unwrap();
            //Check if no longer active
            if *active{
                Some(&self.answers[idx])
            }else{
                None
            }
        }else{
            None
        }
    }

    /// Simply read an answer in the answer array for this consumer 
    /// May panic if index to large
    pub fn read_answer(&self, idx: usize) -> &Answer{
        &self.answers[idx]
    }
}
