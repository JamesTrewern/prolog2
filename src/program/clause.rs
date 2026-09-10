//! Clause representation and metadata.
use crate::heap::Heap;
use smallvec::SmallVec;
use std::ops::{Deref, DerefMut};

pub(crate) const MAX_ARG: usize = 64;

/// Compact 64-bit flag set used to mark meta-variables and constrained variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BitFlag64(u64);

impl BitFlag64 {
    pub fn set(&mut self, idx: usize) {
        self.0 = self.0 | 1 << idx;
    }

    pub fn _unset(&mut self, idx: usize) {
        self.0 = self.0 & !(1 << idx);
    }

    pub fn get(&self, idx: usize) -> bool {
        self.0 & (1 << idx) != 0
    }

    pub fn is_some(&self) -> bool {
        self.0 != 0
    }

    pub fn is_none(&self) -> bool {
        self.0 == 0
    }
}

impl From<Vec<usize>> for BitFlag64 {
    fn from(bit_positions: Vec<usize>) -> Self {
        let mut bit_flags = Self(0);
        for bit_pos in bit_positions {
            assert!(
                bit_pos < MAX_ARG,
                "meta clause cannot have more than {MAX_ARG} variables (variable index {bit_pos} exceeds limit)"
            );
            bit_flags.set(bit_pos);
        }
        bit_flags
    }
}

/// A compiled clause: a list of literal heap addresses with metadata
/// about which variables are second-order (meta) and which are constrained.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Clause {
    literals: SmallVec<[usize; 5]>,
    pub max_arg_id: usize,
    pub meta_vars: BitFlag64,
    pub constrained_vars: BitFlag64,
}

impl Clause {
    pub fn new(
        literals: Vec<usize>,
        meta_constrained_vars: Option<(Vec<usize>, Vec<usize>)>,
        max_arg_id: usize,
    ) -> Self {
        let (meta_vars, constrained_vars) = match meta_constrained_vars {
            Some((mvs, cvs)) => (mvs.into(), cvs.into()),
            None => (BitFlag64::default(), BitFlag64::default()),
        };

        let literals: SmallVec<[usize; 5]> = SmallVec::from_vec(literals);
        Clause {
            literals,
            meta_vars,
            constrained_vars,
            max_arg_id,
        }
    }

    pub fn head(&self) -> usize {
        self[0]
    }

    pub fn body(&self) -> &[usize] {
        &self[1..]
    }

    pub fn meta(&self) -> bool {
        self.meta_vars.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool, &'static str> {
        if self.meta_vars.is_none() {
            return Err("Clause is not a meta clause");
        }
        Ok(self.meta_vars.get(arg_id))
    }

    pub fn constrained_var(&self, arg_id: usize) -> bool {
        self.constrained_vars.get(arg_id)
    }

    pub fn normalise_clause_vars(&self, heap: &mut impl Heap) {
        let mut arg_ids: Vec<usize> = Vec::new();
        for &literal in self.literals.iter() {
            heap.normalise_args(literal, &mut arg_ids);
        }
    }

    pub fn to_string(&self, heap: &impl Heap) -> String {
        if self.len() == 1 {
            return heap.term_string(self.head()) + ".";
        }
        let mut buffer = format!("{}:-", heap.term_string(self.head()));
        for body_literal in self.body() {
            buffer += &heap.term_string(*body_literal);
            buffer += ","
        }
        buffer.pop();
        buffer += ".";
        buffer
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &[usize] {
        &self.literals
    }
}

impl DerefMut for Clause {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.literals
    }
}
