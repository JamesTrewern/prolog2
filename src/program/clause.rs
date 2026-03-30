//! Clause representation and metadata.

use std::ops::{Deref, DerefMut};

use smallvec::SmallVec;

use crate::heap::heap::Heap;

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
}

/// A compiled clause: a list of literal heap addresses with metadata
/// about which variables are second-order (meta) and which are constrained.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Clause {
    literals: SmallVec<[usize; 5]>,
    pub meta_vars: Option<BitFlag64>,
    pub constrained_vars: BitFlag64,
}

impl Clause {
    fn meta_vars_to_bit_flags(meta_vars: Vec<usize>) -> BitFlag64 {
        let mut bit_flags = BitFlag64::default();
        for meta_var in meta_vars {
            assert!(
                meta_var <= 63,
                "meta clause cannot have more than 64 variables (variable index {meta_var} exceeds limit)"
            );
            bit_flags.set(meta_var);
        }
        bit_flags
    }

    pub fn new(
        literals: Vec<usize>,
        meta_vars: Option<Vec<usize>>,
        constrained_vars: Option<Vec<usize>>,
    ) -> Self {
        let meta_vars = meta_vars.map(Self::meta_vars_to_bit_flags);
        let constrained_vars = match constrained_vars {
            Some(cv) => Self::meta_vars_to_bit_flags(cv),
            None => meta_vars.unwrap_or_default(),
        };
        let literals: SmallVec<[usize; 5]> = SmallVec::from_vec(literals);
        Clause {
            literals,
            meta_vars,
            constrained_vars,
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
        let meta_vars = self.meta_vars.ok_or("Clause is not a meta clause")?;
        Ok(meta_vars.get(arg_id))
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
