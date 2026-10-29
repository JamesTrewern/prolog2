//! Clause representation and metadata.
use crate::heap::Heap;
use smallvec::SmallVec;
use std::{
    ops::{Deref, DerefMut},
    sync::atomic::{AtomicUsize, Ordering::Relaxed},
};

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

    /// Iterate the set bit indices in ascending order.
    ///
    /// The inverse of the filter in
    /// [`MetaSub::from_arg_regs`](crate::program::MetaSub::from_arg_regs),
    /// which compacts the argument registers by discarding every position
    /// whose bit is clear. Zipping this iterator with the compacted vector
    /// recovers the original argument ids.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..MAX_ARG).filter(move |&idx| self.get(idx))
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

static META_CLAUSE_COUNT: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct MetaData {
    pub meta_vars: BitFlag64,
    pub constrained_vars: BitFlag64,
    pub id: usize,
}

/// A compiled clause: a list of literal heap addresses with metadata
/// about which variables are second-order (meta) and which are constrained.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Clause {
    pub literals: SmallVec<[usize; 5]>,
    pub max_arg_id: usize,
    pub meta_data: Option<MetaData>,
}

impl Clause {
    pub fn new(
        literals: Vec<usize>,
        meta_constrained_vars: Option<(Vec<usize>, Vec<usize>)>,
        max_arg_id: usize,
    ) -> Self {
        let meta_data = meta_constrained_vars.map(|(mvs, cvs)| MetaData {
            meta_vars: mvs.into(),
            constrained_vars: cvs.into(),
            id: META_CLAUSE_COUNT.fetch_add(1, Relaxed),
        });

        let literals: SmallVec<[usize; 5]> = SmallVec::from_vec(literals);
        Clause {
            literals,
            max_arg_id,
            meta_data,
        }
    }

    pub fn head(&self) -> usize {
        self[0]
    }

    pub fn body(&self) -> &[usize] {
        &self[1..]
    }

    pub fn meta(&self) -> bool {
        self.meta_data.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool, &'static str> {
        if let Some(MetaData { meta_vars, .. }) = self.meta_data {
            Ok(meta_vars.get(arg_id))
        } else {
            return Err("Clause is not a meta clause");
        }
    }

    pub fn constrained_var(&self, arg_id: usize) -> bool {
        if let Some(MetaData {
            constrained_vars, ..
        }) = self.meta_data
        {
            constrained_vars.get(arg_id)
        } else {
            false
        }
    }

    pub fn meta_vars(&self) -> Option<BitFlag64> {
        self.meta_data.as_ref().map(|meta_data| meta_data.meta_vars)
    }

    pub fn constrained_vars(&self) -> Option<BitFlag64> {
        self.meta_data
            .as_ref()
            .map(|meta_data| meta_data.constrained_vars)
    }

    /// Shift every literal's heap address by `offset`. Used when appending a
    /// clause -- and the heap region it was extracted into -- onto a larger,
    /// already-populated heap.
    pub fn shift_literals(&mut self, offset: usize) {
        for literal in self.literals.iter_mut() {
            *literal += offset;
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
