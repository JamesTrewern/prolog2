use std::{
    alloc::{alloc, dealloc, Layout},
    ops::Deref,
    ptr::copy_nonoverlapping,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct BitFlag64(u64);

impl BitFlag64 {
    pub fn set(&mut self, idx: usize) {
        self.0 = self.0 | 1 << idx;
    }

    pub fn unset(&mut self, idx: usize) {
        self.0 = self.0 & !(1 << idx);
    }

    pub fn get(&self, idx: usize) -> bool {
        self.0 & (1 << idx) != 0
    }
}

#[derive(Debug, Clone, Copy, Eq)]
pub struct Clause {
    ptr: *const usize,
    len: usize,
    meta_vars: Option<BitFlag64>,
}

impl Clause {
    fn meta_vars_to_bit_flags(meta_vars: Vec<usize>) -> BitFlag64 {
        let mut bit_flags = BitFlag64::default();
        for meta_var in meta_vars {
            if meta_var > 63 {
                panic!("Cant have more than 64 variables in meta clause")
            }
            bit_flags.set(meta_var);
        }
        bit_flags
    }

    pub fn new(literals: Vec<usize>, meta_vars: Option<Vec<usize>>) -> Self {
        let len = literals.len();
        let meta_vars = meta_vars.map(Self::meta_vars_to_bit_flags);
        unsafe {
            let layout = Layout::array::<usize>(len).unwrap();
            let ptr = alloc(layout) as *mut usize;
            copy_nonoverlapping(literals.as_ptr(), ptr, len);
            Clause {
                ptr: ptr as *const usize,
                len,
                meta_vars,
            }
        }
    }

    pub fn head(&self) -> usize {
        self[0]
    }

    pub fn body(&self) -> &[usize]{
        &self[1..]
    }

    pub fn meta(&self) -> bool {
        self.meta_vars.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool, &'static str> {
        let meta_vars = self.meta_vars.ok_or("Clause is not a meta clause")?;
        Ok(meta_vars.get(arg_id))
    }

    pub fn drop(self) {
        unsafe {
            dealloc(
                self.ptr as *mut u8,
                Layout::array::<usize>(self.len()).unwrap(),
            )
        };
    }
}

impl Deref for Clause {
    type Target = [usize];

    fn deref(&self) -> &[usize] {
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        self.deref() == other.deref()
    }
}
