use std::{
    alloc::{alloc, dealloc, Layout},
    ops::Deref,
    ptr::copy_nonoverlapping,
};

#[derive(Debug, Clone, Copy, Eq)]
pub struct Clause {
    ptr: *const usize,
    len: usize,
    meta_vars: Option<u64>,
}

impl Clause {
    fn meta_vars_to_bit_flags(meta_vars: Vec<usize>) -> u64 {
        let mut bit_flags: u64 = 0;
        for meta_var in meta_vars {
            if meta_var > 65 {
                panic!("Cant have more than 64 variables in meta clause")
            }
            bit_flags = bit_flags | 1 << meta_var
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

    pub fn meta(&self) -> bool {
        self.meta_vars.is_some()
    }

    pub fn meta_var(&self, arg_id: usize) -> Result<bool, &'static str> {
        let meta_vars = self.meta_vars.ok_or("Clause is not a meta clause")?;
        Ok(meta_vars & (1 << arg_id) != 0)
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