use std::ops::{Deref, DerefMut};

use crate::{heap::VarReg, program::BitFlag64};
use multiversion::multiversion;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ArgRegs {
    /// Inline, and the only variant any clause in practice needs: every
    /// clause measured has `max_arg_id < 8`.
    A8([VarReg; 8]),
    /// Boxed fallback at the maximum width, so the enum stays 72 bytes.
    A64(Box<[VarReg; 64]>),
}

impl ArgRegs {
    /// Given the highest argument id, return new arg regs of appropriate size
    pub fn new_from_max_arg(max_arg_id: usize) -> Self {
        if max_arg_id < 8 {
            Self::new_8()
        } else {
            Self::new_64()
        }
    }

    pub const fn new_8() -> Self {
        ArgRegs::A8([VarReg::UNBOUND; 8])
    }

    pub fn new_64() -> Self {
        ArgRegs::A64(Box::new([VarReg::UNBOUND; 64]))
    }

    pub fn find_replace(&mut self, find: VarReg, replace: VarReg) {
        match self {
            ArgRegs::A8(regs) => find_replace_8(regs, find, replace),
            ArgRegs::A64(regs) => find_replace_64(regs, find, replace),
        }
    }

    pub fn to_meta_sub(&self, meta_vars: BitFlag64) -> Self {
        let mut res = self.clone();
        for (i, reg) in res.iter_mut().enumerate() {
            if !meta_vars.get(i) {
                *reg = VarReg::UNBOUND;
            }
        }
        res
    }
}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_8(regs: &mut [VarReg; 8], find: VarReg, replace: VarReg) {
    for r in regs.iter_mut() {
        *r = if r.0 == find.0 { replace } else { *r }; // autovectorizes per-clone
    }
}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_64(regs: &mut [VarReg; 64], find: VarReg, replace: VarReg) {
    for r in regs.iter_mut() {
        *r = if r.0 == find.0 { replace } else { *r }; // autovectorizes per-clone
    }
}

impl Deref for ArgRegs {
    type Target = [VarReg];

    fn deref(&self) -> &Self::Target {
        match self {
            ArgRegs::A8(inner) => inner,
            ArgRegs::A64(inner) => &**inner,
        }
    }
}

impl DerefMut for ArgRegs {
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ArgRegs::A8(inner) => inner,
            ArgRegs::A64(inner) => &mut **inner,
        }
    }
}
