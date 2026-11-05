use std::ops::{Deref, DerefMut};

use crate::{heap::VarReg, ARG_REGS_DEFAULT_SIZE};
use multiversion::multiversion;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ArgRegs {
    /// Inline, and the only variant any clause in practice needs: every
    /// clause measured has `max_arg_id < 8`.
    A8([VarReg; ARG_REGS_DEFAULT_SIZE]),
    /// Boxed fallback at the maximum width, so the enum stays 72 bytes.
    A64(Box<[VarReg; 64]>),
}

impl ArgRegs {
    /// Given the highest argument id, return new arg regs of appropriate size
    pub fn new_from_max_arg(max_arg_id: usize) -> Self {
        if max_arg_id < ARG_REGS_DEFAULT_SIZE {
            Self::new_8()
        } else {
            Self::new_64()
        }
    }

    pub const fn new_8() -> Self {
        ArgRegs::A8([VarReg::UNBOUND; ARG_REGS_DEFAULT_SIZE])
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

}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_8(regs: &mut [VarReg; ARG_REGS_DEFAULT_SIZE], find: VarReg, replace: VarReg) {
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
