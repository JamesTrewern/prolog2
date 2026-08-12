use std::ops::{Deref, DerefMut};

use crate::heap::VarReg;
use multiversion::multiversion;

#[derive(Debug,PartialEq, Eq)]
pub enum ArgRegs {
    A16([VarReg; 16]),
    A32([VarReg; 32]),
    A64(Box<[VarReg; 64]>),
}

impl ArgRegs {
    /// Given the highest argument id, return new arg regs of appropriate size
    pub fn new_from_max_arg(max_arg_id: usize) -> Self {
        if max_arg_id < 16 {
            Self::new_16()
        } else if max_arg_id < 32 {
            Self::new_32()
        } else {
            Self::new_64()
        }
    }

    pub const fn new_16() -> Self {
        ArgRegs::A16([VarReg::UNBOUND; 16])
    }

    pub const fn new_32() -> Self {
        ArgRegs::A32([VarReg::UNBOUND; 32])
    }

    pub fn new_64() -> Self {
        ArgRegs::A64(Box::new([VarReg::UNBOUND; 64]))
    }

    pub fn find_replace(&mut self, find: VarReg, replace: VarReg) {
        match self {
            ArgRegs::A16(regs) => find_replace_16(regs, find, replace),
            ArgRegs::A32(regs) => find_replace_32(regs, find, replace),
            ArgRegs::A64(regs) => find_replace_64(regs, find, replace),
        }
    }
}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_64(regs: &mut [VarReg; 64], find: VarReg, replace: VarReg) {
    for r in regs.iter_mut() {
        *r = if r.0 == find.0 { replace } else { *r }; // autovectorizes per-clone
    }
}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_32(regs: &mut [VarReg; 32], find: VarReg, replace: VarReg) {
    for r in regs.iter_mut() {
        *r = if r.0 == find.0 { replace } else { *r }; // autovectorizes per-clone
    }
}

#[multiversion(targets = "simd")] // generates avx512/avx2/sse2/neon clones + runtime dispatch
pub fn find_replace_16(regs: &mut [VarReg; 16], find: VarReg, replace: VarReg) {
    for r in regs.iter_mut() {
        *r = if r.0 == find.0 { replace } else { *r }; // autovectorizes per-clone
    }
}

impl Deref for ArgRegs{
    type Target = [VarReg];

    fn deref(&self) -> &Self::Target {
        match self {
            ArgRegs::A16(inner) => inner,
            ArgRegs::A32(inner) => inner,
            ArgRegs::A64(inner) => &**inner,
        }
    }
}

impl DerefMut for ArgRegs{
    fn deref_mut(&mut self) -> &mut Self::Target {
        match self {
            ArgRegs::A16(inner) => inner,
            ArgRegs::A32(inner) => inner,
            ArgRegs::A64(inner) => &mut **inner,
        }
    }
}