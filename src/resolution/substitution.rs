use std::ops::{Deref, DerefMut};

use smallvec::SmallVec;
use crate::heap::{VarBind::{self,*}, VarReg};

/// Substitution mapping clause `Arg` cells to heap addresses.
///
/// Tracks argument register bindings and direct heap-to-heap bindings
/// produced during unification.
#[derive(Debug, PartialEq)]
pub struct Substitution {
    pub(crate) arg_regs: [VarReg; 32],
    pub(crate) bound_vars: SmallVec<[usize; 5]>, // List of bound variables
    pub(crate) needs_rebuild: SmallVec<[bool; 5]>, // Are bound variables bound to complex?
}

impl Deref for Substitution {
    type Target = [usize];
    fn deref(&self) -> &Self::Target {
        &self.bound_vars
    }
}

impl DerefMut for Substitution {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bound_vars
    }
}

impl Default for Substitution {
    fn default() -> Self {
        Self {
            arg_regs: [VarReg::UNBOUND; 32],
            bound_vars: SmallVec::new(),
            needs_rebuild: SmallVec::new(),
        }
    }
}

impl Substitution {
    pub fn bound(&self, var_id: usize) -> bool {
        self.bound_vars.contains(&var_id)
    }

    pub fn get_arg(&self, arg_id: usize) -> Option<VarBind> {
        self.arg_regs[arg_id].get_bind()
    }

    pub fn set_arg(&mut self, arg_id: usize, binding: VarBind) {
        self.arg_regs[arg_id].bind(binding);
    }

    pub fn get_bound_vars(self) -> Box<[usize]> {
        self.bound_vars.into_boxed_slice()
    }

    pub fn push_bound_var(&mut self, var_id: usize, needs_rebuild: bool, binding: VarBind) {
        self.bound_vars.push(var_id);
        self.needs_rebuild.push(needs_rebuild);
        self.update_arg_regs(var_id, binding);
    }

    /// When binding a var in heap, check if any args are bound to var
    /// and update arg binding if they are 
    pub fn update_arg_regs(&mut self, var_id: usize, binding: VarBind){
        let find: VarReg = Var(var_id).into();
        let replace: VarReg = binding.into();

        VarReg::replace_all(&mut self.arg_regs, find, replace);
        //SIMD find and replace values
        //self.arg_regs find replace
    }
}
