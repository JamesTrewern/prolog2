use crate::{
    heap::{QueryHeap, VarReg}, program::clause::{BitFlag64},
};

pub fn pre_pass_constraint(
    arg_regs: &mut [VarReg],
    constrained_args: BitFlag64,
    heap: &mut QueryHeap,
) {
    for (i, arg_reg) in arg_regs.iter_mut().enumerate() {
        // If arg_id constrained ensure arg reg set to constrained var
        if constrained_args.get(i){
            if !arg_reg.var(){
                *arg_reg = VarReg::from_var(heap.new_var(*arg_reg))
            }
        }
    }
}