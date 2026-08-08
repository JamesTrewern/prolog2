use crate::{
    heap::{QueryHeap, VarReg},
    program::clause::{BitFlag64, MAX_ARG},
};

fn pre_pass_constraint(
    arg_regs: &mut [VarReg; MAX_ARG],
    constrained_args: BitFlag64,
    heap: &mut QueryHeap,
) {
    for (i, arg_reg) in arg_regs.iter_mut().enumerate() {
        if constrained_args.get(i){
            *arg_reg = VarReg::from_var(heap.set_constrained_var(*arg_reg));
        }
    }
}
