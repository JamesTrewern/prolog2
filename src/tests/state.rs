use crate::{heap::heap::Tag, interface::state::State};

#[test]
fn load_family() {
    let mut state = State::new(None);
    let [mum, dad, christine, ken, tami, adam, james] = [
        "mum",
        "dad",
        "christine",
        "ken",
        "tami",
        "adam",
        "james",
    ]
    .map(|symbol| state.heap.add_const_symbol(symbol));

    state.load_file("examples/simple_family");
    state.heap.print_heap();
    assert_eq!(&state.heap[..], &[
        (Tag::STR, 2),
        (Tag::CON, mum),    
        (Tag::CON, tami),    
        (Tag::CON, james),    
        (Tag::STR, 2),
        (Tag::CON, mum),    
        (Tag::CON, christine),    
        (Tag::CON, tami), 
        (Tag::STR, 2),
        (Tag::CON, dad),    
        (Tag::CON, ken),    
        (Tag::CON, adam),    
        (Tag::STR, 2),
        (Tag::CON, dad),    
        (Tag::CON, adam),    
        (Tag::CON, james), 
        (Tag::STR, 2),
        (Tag::REFC, 17),    
        (Tag::REFA, 18),    
        (Tag::REFA, 19), 
        (Tag::STR, 2),
        (Tag::REFC, 21),    
        (Tag::REFA, 18),    
        (Tag::REFA, 19), 
    ]);
}
