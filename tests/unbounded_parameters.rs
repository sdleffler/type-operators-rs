#[macro_use]
extern crate type_operators;

type_operators! {
    [A, B, C, D, E]

    data List {
        Nil,
        Cons(_, List),
    }
}
