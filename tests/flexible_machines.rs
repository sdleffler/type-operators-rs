#[macro_use]
extern crate type_operators;
use type_operators::All;

pub trait Array<T> {}

type_operators! {
    [A, B, C, D, E]

    (Reify) Arrayify(_, T: _): (Array T) {

    }

    (Foo) Bar(All, All, All, All): All {

    }
}
