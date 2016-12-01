#![feature(trace_macros)]


#[macro_use]
extern crate type_operators;

pub trait Array<T> {}

trace_macros!(true);

type_operators! {
    [A, B, C, D, E]

    (Reify) Arrayify(_, T: _): (Array T) {

    }

    (Foo) Bar(_, _, _, _): _ {

    }
}
