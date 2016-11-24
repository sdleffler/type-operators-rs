#[macro_use]
extern crate type_operators;

mod concrete {
    type_operators! {
        [A, B, C, D, E]

        concrete Nat: Default => usize {
            #[derive(Default)]
            Z => 0,
            #[derive(Default)]
            S(N: Nat) => 1 + N,
        }
    }
}

mod data {
    type_operators! {
        [A, B, C, D, E]

        data Nat: Default {
            #[derive(Default)]
            Z,
            #[derive(Default)]
            S(Nat),
        }
    }
}
