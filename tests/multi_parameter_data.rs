#[macro_use]
extern crate type_operators;

type_operators! {
    [A, B, C, D, E]

    concrete Int => isize {
        Term => 0,
        Zero(X: Int = Term) => 3 * X,
        Plus(X: Int = Term) => 3 * X + 1,
        Minus(X: Int = Term) => 3 * X - 1,
        Undefined => panic!("Error: This type-level Int value is undefined, and cannot be reified!"),
    }

    data IntPair {
        Int2(Int, Int),
    }

    (Int2First) Int2P1(IntPair): Int {
        forall (A: Int, B: Int) {
            [(Int2 A B)] => A
        }
    }

    (Int2Second) Int2P2(IntPair): Int {
        forall (A: Int, B: Int) {
            [(Int2 A B)] => B
        }
    }
}
