extern crate bit_vec;

#[macro_use]
extern crate type_operators;


use bit_vec::BitVec;


pub struct State {
    loc: usize,
    bits: BitVec,
}


type_operators! {
    [A, B, C, D, E]
    
    data Program {
        Empty,
        Left(Program = Empty),
        Right(Program = Empty),
        Flip(Program = Empty),
        Loop(Program = Empty, Program = Empty),
    }

    concrete Bit => bool {
        F => false,
        T => true,
    }

    concrete List => BitVec {
        Nil => BitVec::new(),
        Cons(B: Bit, L: List = Nil) => { let mut tail = L; tail.push(B); tail },
    }

    concrete Smallfsck => State {
        St(L: List, C: Bit, R: List) => {
            // So, R is backwards here. That's a problem! But no worries - we
            // know it's a problem, so now it's less of a problem. ;)

            let mut bits = L;
            let loc = bits.len();
            bits.push(C);
            bits.extend(R.into_iter().rev());

            State {
                loc: loc,
                bits: bits,
            }
        },
    }

    (Run) Running(Program, Smallfsck): Smallfsck {
        forall (P: Program, L: List, C: Bit) {
            [(Left P), (St L C Nil)] => (# P (St (Cons C L) F Nil))
        }
        forall (P: Program, C: Bit, R: List) {
            [(Right P), (St Nil C R)] => (# P (St Nil F (Cons C R)))
        }
        forall (P: Program, L: List, C: Bit, N: Bit, R: List) {
            [(Left P), (St L C (Cons N R))] => (# P (St (Cons C L) N R))
            [(Right P), (St (Cons N L) C R)] => (# P (St L N (Cons C R)))
        }
        forall (P: Program, L: List, R: List) {
            [(Flip P), (St L F R)] => (# P (St L T R))
            [(Flip P), (St L T R)] => (# P (St L F R))
        }
        forall (P: Program, Q: Program, L: List, R: List) {
            [(Loop P Q), (St L F R)] => (# Q (St L F R))
            [(Loop P Q), (St L T R)] => (# (Loop P Q) (# P (St L T R)))
        }
        forall (S: Smallfsck) {
            [Empty, S] => S
        }
    }
}


macro_rules! sf {
    (< $($prog:tt)*) => { Left<sf!($($prog)*)> };
    (> $($prog:tt)*) => { Right<sf!($($prog)*)> };
    (* $($prog:tt)*) => { Flip<sf!($($prog)*)> };
    ([$($prog:tt)*]) => { Loop<sf!($($prog)*)> };
    () => { Nil };
}


type Example = sf!{
    > * > * > * > [ * < ]
};
