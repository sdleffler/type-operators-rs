//! # The `type_operators` macro - a DSL for declaring type operators and type-level logic in Rust.
//!
//! This crate contains a macro for declaring type operators in Rust. Type operators are like functions
//! which act at the type level. The `type_operators` macro works by translating a LISP-y DSL into a big mess of
//! traits and impls with associated types.
//!
//! # The DSL
//!
//! Let's take a look at this fairly small example:
//!
//! ```rust
//! # #[macro_use] extern crate type_operators;
//! type_operators! {
//!     [A, B, C, D, E]
//!
//!     data Nat {
//!         P,
//!         I(Nat = P),
//!         O(Nat = P),
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! There are two essential things to note in this example. The first is the "gensym list" - Rust does
//! not currently have a way to generate unique identifiers, so we have to supply our own. It is on *you*
//! to avoid clashes between these pseudo-gensyms and the names of the structs involved! If we put `P`, `I`, or `O`
//! into the gensym list, things could get really bad! We'd get type errors at compile-time stemming from trait
//! bounds, coming from the definitions of type operators later. Thankfully, the gensym list can be fairly small
//! and usually never uses more than two or three symbols.
//!
//! The second thing is the `data` declaration. This declares a group of structs which fall under a marker trait.
//! In our case, `Nat` is the marker trait generated and `P`, `I`, and `O` are the structs generated. This example
//! shows an implementation of natural numbers (positive integers, including zero) which are represented as types.
//! So, `P` indicates the end of a natural number - think of it as a sort of nil; we're working with a linked list
//! here, at the type level. So, `I<P>` would represent "one times twice `P`", which of course comes out to `1`;
//! `O<P>` would represent "twice `P`", which of course comes out to zero. If we look at `I` and `O` as bits of a
//! binary number, we come out with a sort of reversed binary representation where the "bit" furthest to the left
//! is the least significant bit. As such, `O<O<I>>` represents `4`, `I<O<O<I>>>` represents `9`, and so on.
//!
//! When we write `I(Nat = P)`, the `= P` denotes a default. This lets us write `I`, and have it be inferred to be
//! `I<P>`, which is probably what you mean if you just write `I` alone. `Nat` gives a trait bound. To better demonstrate,
//! here is (roughly) what the above invocation of `type_operators` expands to:
//!
//! ```rust
//! # use std::marker::PhantomData;
//!
//! pub trait Nat {}
//!
//! pub struct P;
//! impl Nat for P {}
//!
//! pub struct I<A: Nat = P>(PhantomData<(A)>);
//! impl<A: Nat> Nat for I<A> {}
//!
//! pub struct O<A: Nat = P>(PhantomData<(A)>);
//! impl<A: Nat> Nat for O<A> {}
//! # fn main() {}
//! ```
//!
//! The `Undefined` value looks a little silly, but it allows for the definition of division in a way which uses
//! type-level comparison and branching. More on that later.
//!
//! The above definition has a problem. We cannot *fold* our type-level representation down into a numerical representation.
//! That makes our type-level natural numbers useless! That's why `type_operators` provides another way of defining
//! type-level representations, the `concrete` declaration:
//!
//! ```rust
//! # #[macro_use]
//! # extern crate type_operators;
//!
//! type_operators! {
//!     [A, B, C, D, E]
//!
//!     concrete Nat => usize {
//!         P => 0,
//!         I(N: Nat = P) => 1 + 2 * N,
//!         O(N: Nat = P) => 2 * N,
//!         Undefined => panic!("Undefined type-level arithmetic result!"),
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! This adds an associated function to the `Nat` trait called `reify`, which allows you to turn your type-level
//! representations into concrete values of type `usize` (in this case.) If you've ever seen primitive-recursive
//! functions, then this should look a bit familiar to you - it's reminiscent of a recursion scheme, which is a
//! way of recursing over a value to map it into something else. (See also "catamorphism".) It should be fairly
//! obvious how this works, but if not, here's a breakdown:
//!
//! - `P` always represents zero, so we say that `P => 0`. Simple.
//! - `I` represents double its argument plus one. If we annotate our macro's definition with a variable `N`,
//!   then `type_operators` will automatically call `N::reify()` and substitute that value for your `N` in the
//!   expression you give it. So, in this way, we define the reification of `I` to be one plus two times the
//!   value that `N` reifies to.
//! - `O` represents double its argument, so this one's straightforward - it's like `I`, but without the `1 +`.
//!
//! Okay. So now that we've got that under our belts, let's dive into something a bit more complex: let's define
//! a type operator for addition.
//!
//! `type_operators` allows you to define recursive functions. Speaking generally, that's what you'll really need
//! to pull this off whatever you do. (And speaking precisely, this whole approach was inspired by primitive-recursion.)
//! So let's think about how we can add two binary numbers, starting at the least-significant bit:
//! - Obviously, `P + P` should be `P`, since zero plus zero is zero.
//! - What about `P + O<N>`, for any natural number `N`? Well, that should be `O<N>`. Same with `I<N>`. As a matter of
//!   fact, now it looks pretty obvious that whenever we have `P` on one side, we should just say that whatever's on the
//!   other side is the result.
//! So our little table of operations now looks like:
//! ```text
//! [P, P] => P
//! [P, (O N)] => (O N)
//! [P, (I N)] => (I N)
//! [(O N), P] => (O N)
//! [(I N), P] => (I N)
//! ```
//! Now you're probably saying, "whoa! That doesn't look like Rust at all! Back up!" And that's because it *isn't.* I made
//! a little LISP-like dialect to describe Rust types for this project because it makes things a lot easier to parse in
//! macros; specifically, each little atomic type can be wrapped up in a pair of parentheses, while with angle brackets,
//! Rust has to parse them as separate tokens. In this setup, `(O N)` means `O<N>`,
//! just `P` alone means `P`, etc. etc. The notation `[X, Y] => Z` means "given inputs `X` and `Y`, produce output `Z`." So
//! it's a sort of pattern-matching.
//!
//! Now let's look at the more complex cases. We need to cover all the parts where combinations of `O<N>` and `I<N>` are
//! added together.
//! - `O<M> + O<N>` should come out to `O<M + N>`. This is a fairly intuitive result, but we can describe it mathematically
//!   as `2 * m + 2 * n == 2 * (m + n)`. So, it's the distributive law, and most importantly, it cuts down on the *structure*
//!   of the arguments - we go from adding `O<M>` and `O<N>` to `M` and `N`, whatever they are, and `M` and `N` are clearly
//!   less complex than `O<M>` and `O<N>`. If we always see that our outputs have less complexity than the inputs, then we're
//!   that much closer to a proof that our little type operator always terminates with a result!
//! - `I<M> + O<N>` and `O<M> + I<N>` should come out to `I<M + N>`. Again, fairly intuitive. We have `1 + 2 * m + 2 * n`,
//!   which we can package up into `1 + 2 * (m + n)`.
//! - `I<M> + I<N>` is the trickiest part here. We have `1 + 2 * m + 1 + 2 * m == 2 + 2 * m + 2 * n == 2 * (1 + m + n)`. We
//!   can implement this as `I<I + M + N>`, but we can do a little bit better. More on that later, we'll head with the simpler
//!   implementation for now.
//!
//! Let's add these to the table:
//! ```text
//! [P, P] => P
//! [P, (O N)] => (O N)
//! [P, (I N)] => (I N)
//! [(O N), P] => (O N)
//! [(I N), P] => (I N)
//! // New:
//! [(O M), (O N)] => (O (# M N))
//! [(I M), (O N)] => (I (# M N))
//! [(O M), (I N)] => (I (# M N))
//! [(I M), (I N)] => (O (# (# I M) N))
//! ```
//! Here's something new: the `(# ...)` notation. This tells the macro, "hey, we wanna recurse." It's really shorthand
//! for a slightly more complex piece of notation, but they both have one thing in common - *when type_operators processes
//! the `(# ...)` notation, it uses it to calculate trait bounds.* This is because your type operator won't compile unless
//! it's absolutely certain that `(# M N)` will actually have a defined result. At an even higher level, this is the reason
//! I wish Rust had "closed type families" - if `P`, `I`, and `O` were in a closed type family `Nat`, Rust could check at compile-time
//! and be absolutely sure that `(# M N)` existed for all `M` and `N` that are in the `Nat` family.
//!
//! So then. Let's load this into an invocation of `type_operators` to see how it looks like. It's pretty close to the table,
//! but with a couple additions (I'm leaving out `Undefined` for now because it's not yet relevant):
//!
//! ```rust
//! # #[macro_use] extern crate type_operators;
//!
//! type_operators! {
//!     [A, B, C, D, E]
//!
//!     concrete Nat => usize {
//!         P => 0,
//!         I(N: Nat = P) => 1 + 2 * N,
//!         O(N: Nat = P) => 2 * N,
//!     }
//!
//!     (Sum) Adding(Nat, Nat): Nat {
//!         [P, P] => P
//!         forall (N: Nat) {
//!             [(O N), P] => (O N)
//!             [(I N), P] => (I N)
//!             [P, (O N)] => (O N)
//!             [P, (I N)] => (I N)
//!         }
//!         forall (N: Nat, M: Nat) {
//!             [(O M), (O N)] => (O (# M N))
//!             [(I M), (O N)] => (I (# M N))
//!             [(O M), (I N)] => (I (# M N))
//!             [(I M), (I N)] => (O (# (# M N) I))
//!         }
//!     }
//! }
//! # fn main() {}
//! ```
//!
//! There are several things to note. First, the definition `(Sum) Adding(Nat, Nat): Nat`. This says,
//! "this type operator takes two `Nat`s as input and outputs a `Nat`." Since addition is implemented
//! as a recursive trait under the hood, this means we get a trait definition of the form:
//!
//! ```rust
//! # pub trait Nat {}
//! pub trait Adding<A: Nat>: Nat {
//!     type Output: Nat;
//! }
//! ```
//!
//! The `(Sum)` bit declares a nice, convenient alias for us, so that instead of typing `<X as Adding<Y>>::Output`
//! to get the sum of two numbers, we can instead type `Sum<X, Y>`. Much neater.
//!
//! Second, the "quantifier" sections (the parts with `forall`) avoid Rust complaining about "undeclared type variables." In any given
//! generic `impl`, we have to worry about declaring what type variables/generic type parameters we can use in
//! that `impl`. The `forall` bit modifies the prelude of the `impl`. For example, `forall (N: Nat)` causes all the
//! `impl`s inside its little block to be declared as `impl<N: Nat> ...` instead of `impl ...`, so that we can use
//! `N` as a variable inside those expressions.
//!
//! That just about wraps up our short introduction. To finish, here are the rest of the notations specific to our
//! little LISP-y dialect, all of which can only be used on the right-hand side of a rule in the DSL:
//!
//! - `(@TypeOperator ...)` invokes another type operator (can be the original caller!) and generates the proper trait bounds.
//! - `(% ...)` is like `(# ...)`, but does not generate any trait bounds.
//! - `(& <type> where (<where_clause>) (<where_clause>) ...)` allows for the definition of custom `where` clauses for a given
//!   `impl`. It can appear anywhere in the right-hand side of a rule in the DSL, but in general should probably always be
//!   written at the top-level for consistency.
//!
//! If questions are had, I may be found either at my email (which is listed on GitHub) or on the `#rust` IRC, where I go by
//! the nick `sleffy`.
//!

/// The `type_operators` macro does a lot of different things. Specifically, there are two things
/// it's meant to do:
///     1. Make declaring closed type families easier. (Although they never *really* end up closed... Good enough.)
///     2. Make declaring type operators easier. (Although there are still a lotta problems with this.)
///
/// By "closed type family" here, I mean a family of structs which have a marker trait indicating that they
/// "belong" to the family. A sort of type-level enum, if you will (if only something like that could truly
/// exist in Rust some day!) And by "type operator", I mean a sort of function which acts on types and returns
/// a type. In the following example, the natural numbers (encoded in binary here) are our "closed type family",
/// and addition, subtraction, multiplication, division, etc. etc. are all our type operators.
///
/// You should probably read the top-level documentation before you look at this more complex example.
///
/// ```
/// # #[macro_use]
/// # extern crate type_operators;
///
/// type_operators! {
///     [A, B, C, D, E] // The gensym list. Be careful not to have these collide with your struct names!
///
///     // If I used `data` instead of concrete, no automatic `reify` function would be provided.
///     // But since I did, we have a sort of inductive thing going on here, by which we can transform
///     // any instance of this type into the reified version.
///
///     // data Nat {
///     //     P,
///     //     I(Nat = P),
///     //     O(Nat = P),
///     // }
///
///     concrete Nat => usize {
///         P => 0,
///         I(N: Nat = P) => 1 + 2 * N,
///         O(N: Nat = P) => 2 * N,
///         Undefined => panic!("Undefined type-level arithmetic result!"),
///     }
///
///     // It's not just for natural numbers! Yes, we can do all sorts of logic here. However, in
///     // this example, `Bool` is used later on in implementations that are hidden from you due
///     // to their complexity.
///     concrete Bool => bool {
///         False => false,
///         True => true,
///     }
///
///     (Pred) Predecessor(Nat): Nat {
///         [Undefined] => Undefined
///         [P] => Undefined
///         forall (N: Nat) {
///             [(O N)] => (I (# N))
///             [(I N)] => (O N)
///         }
///     }
///
///     (Succ) Successor(Nat): Nat {
///         [Undefined] => Undefined
///         [P] => I
///         forall (N: Nat) {
///             [(O N)] => (I N)
///             [(I N)] => (O (# N))
///         }
///     }
///
///     (Sum) Adding(Nat, Nat): Nat {
///         [P, P] => P
///         forall (N: Nat) {
///             [(O N), P] => (O N)
///             [(I N), P] => (I N)
///             [P, (O N)] => (O N)
///             [P, (I N)] => (I N)
///         }
///         forall (N: Nat, M: Nat) {
///             [(O M), (O N)] => (O (# M N))
///             [(I M), (O N)] => (I (# M N))
///             [(O M), (I N)] => (I (# M N))
///             [(I M), (I N)] => (O (# (# M N) I))
///         }
///     }
///
///     (Difference) Subtracting(Nat, Nat): Nat {
///         forall (N: Nat) {
///             [N, P] => N
///         }
///         forall (N: Nat, M: Nat) {
///             [(O M), (O N)] => (O (# M N))
///             [(I M), (O N)] => (I (# M N))
///             [(O M), (I N)] => (I (# (# M N) I))
///             [(I M), (I N)] => (O (# M N))
///         }
///     }
///
///     (Product) Multiplying(Nat, Nat): Nat {
///         forall (N: Nat) {
///             [P, N] => P
///         }
///         forall (N: Nat, M: Nat) {
///             [(O M), N] => (# M (O N))
///             [(I M), N] => (@Adding N (# M (O N)))
///         }
///     }
///
///     (If) NatIf(Bool, Nat, Nat): Nat {
///         forall (T: Nat, U: Nat) {
///             [True, T, U] => T
///             [False, T, U] => U
///         }
///     }
///
///     (NatIsUndef) NatIsUndefined(Nat): Bool {
///         [Undefined] => True
///         [P] => False
///         forall (M: Nat) {
///             [(O M)] => False
///             [(I M)] => False
///         }
///     }
///
///     (NatUndef) NatUndefined(Nat, Nat): Nat {
///         forall (M: Nat) {
///             [Undefined, M] => Undefined
///             [P, M] => M
///         }
///         forall (M: Nat, N: Nat) {
///             [(O N), M] => M
///             [(I N), M] => M
///         }
///     }
///
///     (TotalDifference) TotalSubtracting(Nat, Nat): Nat {
///         [P, P] => P
///         [Undefined, P] => Undefined
///         forall (N: Nat) {
///             [N, Undefined] => Undefined
///             [P, (O N)] => (# P N)
///             [P, (I N)] => Undefined
///             [(O N), P] => (O N)
///             [(I N), P] => (I N)
///             [Undefined, (O N)] => Undefined
///             [Undefined, (I N)] => Undefined
///         }
///         forall (N: Nat, M: Nat) {
///             [(O M), (O N)] => (@NatUndefined (# M N) (O (# M N)))
///             [(I M), (O N)] => (@NatUndefined (# M N) (I (# M N)))
///             [(O M), (I N)] => (@NatUndefined (# (# M N) I) (I (# (# M N) I)))
///             [(I M), (I N)] => (@NatUndefined (# M N) (O (# M N)))
///         }
///     }
///
///     (Quotient) Quotienting(Nat, Nat): Nat {
///         forall (D: Nat) {
///             [Undefined, D] => Undefined
///             [P, D] => (@NatIf (@NatIsUndefined (@TotalSubtracting P D)) O (@Successor (# (@TotalSubtracting P D) D)))
///         }
///         forall (N: Nat, D: Nat) {
///             [(O N), D] => (@NatIf (@NatIsUndefined (@TotalSubtracting (O N) D)) O (@Successor (# (@TotalSubtracting (O N) D) D)))
///             [(I N), D] => (@NatIf (@NatIsUndefined (@TotalSubtracting (I N) D)) O (@Successor (# (@TotalSubtracting (I N) D) D)))
///         }
///     }
///
///     (Remainder) Remaindering(Nat, Nat): Nat {
///         forall (D: Nat) {
///             [Undefined, D] => Undefined
///             [P, D] => (@NatIf (@NatIsUndefined (@TotalSubtracting P D)) P (# (@TotalSubtracting P D) D))
///         }
///         forall (N: Nat, D: Nat) {
///             [(O N), D] => (@NatIf (@NatIsUndefined (@TotalSubtracting (O N) D)) (O N) (# (@TotalSubtracting (O N) D) D))
///             [(I N), D] => (@NatIf (@NatIsUndefined (@TotalSubtracting (I N) D)) (I O) (# (@TotalSubtracting (I N) D) D))
///         }
///     }
/// }
///
/// # fn main() {
/// assert_eq!(<I<I> as Nat>::reify(), 3);
/// assert_eq!(<I<O<I>> as Nat>::reify(), 5);
/// assert_eq!(<Sum<I<O<I>>, I<I>> as Nat>::reify(), 8);
/// assert_eq!(<Difference<I<I>, O<I>> as Nat>::reify(), 1);
/// assert_eq!(<Difference<O<O<O<I>>>, I<I>> as Nat>::reify(), 5);
/// assert_eq!(<Product<I<I>, I<O<I>>> as Nat>::reify(), 15);
/// assert_eq!(<Quotient<I<I>, O<I>> as Nat>::reify(), 1);
/// assert_eq!(<Remainder<I<O<O<I>>>, O<O<I>>> as Nat>::reify(), 1);
/// # }
/// ```
#[macro_export]
macro_rules! type_operators {
    ($gensym:tt data $name:ident { $($stuff:tt)* } $($rest:tt)*) => {
        pub trait $name {}

        _tlsm_data!($name $gensym $($stuff)*);
        type_operators!($gensym $($rest)*);
    };

    ($gensym:tt concrete $name:ident => $output:ty { $($stuff:tt)* } $($rest:tt)*) => {
        pub trait $name {
            fn reify() -> $output;
        }

        _tlsm_concrete!($name $output; $gensym $($stuff)*);
        type_operators!($gensym $($rest)*);
    };

    ($gensym:tt ($alias:ident) $machine:ident ($($kind:tt),*): $out:tt { $($states:tt)* } $($rest:tt)*) => {
        _tlsm_machine!($alias $machine $gensym [$($kind),*] [] $out);
        _tlsm_states!($machine $($states)*);

        type_operators!($gensym $($rest)*);
    };

    ($gensym:tt) => {};
}

#[macro_export]
macro_rules! _tlsm_parse_type {
    (($parameterized:ident $($arg:tt)*)) => {
        $parameterized<$(_tlsm_parse_type!($arg)),*>
    };
    ($constant:ident) => {
        $constant
    };
}

#[macro_export]
macro_rules! _tlsm_states {
    (@bounds $machine:ident $implinfo:tt [$($bounds:tt)*] [$($queue:tt)*] (& $arg:tt where $($extra:tt)*)) => {
        _tlsm_states!(@bounds $machine $implinfo [$($bounds)* $($extra)*] [$($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt $bounds:tt [$($queue:tt)*] (% $arg:tt $($more:tt)*)) => {
        _tlsm_states!(@bounds $machine $implinfo $bounds [$($more)* $($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt [$($bounds:tt)*] [$($queue:tt)*] (# $arg:tt $($more:tt)+)) => {
        _tlsm_states!(@bounds $machine $implinfo
                [$($bounds)* (_tlsm_states!(@output $machine $arg):
                    $machine< $(_tlsm_states!(@output $machine $more)),+ >)] [$($more)* $($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt [$($bounds:tt)*] [$($queue:tt)*] (@ $external:ident $arg:tt $($more:tt)+)) => {
        _tlsm_states!(@bounds $machine $implinfo
                [$($bounds)* (_tlsm_states!(@output $machine $arg):
                    $external< $(_tlsm_states!(@output $machine $more)),+ >)] [$($more)* $($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt [$($bounds:tt)*] [$($queue:tt)*] (# $arg:tt)) => {
        _tlsm_states!(@bounds $machine $implinfo
                [$($bounds)* (_tlsm_states!(@output $machine $arg): $machine)] [$($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt [$($bounds:tt)*] [$($queue:tt)*] (@ $external:ident $arg:tt)) => {
        _tlsm_states!(@bounds $machine $implinfo
                [$($bounds)* (_tlsm_states!(@output $machine $arg): $external)] [$($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt $bounds:tt [$($queue:tt)*] ($parameterized:ident $arg:tt $($args:tt)*)) => {
        _tlsm_states!(@bounds $machine $implinfo $bounds [$($args)* $($queue)*] $arg);
    };
    (@bounds $machine:ident $implinfo:tt $bounds:tt [$next:tt $($queue:tt)*] $constant:ident) => {
        _tlsm_states!(@bounds $machine $implinfo $bounds [$($queue)*] $next);
    };
    (@bounds $machine:ident { $($implinfo:tt)* } $bounds:tt [] $constant:ident) => {
        _tlsm_states!(@implement $machine $bounds $($implinfo)*);
    };
    (@dispatch $machine:ident forall $quantified:tt { $($input:tt => $output:tt)* }) => {
        $(_tlsm_states!(@bounds $machine { $quantified $input => $output } [] [] $output);)*
    };
    (@dispatch $machine:ident $input:tt => $output:tt) => {
        _tlsm_states!(@bounds $machine { () $input => $output } [] [] $output);
    };
    (@implement $machine:ident [$(($($constraint:tt)*))+] ($($bounds:tt)+) [$head:tt $(, $input:tt)+] => $output:tt) => {
        impl<$($bounds)+> $machine< $(_tlsm_parse_type!($input)),+ > for _tlsm_parse_type!($head) where $($($constraint)*),+
        {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [$(($($constraint:tt)*))+] ($($bounds:tt)+) [$head:tt] => $output:tt) => {
        impl<$($bounds)+> $machine for _tlsm_parse_type!($head) where $($($constraint)*),+
        {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [$(($($constraint:tt)*))+] () [$head:tt $(, $input:tt)+] => $output:tt) => {
        impl $machine< $(_tlsm_parse_type!($input)),+ > for _tlsm_parse_type!($head) where $($($constraint)*),+
        {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [$(($($constraint:tt)*))+] () [$head:tt] => $output:tt) => {
        impl $machine for _tlsm_parse_type!($head) where $($($constraint)*),+
        {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [] ($($bounds:tt)+) [$head:tt $(, $input:tt)+] => $output:tt) => {
        impl<$($bounds)+> $machine< $(_tlsm_parse_type!($input)),+ > for _tlsm_parse_type!($head) {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [] ($($bounds:tt)+) [$head:tt] => $output:tt) => {
        impl<$($bounds)+> $machine for _tlsm_parse_type!($head) {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [] () [$head:tt $(, $input:tt)+] => $output:tt) => {
        impl $machine< $(_tlsm_parse_type!($input)),+ > for _tlsm_parse_type!($head) {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@implement $machine:ident [] () [$head:tt] => $output:tt) => {
        impl $machine for _tlsm_parse_type!($head) {
            type Output = _tlsm_states!(@output $machine $output);
        }
    };
    (@output $machine:ident (& $arg:tt $($extra:tt)*)) => {
        _tlsm_states!(@output $machine $arg)
    };
    (@output $machine:ident (# $arg:tt $($more:tt)+)) => {
        <_tlsm_states!(@output $machine $arg) as $machine< $(_tlsm_states!(@output $machine $more)),+ >>::Output
    };
    (@output $machine:ident (# $arg:tt)) => {
        <_tlsm_states!(@output $machine $arg) as $machine>::Output
    };
    (@output $machine:ident (% $arg:tt $($more:tt)+)) => {
        <_tlsm_states!(@output $machine $arg) as $machine< $(_tlsm_states!(@output $machine $more)),+ >>::Output
    };
    (@output $machine:ident (% $arg:tt)) => {
        <_tlsm_states!(@output $machine $arg) as $machine>::Output
    };
    (@output $machine:ident (@ $external:ident $arg:tt $($more:tt)+)) => {
        <_tlsm_states!(@output $machine $arg) as $external< $(_tlsm_states!(@output $machine $more)),+ >>::Output
    };
    (@output $machine:ident (@ $external:ident $arg:tt)) => {
        <_tlsm_states!(@output $machine $arg) as $external>::Output
    };
    (@output $machine:ident ($parameterized:ident $($arg:tt)+)) => {
        $parameterized<$(_tlsm_states!(@output $machine $arg)),+>
    };
    (@output $machine:ident $constant:ident) => {
        $constant
    };
    ($machine:ident $($head:tt $body:tt $tail:tt)*) => {
        $(_tlsm_states!(@dispatch $machine $head $body $tail);)*
    };
}

#[macro_export]
macro_rules! _tlsm_machine {
    ($alias:ident $machine:ident [$gensym:ident $(, $gensyms:ident)*] [_ $(, $kinds:tt)*] [$($accum:tt)*] $out:tt) => {
        _tlsm_machine!($alias $machine [$($gensyms),*] [$($kinds),*] [$($accum)* ($gensym)] $out);
    };
    ($alias:ident $machine:ident [$gensym:ident $(, $gensyms:ident)*] [$kind:tt $(, $kinds:tt)*] [$($accum:tt)*] $out:tt) => {
        _tlsm_machine!($alias $machine [$($gensyms),*] [$($kinds),*] [$($accum)* ($gensym: $kind)] $out);
    };
    ($alias:ident $machine:ident $gensym:tt [] [($fsym:ident $($fbound:tt)*) $(($sym:ident $($bound:tt)*))+] _) => {
        pub trait $machine < $($sym $($bound)*),+ > $($fbound)* {
            type Output;
        }

        pub type $alias < $fsym $($fbound)* $(, $sym $($bound)*)+ > = <$fsym as $machine< $($sym),+ >>::Output;
    };
    ($alias:ident $machine:ident $gensym:tt [] [($fsym:ident $($fbound:tt)*)] _) => {
        pub trait $machine $($fbound)* {
            type Output;
        }

        pub type $alias < $fsym $($fbound)* > = <$fsym as $machine>::Output;
    };
    ($alias:ident $machine:ident $gensym:tt [] [($fsym:ident $($fbound:tt)*) $(($sym:ident $($bound:tt)*))+] $out:ident) => {
        pub trait $machine < $($sym $($bound)*),+ > $($fbound)* {
            type Output: $out;
        }

        pub type $alias < $fsym $($fbound)* $(, $sym $($bound)*)+ > = <$fsym as $machine< $($sym),+ >>::Output;
    };
    ($alias:ident $machine:ident $gensym:tt [] [($fsym:ident $($fbound:tt)*)] $out:ident) => {
        pub trait $machine $($fbound)* {
            type Output: $out;
        }

        pub type $alias < $fsym $($fbound)* > = <$fsym as $machine>::Output;
    };
}

#[macro_export]
macro_rules! _tlsm_data {
    ($group:ident @parameterized $name:ident [$gensym:ident $(, $next:ident)*] [$($args:tt)*] [$($bounds:tt)*] [$($phantom:tt)*] $kind:ident = $default:ty $(, $($rest:tt)*)*) => {
        _tlsm_data!($group @parameterized $name [$($next),*] [$($args)* ($gensym: $kind = $default)] [$($bounds)* ($gensym: $kind)] [$($phantom)* ($gensym)] $($($rest)*),*);
    };
    ($group:ident @parameterized $name:ident [$gensym:ident $(, $next:ident)*] [$($args:tt)*] [$($bounds:tt)*] [$($phantom:tt)*] $kind:ident $($rest:tt)*) => {
        _tlsm_data!($group @parameterized $name [$($next),*] [$($args)* ($gensym: $kind)] [$($bounds)* ($gensym: $kind)] [$($phantom)* ($gensym)] $($rest)*);
    };
    ($group:ident @parameterized $name:ident $gensyms:tt [$(($($args:tt)*))*] [$(($($bounds:tt)*))*] [$(($($phantom:tt)*))*]) => {
        pub struct $name < $($($args)*),* >(::std::marker::PhantomData<($($($phantom)*),*)>);
        impl< $($($bounds)*),* > $group for $name<$($($phantom)*),*> {}
    };
    ($group:ident $gensym:tt $name:ident, $($rest:tt)*) => {
        pub struct $name;
        impl $group for $name {}
        _tlsm_data!($group $gensym $($rest)*);
    };
    ($group:ident $gensym:tt $name:ident($($args:tt)*), $($rest:tt)*) => {
        _tlsm_data!($group @parameterized $name $gensym [] [] [] $($args)*);
        _tlsm_data!($group $gensym $($rest)*);
    };
    ($group:ident $gensym:tt) => {};
}

#[macro_export]
macro_rules! _tlsm_concrete {
    ($group:ident $output:ty; @parameterized $name:ident => $value:expr; $gensym:tt [$($args:tt)*] [$($bounds:tt)*] [$($syms:ident)*] $sym:ident: $kind:ident = $default:ty $(, $($rest:tt)*)*) => {
        _tlsm_concrete!($group $output; @parameterized $name => $value; $gensym [$($args)* ($sym: $kind = $default)] [$($bounds)* ($sym: $kind)] [$($syms)* $sym] $($($rest)*),*);
    };
    ($group:ident $output:ty; @parameterized $name:ident => $value:expr; $gensym:tt [$($args:tt)*] [$($bounds:tt)*] [$($syms:ident)*] $sym:ident: $kind:ident $(, $($rest:tt)*)*) => {
        _tlsm_concrete!($group $output; @parameterized $name => $value; $gensym [$($args)* ($sym: $kind)] [$($bounds)* ($sym: $kind)] [$($syms)* $sym] $($($rest)*),*);
    };
    ($group:ident $output:ty; @parameterized $name:ident => $value:expr; [$gensym:ident $(, $next:ident)*] [$($args:tt)*] [$($bounds:tt)*] $syms:tt $kind:ident = $default:ty $(, $($rest:tt)*)*) => {
        _tlsm_concrete!($group $output; @parameterized $name => $value; [$($next),*] [$($args)* ($gensym: $kind = $default)] [$($bounds)* ($gensym: $kind)] $syms $($($rest)*),*);
    };
    ($group:ident $output:ty; @parameterized $name:ident => $value:expr; [$gensym:ident $(, $next:ident)*] [$($args:tt)*] [$($bounds:tt)*] $syms:tt $kind:ident $(, $($rest:tt)*)*) => {
        _tlsm_concrete!($group $output; @parameterized $name => $value; [$($next),*] [$($args)* ($gensym: $kind)] [$($bounds)* ($gensym: $kind)] $syms $($($rest)*),*);
    };
    ($group:ident $output:ty; @parameterized $name:ident => $value:expr; $gensyms:tt [$(($tysym:ident: $($args:tt)*))*] [$(($bsym:ident: $bound:ident))*] [$($sym:ident)*]) => {
        pub struct $name < $($tysym: $($args)*),* >(::std::marker::PhantomData<($($tysym),*)>);

        impl< $($bsym: $bound),* > $group for $name<$($bsym),*> {
            #[allow(non_snake_case)]
            fn reify() -> $output { $(let $sym = <$sym>::reify();)* $value }
        }
    };
    ($group:ident $output:ty; $gensym:tt $name:ident => $value:expr, $($rest:tt)*) => {
        pub struct $name;

        impl $group for $name {
            fn reify() -> $output { $value }
        }

        _tlsm_concrete!($group $output; $gensym $($rest)*);
    };
    ($group:ident $output:ty; $gensym:tt $name:ident($($args:tt)*) => $value:expr, $($rest:tt)*) => {
        _tlsm_concrete!($group $output; @parameterized $name => $value; $gensym [] [] [] $($args)*);
        _tlsm_concrete!($group $output; $gensym $($rest)*);
    };
    ($group:ident $output:ty; $gensym:tt) => {};
}
