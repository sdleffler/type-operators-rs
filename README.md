[![Build Status](https://travis-ci.org/sdleffler/type-operators-rs.svg?branch=master)](https://travis-ci.org/sdleffler/type-operators-rs)
[![Docs Status](https://docs.rs/type-operators/badge.svg)](https://docs.rs/type-operators)
[![On crates.io](https://img.shields.io/crates/v/type-operators.svg)](https://crates.io/crates/type-operators)

# type-operators

## The `type_operators` macro - a DSL for declaring type operators and type-level logic in Rust.

This crate contains a macro for declaring type operators in Rust. Type operators are like functions
which act at the type level. The `type_operators` macro works by translating a LISP-y DSL into a big mess of
traits and impls with associated types.

## The DSL

Let's take a look at this fairly small example:

```rust
type_operators! {
    [A, B, C, D, E]

    data Nat {
        P,
        I(Nat = P),
        O(Nat = P),
    }
}
```

There are two essential things to note in this example. The first is the "gensym list" - Rust does
not currently have a way to generate unique identifiers, so we have to supply our own. It is on *you*
to avoid clashes between these pseudo-gensyms and the names of the structs involved! If we put `P`, `I`, or `O`
into the gensym list, things could get really bad! We'd get type errors at compile-time stemming from trait
bounds, coming from the definitions of type operators later. Thankfully, the gensym list can be fairly small
and usually never uses more than two or three symbols.

The second thing is the `data` declaration. This declares a group of structs which fall under a marker trait.
In our case, `Nat` is the marker trait generated and `P`, `I`, and `O` are the structs generated. This example
shows an implementation of natural numbers (positive integers, including zero) which are represented as types.
So, `P` indicates the end of a natural number - think of it as a sort of nil; we're working with a linked list
here, at the type level. So, `I<P>` would represent "one plus twice `P`", which of course comes out to `1`;
`O<P>` would represent "twice `P`", which of course comes out to zero. If we look at `I` and `O` as bits of a
binary number, we come out with a sort of reversed binary representation where the "bit" furthest to the left
is the least significant bit. As such, `O<O<I>>` represents `4`, `I<O<O<I>>>` represents `9`, and so on.

When we write `I(Nat = P)`, the `= P` denotes a default. This lets us write `I`, and have it be inferred to be
`I<P>`, which is probably what you mean if you just write `I` alone. `Nat` gives a trait bound. To better demonstrate,
here is (roughly) what the above invocation of `type_operators` expands to:

```rust
pub trait Nat {}

pub struct P;
impl Nat for P {}

pub struct I<A: Nat = P>(PhantomData<(A)>);
impl<A: Nat> Nat for I<A> {}

pub struct O<A: Nat = P>(PhantomData<(A)>);
impl<A: Nat> Nat for O<A> {}
```

The `Undefined` value looks a little silly, but it allows for the definition of division in a way which uses
type-level comparison and branching. More on that later.

The above definition has a problem. We cannot *fold* our type-level representation down into a numerical representation.
That makes our type-level natural numbers useless! That's why `type_operators` provides another way of defining
type-level representations, the `concrete` declaration:

```rust
type_operators! {
    [A, B, C, D, E]

    concrete Nat => usize {
        P => 0,
        I(N: Nat = P) => 1 + 2 * N,
        O(N: Nat = P) => 2 * N,
        Undefined => panic!("Undefined type-level arithmetic result!"),
    }
}
```

This adds an associated function to the `Nat` trait called `reify`, which allows you to turn your type-level
representations into concrete values of type `usize` (in this case.) If you've ever seen primitive-recursive
functions, then this should look a bit familiar to you - it's reminiscent of a recursion scheme, which is a
way of recursing over a value to map it into something else. (See also "catamorphism".) It should be fairly
obvious how this works, but if not, here's a breakdown:

- `P` always represents zero, so we say that `P => 0`. Simple.
- `I` represents double its argument plus one. If we annotate our macro's definition with a variable `N`,
  then `type_operators` will automatically call `N::reify()` and substitute that value for your `N` in the
  expression you give it. So, in this way, we define the reification of `I` to be one plus two times the
  value that `N` reifies to.
- `O` represents double its argument, so this one's straightforward - it's like `I`, but without the `1 +`.

Okay. So now that we've got that under our belts, let's dive into something a bit more complex: let's define
a type operator for addition.

`type_operators` allows you to define recursive functions. Speaking generally, that's what you'll really need
to pull this off whatever you do. (And speaking precisely, this whole approach was inspired by primitive-recursion.)
So let's think about how we can add two binary numbers, starting at the least-significant bit:
- Obviously, `P + P` should be `P`, since zero plus zero is zero.
- What about `P + O<N>`, for any natural number `N`? Well, that should be `O<N>`. Same with `I<N>`. As a matter of
  fact, now it looks pretty obvious that whenever we have `P` on one side, we should just say that whatever's on the
  other side is the result.
So our little table of operations now looks like:
```text
[P, P] => P
[P, (O N)] => (O N)
[P, (I N)] => (I N)
[(O N), P] => (O N)
[(I N), P] => (I N)
```
Now you're probably saying, "whoa! That doesn't look like Rust at all! Back up!" And that's because it *isn't.* I made
a little LISP-like dialect to describe Rust types for this project because it makes things a lot easier to parse in
macros; specifically, each little atomic type can be wrapped up in a pair of parentheses, while with angle brackets,
Rust has to parse them as separate tokens. In this setup, `(O N)` means `O<N>`,
just `P` alone means `P`, etc. etc. The notation `[X, Y] => Z` means "given inputs `X` and `Y`, produce output `Z`." So
it's a sort of pattern-matching.

Now let's look at the more complex cases. We need to cover all the parts where combinations of `O<N>` and `I<N>` are
added together.
- `O<M> + O<N>` should come out to `O<M + N>`. This is a fairly intuitive result, but we can describe it mathematically
  as `2 * m + 2 * n == 2 * (m + n)`. So, it's the distributive law, and most importantly, it cuts down on the *structure*
  of the arguments - we go from adding `O<M>` and `O<N>` to `M` and `N`, whatever they are, and `M` and `N` are clearly
  less complex than `O<M>` and `O<N>`. If we always see that our outputs have less complexity than the inputs, then we're
  that much closer to a proof that our little type operator always terminates with a result!
- `I<M> + O<N>` and `O<M> + I<N>` should come out to `I<M + N>`. Again, fairly intuitive. We have `1 + 2 * m + 2 * n`,
  which we can package up into `1 + 2 * (m + n)`.
- `I<M> + I<N>` is the trickiest part here. We have `1 + 2 * m + 1 + 2 * n == 2 + 2 * m + 2 * n == 2 * (1 + m + n)`. We
  can implement this as `I<I + M + N>`, but we can do a little bit better. More on that later, we'll head with the simpler
  implementation for now.

Let's add these to the table:
```text
[P, P] => P
[P, (O N)] => (O N)
[P, (I N)] => (I N)
[(O N), P] => (O N)
[(I N), P] => (I N)
// New:
[(O M), (O N)] => (O (# M N))
[(I M), (O N)] => (I (# M N))
[(O M), (I N)] => (I (# M N))
[(I M), (I N)] => (O (# (# I M) N))
```
Here's something new: the `(# ...)` notation. This tells the macro, "hey, we wanna recurse." It's really shorthand
for a slightly more complex piece of notation, but they both have one thing in common - *when type_operators processes
the `(# ...)` notation, it uses it to calculate trait bounds.* This is because your type operator won't compile unless
it's absolutely certain that `(# M N)` will actually have a defined result. At an even higher level, this is the reason
I wish Rust had "closed type families" - if `P`, `I`, and `O` were in a closed type family `Nat`, Rust could check at compile-time
and be absolutely sure that `(# M N)` existed for all `M` and `N` that are in the `Nat` family.

So then. Let's load this into an invocation of `type_operators` to see how it looks like. It's pretty close to the table,
but with a couple additions (I'm leaving out `Undefined` for now because it's not yet relevant):

```rust
type_operators! {
    [A, B, C, D, E]

    concrete Nat => usize {
        P => 0,
        I(N: Nat = P) => 1 + 2 * N,
        O(N: Nat = P) => 2 * N,
    }

    (Sum) Adding(Nat, Nat): Nat {
        [P, P] => P
        forall (N: Nat) {
            [(O N), P] => (O N)
            [(I N), P] => (I N)
            [P, (O N)] => (O N)
            [P, (I N)] => (I N)
        }
        forall (N: Nat, M: Nat) {
            [(O M), (O N)] => (O (# M N))
            [(I M), (O N)] => (I (# M N))
            [(O M), (I N)] => (I (# M N))
            [(I M), (I N)] => (O (# (# M N) I))
        }
    }
}
```

There are several things to note. First, the definition `(Sum) Adding(Nat, Nat): Nat`. This says,
"this type operator takes two `Nat`s as input and outputs a `Nat`." Since addition is implemented
as a recursive trait under the hood, this means we get a trait definition of the form:

```rust
pub trait Adding<A: Nat>: Nat {
    type Output: Nat;
}
```

The `(Sum)` bit declares a nice, convenient alias for us, so that instead of typing `<X as Adding<Y>>::Output`
to get the sum of two numbers, we can instead type `Sum<X, Y>`. Much neater.

Second, the "quantifier" sections (the parts with `forall`) avoid Rust complaining about "undeclared type variables." In any given
generic `impl`, we have to worry about declaring what type variables/generic type parameters we can use in
that `impl`. The `forall` bit modifies the prelude of the `impl`. For example, `forall (N: Nat)` causes all the
`impl`s inside its little block to be declared as `impl<N: Nat> ...` instead of `impl ...`, so that we can use
`N` as a variable inside those expressions.

That just about wraps up our short introduction. To finish, here are the rest of the notations specific to our
little LISP-y dialect, all of which can only be used on the right-hand side of a rule in the DSL:

- `(@TypeOperator ...)` invokes another type operator (can be the original caller!) and generates the proper trait bounds.
- `(% ...)` is like `(# ...)`, but does not generate any trait bounds.
- `(& <type> where (<where_clause>) (<where_clause>) ...)` allows for the definition of custom `where` clauses for a given
  `impl`. It can appear anywhere in the right-hand side of a rule in the DSL, but in general should probably always be
  written at the top-level for consistency.

In addition, it is possible to use attributes such as `#[derive(...)]` or `#[cfg(...)]` on `data` and `concrete` definitions
as well as individual elements inside them. In addition, attributes can be added to the `impl`s for rules. For example:

```rust
type_operators! {
    [A, B, C, D, E]

    data Nat: Default + Debug where #[derive(Default, Debug)] {
        P,
        I(Nat = P),
        O(Nat = P),
        #[cfg(features = "specialization")]
        Error,
        #[cfg(features = "specialization")]
        DEFAULT,
    }

    (Sum) Adding(Nat, Nat): Nat {
        [P, P] => P
        forall (N: Nat) {
            [(O N), P] => (O N)
            [(I N), P] => (I N)
            [P, (O N)] => (O N)
            [P, (I N)] => (I N)
        }
        forall (N: Nat, M: Nat) {
            [(O M), (O N)] => (O (# M N))
            [(I M), (O N)] => (I (# M N))
            [(O M), (I N)] => (I (# M N))
            [(I M), (I N)] => (O (# (# M N) I))

            #[cfg(features = "specialization")] {
                {M, N} => Error
            }
        }
    }
}
```

Note the block `#[cfg(features = "specialization")] { ... }`. This tells `type_operators!` to add the attribute
`#[cfg(features = "specialization")]` to every `impl` declared inside. It's also worth noting that adding derives
to every single statement inside a `concrete` or `data` declaration can be done as shown above with a `where`
clause-like structure - the reason we have to do this is because if we were allowed to define it the intuitive
way, there would be no easy way to extract doc comments on the group trait (thanks to macro parsing ambiguities.)

Current bugs/improvements to be made:
- Bounds in type operators are currently restricted to identifiers only - they should be augmented with a LISP-like
  dialect similar to the rest of the macro system.

If questions are had, I may be found either at my email (which is listed on GitHub) or on the `#rust` IRC, where I go by
the nick `sleffy`.


## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
