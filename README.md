# `collection_macro`

<!-- cargo-rdme start -->

[![crates.io](https://img.shields.io/crates/v/collection_macro?style=flat-square&logo=rust)](https://crates.io/crates/collection_macro)
[![docs.rs](https://img.shields.io/badge/docs.rs-collection_macro-blue?style=flat-square&logo=docs.rs)](https://docs.rs/collection_macro)
![license](https://img.shields.io/badge/license-Apache--2.0_OR_MIT-blue?style=flat-square)
![msrv](https://img.shields.io/badge/msrv-1.60-blue?style=flat-square&logo=rust)
[![github](https://img.shields.io/github/stars/nik-rev/collection-macro)](https://github.com/nik-rev/collection-macro)

This crate provides the general-purpose [`seq![]`](https://docs.rs/collection_macro/latest/collection_macro/macro.seq.html) and [`map! {}`](https://docs.rs/collection_macro/latest/collection_macro/macro.map.html) macros.

```toml
[dependencies]
collection_macro = "0.1"
```

We also show off how to bypass the [Orphan Rule](https://doc.rust-lang.org/reference/items/implementations.html#orphan-rules) to create incredibly versatile macros.

## Usage

These macros rely on type inference to determine the collection that they create.

The real power of these macros lies in the fact that work with absolutely any collection type, even collections from other crates.

### [`seq![]`](https://docs.rs/collection_macro/latest/collection_macro/macro.seq.html)

Takes a list of expressions, and creates a sequence like `Vec<T>` or `HashSet<T>`:

```rust
let seq: Vec<_> = seq![1, 2, 3];
```

You can use the array syntax `seq![expr; amount]`:

```rust
let seq: Vec<_> = seq![0; 10];
assert_eq!(seq, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
```

You can create non-empty sequences, like ones from the [`mitsein`](https://docs.rs/mitsein/latest/mitsein/) crate:

```rust
extern crate mitsein;

use collection_macro::{seq, Seq1Plus};
use mitsein::NonEmpty;

struct BypassOrphanRule;

// we usually can't implement external trait `Seq1Plus`
// for external struct `NonEmpty`,
// but because `BypassOrphanRule` is a local type, and it is
// inferred in the `seq!` macro, this works!
impl<T> Seq1Plus<BypassOrphanRule, T> for NonEmpty<Vec<T>> {
    fn from_1(first: T, capacity: usize) -> Self {
        NonEmpty::<Vec<T>>::from_one_with_capacity(first, capacity)
    }
    fn insert(&mut self, value: T) {
        self.push(value);
    }
}

// it just works!!
let seq: NonEmpty<Vec<_>> = seq![1, 2, 3];
assert_eq!(seq, NonEmpty::<Vec<_>>::from_head_and_tail(1, [2, 3]));
```

Non-empty sequences fail to compile if no arguments are provided:

```rust
let seq: NonEmpty<Vec<_>> = seq![];
```

**Traits:**

- If your type implements [`Seq0<T>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq0.html), then it can be used with `seq![]` syntax
- If your type implements [`Seq1Plus<T>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq1Plus.html), then it can be used with 1+ argument to: `seq![1, 2]`
- If your type implements **both** [`Seq0<T>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq0.html) and [`Seq1Plus<T>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq1Plus.html) then you can use the array syntax: `seq![0; 10]`

`seq!` can be used with these standard library types by default:

- `VecDeque`
- `Vec`
- `BTreeSet`
- `HashSet`

But you can use it with *any* struct, even the ones from external crates by implementing the traits [`Seq0`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq0.html) and [`Seq1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq1Plus.html).

**Tips:**

- For a sequence of 0 or more elements can such as `Vec<T>`, implement both [`Seq0`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq0.html) and [`Seq1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq1Plus.html)
- If your sequence is non-empty like `NonEmpty<Vec<T>>`, implement just [`Seq1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Seq1Plus.html) - then `seq![]` will be a compile error

### [`map! {}`](https://docs.rs/collection_macro/latest/collection_macro/macro.map.html)

Takes a list of `key => value` pairs, and creates a map like [`HashMap<K, V>`] or [`BTreeMap<K, V>`]:

```rust
let seq: HashMap<_, _> = map! {
    'A' => 0x41,
    'b' => 0x62,
    '!' => 0x21
};
assert_eq!(seq, HashMap::from([('A', 0x41), ('b', 0x62), ('!', 0x21)]));
```

**Traits:**

- If your type implements [`Map0<K, V>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map0.html), then it can be used with `map! {}` syntax
- If your type implements [`Map1Plus<K, V>`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map1Plus.html), then it can be used with 1+ argument to: `map! { 'A' => 0x41, 'b' => 0x62 }`

`map!` can be used with these standard library types by default:

- [`BTreeMap`]
- [`BTreeSet`]

But you can use it with *any* struct, even the ones from external crates by implementing the traits [`Map0`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map0.html) and [`Map1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map1Plus.html).

**Tips:**

- For a map of 0 or more `key => value` pairs can such as `HashMap<K, V>`, implement both [`Map0`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map0.html) and [`Map1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map1Plus.html)
- If your map is non-empty like `NonEmpty<HashMap<K, V>>`, implement just [`Map1Plus`](https://docs.rs/collection_macro/latest/collection_macro/trait.Map1Plus.html) - then `map! {}` will be a compile error

<!-- cargo-rdme end -->
