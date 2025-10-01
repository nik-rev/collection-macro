//! [![crates.io](https://img.shields.io/crates/v/collection_macro?style=flat-square&logo=rust)](https://crates.io/crates/collection_macro)
//! [![docs.rs](https://img.shields.io/badge/docs.rs-collection_macro-blue?style=flat-square&logo=docs.rs)](https://docs.rs/collection_macro)
//! ![license](https://img.shields.io/badge/license-Apache--2.0_OR_MIT-blue?style=flat-square)
//! ![msrv](https://img.shields.io/badge/msrv-1.60-blue?style=flat-square&logo=rust)
//! [![github](https://img.shields.io/github/stars/nik-rev/collection-macro)](https://github.com/nik-rev/collection-macro)
//!
//! This crate provides the general-purpose [`seq![]`](seq) and [`map! {}`](map) macros.
//!
//! ```toml
//! [dependencies]
//! collection_macro = "0.1"
//! ```
//!
//! We also show off how to bypass the [Orphan Rule](https://doc.rust-lang.org/reference/items/implementations.html#orphan-rules) to create incredibly versatile macros.
//!
//! # Usage
//!
//! These macros rely on type inference to determine the collection that they create.
//!
//! The real power of these macros lies in the fact that work with absolutely any collection type, even collections from other crates.
//!
//! ## [`seq![]`](seq)
//!
//! Takes a list of expressions, and creates a sequence like [`Vec<T>`](Vec) or [`HashSet<T>`](HashSet):
//!
//! ```rust
//! # use collection_macro::seq;
//! let seq: Vec<_> = seq![1, 2, 3];
//! ```
//!
//! You can use the array syntax `seq![expr; amount]`:
//!
//! ```rust
//! # use collection_macro::seq;
//! let seq: Vec<_> = seq![0; 10];
//! assert_eq!(seq, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
//! ```
//!
//! You can create non-empty sequences, like ones from the [`mitsein`](https://docs.rs/mitsein/latest/mitsein/) crate:
//!
//! ```rust
//! extern crate mitsein;
//!
//! use collection_macro::{seq, Seq1Plus};
//! use mitsein::NonEmpty;
//!
//! struct BypassOrphanRule;
//!
//! // we usually can't implement external trait `Seq1Plus`
//! // for external struct `NonEmpty`,
//! // but because `BypassOrphanRule` is a local type, and it is
//! // inferred in the `seq!` macro, this works!
//! impl<T> Seq1Plus<BypassOrphanRule, T> for NonEmpty<Vec<T>> {
//!     fn from_1(first: T, capacity: usize) -> Self {
//!         NonEmpty::<Vec<T>>::from_one_with_capacity(first, capacity)
//!     }
//!     fn insert(&mut self, value: T) {
//!         self.push(value);
//!     }
//! }
//!
//! // it just works!!
//! let seq: NonEmpty<Vec<_>> = seq![1, 2, 3];
//! assert_eq!(seq, NonEmpty::<Vec<_>>::from_head_and_tail(1, [2, 3]));
//! ```
//!
//! Non-empty sequences fail to compile if no arguments are provided:
//!
//! ```rust,compile_fail
//! let seq: NonEmpty<Vec<_>> = seq![];
//! ```
//!
//! **Traits:**
//!
//! - If your type implements [`Seq0<T>`](crate::Seq0), then it can be used with `seq![]` syntax
//! - If your type implements [`Seq1Plus<T>`](crate::Seq1Plus), then it can be used with 1+ argument to: `seq![1, 2]`
//! - If your type implements **both** [`Seq0<T>`](crate::Seq0) and [`Seq1Plus<T>`](crate::Seq1Plus) then you can use the array syntax: `seq![0; 10]`
//!
//! `seq!` can be used with these standard library types by default:
//!
//! - [`VecDeque`](VecDeque)
//! - [`Vec`](Vec)
//! - [`BTreeSet`](BTreeSet)
//! - [`HashSet`](HashSet)
//!
//! But you can use it with *any* struct, even the ones from external crates by implementing the traits [`Seq0`](crate::Seq0) and [`Seq1Plus`](crate::Seq1Plus).
//!
//! **Tips:**
//!
//! - For a sequence of 0 or more elements can such as [`Vec<T>`](Vec), implement both [`Seq0`](Seq0) and [`Seq1Plus`](Seq1Plus)
//! - If your sequence is non-empty like `NonEmpty<Vec<T>>`, implement just [`Seq1Plus`](Seq1Plus) - then `seq![]` will be a compile error
//!
//! ## [`map! {}`](map)
//!
//! Takes a list of `key => value` pairs, and creates a map like [`HashMap<K, V>`](HashMap) or [`BTreeMap<K, V>`](BTreeMap):
//!
//! ```rust
//! # use collection_macro::map;
//! # use std::collections::HashMap;
//! let seq: HashMap<_, _> = map! {
//!     'A' => 0x41,
//!     'b' => 0x62,
//!     '!' => 0x21
//! };
//! assert_eq!(seq, HashMap::from([('A', 0x41), ('b', 0x62), ('!', 0x21)]));
//! ```
//!
//! **Traits:**
//!
//! - If your type implements [`Map0<K, V>`], then it can be used with `map! {}` syntax
//! - If your type implements [`Map1Plus<K, V>`], then it can be used with 1+ argument to: `map! { 'A' => 0x41, 'b' => 0x62 }`
//!
//! `map!` can be used with these standard library types by default:
//!
//! - [`BTreeMap`](BTreeMap)
//! - [`BTreeSet`](BTreeSet)
//!
//! But you can use it with *any* struct, even the ones from external crates by implementing the traits [`Map0`] and [`Map1Plus`].
//!
//! **Tips:**
//!
//! - For a map of 0 or more `key => value` pairs can such as [`HashMap<K, V>`](HashMap), implement both [`Map0`] and [`Map1Plus`]
//! - If your map is non-empty like `NonEmpty<HashMap<K, V>>`, implement just [`Map1Plus`] - then `map! {}` will be a compile error

use core::cmp::Ord;
use core::hash::{BuildHasher, Hash};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};

/// General-purpose macro for creating a map with keys pointing to values
///
/// ```rust
/// # use collection_macro::map;
/// let map: std::collections::HashMap<_, _> = map! {
///     1 => 2,
///     2 => 3,
///     3 => 4
/// };
/// ```
///
/// `map! {}` relies on type inference to determine which map to become.
///
/// See the [crate-level](crate) documentation for more info.
#[macro_export]
macro_rules! map {
    // Non-empty
    { $first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)? } => {{
        let capacity = $crate::__private_count!($first_key $($key)*);
        let mut map = <_ as $crate::Map1Plus<_, _, _>>::from_1(
            $first_key, $first_value, capacity
        );
        $(
            let _ = <_ as $crate::Map1Plus<_, _, _>>::insert(&mut map, $key, $value);
        )*
        map
    }};

    // Empty
    {} => { <_ as $crate::Map0<_, _, _>>::empty() };
}

/// General-purpose macro for creating a sequence of items
///
/// ```rust
/// # use collection_macro::seq;
/// let seq: Vec<_> = seq![1, 2, 3];
/// assert_eq!(seq, vec![1, 2, 3]);
/// ```
///
/// `seq![]` relies on type inference to determine which sequence to become.
///
/// See the [crate-level](crate) documentation for more info.
#[macro_export]
macro_rules! seq {
    // Non-empty
    [$first:expr $(, $value:expr)* $(,)?] => {{
        // Count $first plus all subsequent $value tokens
        let capacity = $crate::__private_count!(1 $($value)*);
        let mut seq = <_ as $crate::Seq1Plus<_, _>>::from_1($first, capacity);
        $(
            // Use NonEmptySeq::add which must be implemented for all Seq types
            // (including those that are naturally non-empty).
            // This works because standard collections also implement NonEmptySeq
            // but the generated type will be the same (e.g., Vec<T>).
            // For mitsein types, this will call the NonEmptySeq impl.
            <_ as $crate::Seq1Plus<_, _>>::insert(&mut seq, $value);
        )*
        seq
    }};

    // Empty
    [] => { <_ as $crate::Seq0<_, _>>::empty() };

    // Specific amount
    [$value:expr; $amount:expr] => { <_ as $crate::Seq<_, _>>::from_n($value, $amount) };
}

/// Sequence that can be empty. Unlocks: `seq![]`
pub trait Seq0<BypassOrphanRule, T> {
    /// Create an empty sequence
    fn empty() -> Self;
}

/// Sequence that can have 1 or more elements. Unlocks: `seq![1]`
pub trait Seq1Plus<BypassOrphanRule, T> {
    /// Create a sequence with the first `element` and the specified `capacity`
    ///
    /// Not all sequences support `capacity`, so it may be ignored
    fn from_1(element: T, capacity: usize) -> Self;

    /// Insert an element into the sequence
    fn insert(&mut self, element: T);
}

/// Map that can be empty. Unlocks: `map! {}`
pub trait Map0<BypassOrphanRule, K, V> {
    /// Constructor with capacity for non-empty or empty use.
    fn empty() -> Self;
}

/// Map that can have 1 or more elements. Unlocks: `map! { a => b }`
pub trait Map1Plus<BypassOrphanRule, K, V> {
    /// Create a map with the first `key => value` pair and the specified `capacity`
    ///
    /// Not all sequences support `capacity`, so it may be ignored
    fn from_1(key: K, value: V, capacity: usize) -> Self;

    /// Insert a `key => value` pair into the map
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

impl<T> Seq0<(), T> for std::vec::Vec<T> {
    fn empty() -> Self {
        std::vec::Vec::<T>::new()
    }
}

/// Sequence. Unlocks: `seq![value; amount]`
///
/// Do not implement this trait. Instead, implement both [`Seq0`] and [`Seq1Plus`]
/// to get `Seq` for free
#[doc(hidden)]
pub trait Seq<BypassOrphanRule, T> {
    /// Create sequence with the specified number of elements
    fn from_n(value: T, n: usize) -> Self;
}

impl<BypassOrphanRule, T: Clone, S: Seq0<BypassOrphanRule, T> + Seq1Plus<BypassOrphanRule, T>>
    Seq<BypassOrphanRule, T> for S
{
    fn from_n(value: T, n: usize) -> Self {
        if n == 0 {
            S::empty()
        } else {
            let mut seq = S::from_1(value.clone(), n);
            for _ in 1..n {
                seq.insert(value.clone());
            }
            seq
        }
    }
}

impl<T> Seq1Plus<(), T> for std::vec::Vec<T> {
    fn from_1(first: T, capacity: usize) -> Self {
        let mut vec = std::vec::Vec::with_capacity(capacity);
        vec.push(first);
        vec
    }
    fn insert(&mut self, value: T) {
        self.push(value);
    }
}

impl<T> Seq0<(), T> for VecDeque<T> {
    fn empty() -> Self {
        VecDeque::<T>::new()
    }
}

impl<T> Seq1Plus<(), T> for VecDeque<T> {
    fn from_1(first: T, capacity: usize) -> Self {
        let mut deque = VecDeque::with_capacity(capacity);
        deque.push_back(first);
        deque
    }
    fn insert(&mut self, value: T) {
        self.push_back(value);
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> Seq0<(), T> for HashSet<T, S> {
    fn empty() -> Self {
        HashSet::<T, S>::with_hasher(S::default())
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> Seq1Plus<(), T> for HashSet<T, S> {
    fn from_1(first: T, capacity: usize) -> Self {
        let mut hashset = HashSet::with_capacity_and_hasher(capacity, S::default());
        hashset.insert(first);
        hashset
    }
    fn insert(&mut self, value: T) {
        self.insert(value);
    }
}

impl<T: Ord> Seq0<(), T> for BTreeSet<T> {
    fn empty() -> Self {
        BTreeSet::<T>::new()
    }
}

impl<T: Ord> Seq1Plus<(), T> for BTreeSet<T> {
    fn from_1(first: T, _capacity: usize) -> Self {
        BTreeSet::from_iter([first])
    }

    fn insert(&mut self, value: T) {
        self.insert(value);
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> Map0<(), K, V> for HashMap<K, V, S> {
    fn empty() -> Self {
        HashMap::<K, V, S>::with_hasher(S::default())
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> Map1Plus<(), K, V> for HashMap<K, V, S> {
    fn from_1(first_key: K, first_value: V, capacity: usize) -> Self {
        let mut map = HashMap::<K, V, S>::with_capacity_and_hasher(capacity, S::default());
        map.insert(first_key, first_value);
        map
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

impl<K: Ord, V> Map0<(), K, V> for BTreeMap<K, V> {
    fn empty() -> Self {
        BTreeMap::<K, V>::new()
    }
}

impl<K: Ord, V> Map1Plus<(), K, V> for BTreeMap<K, V> {
    fn from_1(first_key: K, first_value: V, _capacity: usize) -> Self {
        BTreeMap::<K, V>::from_iter([(first_key, first_value)])
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

/// Counts how many tokens there are. **Not public API.**
///
/// From <https://lukaswirth.dev/tlborm/decl-macros/building-blocks/counting.html#bit-twiddling>
#[doc(hidden)]
#[macro_export]
macro_rules! __private_count {
    () => { 0 };
    ($odd:tt $($a:tt $b:tt)*) => { ($crate::__private_count!($($a)*) << 1) | 1 };
    ($($a:tt $even:tt)*) => { $crate::__private_count!($($a)*) << 1 };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_private_count() {
        assert_eq!(__private_count!(), 0);
        assert_eq!(__private_count!(a), 1);
        assert_eq!(__private_count!(a b c d e), 5,);
        assert_eq!(__private_count!(1 2 3 4 5 6 7 8), 8,);
    }

    #[test]
    fn map_infer_non_empty() {
        let map: HashMap<i32, &'static str> = map! { 1 => "one", 2 => "two" };
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&1), Some(&"one"));
    }

    #[test]
    fn map_infer_non_empty_trailing_comma() {
        let map: HashMap<char, i32> = map! { 'a' => 1, 'b' => 2, };
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn map_infer_empty() {
        let map: HashMap<i32, i32> = map! {};
        assert!(map.is_empty());
    }

    #[test]
    fn map_explicit_non_empty_btreemap() {
        let map: BTreeMap<&str, i32> = map! { "a" => 1, "b" => 2, "c" => 3 };
        assert_eq!(map.len(), 3);
        assert!(map.contains_key("b"));
    }

    #[test]
    fn map_explicit_non_empty_hashmap() {
        let map: HashMap<i32, i32> = map! { 1 => 10, 2 => 20 };
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&2), Some(&20));
    }

    #[test]
    fn map_explicit_empty() {
        let map: BTreeMap<u8, bool> = map! {};
        assert!(map.is_empty());
    }

    #[test]
    fn seq_infer_non_empty() {
        let seq: Vec<_> = seq![10, 20, 30];
        assert_eq!(seq, vec![10, 20, 30]);
    }

    #[test]
    fn seq_infer_non_empty_trailing_comma() {
        let seq: Vec<_> = seq!["a", "b",];
        assert_eq!(seq, vec!["a", "b"]);
    }

    #[test]
    fn seq_infer_empty() {
        let seq: Vec<&str> = seq![];
        assert!(seq.is_empty());
    }

    #[test]
    fn seq_infer_repeat() {
        let seq: Vec<i32> = seq![5; 3];
        assert_eq!(seq, vec![5, 5, 5]);
    }

    #[test]
    fn seq_explicit_non_empty_vec() {
        let seq: Vec<f64> = seq![1.1, 2.2];
        assert_eq!(seq.len(), 2);
    }

    #[test]
    fn seq_explicit_non_empty_btreeset() {
        let set: BTreeSet<i32> = seq![5, 1, 3];
        assert_eq!(set.len(), 3);
        assert_eq!(set.into_iter().collect::<Vec<_>>(), vec![1, 3, 5]);
    }

    #[test]
    fn seq_explicit_non_empty_hashset() {
        let set: HashSet<i32> = seq![5, 1, 5];
        assert_eq!(set.len(), 2);
        assert!(set.contains(&1));
    }

    #[test]
    fn seq_explicit_non_empty_vecdeque() {
        let deque: VecDeque<i32> = seq![1, 2, 3];
        assert_eq!(deque.front(), Some(&1));
    }

    #[test]
    fn seq_explicit_empty() {
        let seq: BTreeSet<u8> = seq![];
        assert!(seq.is_empty());
    }

    #[test]
    fn seq_explicit_repeat_non_empty() {
        let seq: VecDeque<char> = seq!['x'; 2];
        assert_eq!(seq, VecDeque::from(vec!['x', 'x']));
    }

    #[test]
    fn seq_explicit_repeat_empty() {
        let seq: Vec<i32> = seq![10; 0];
        assert!(seq.is_empty());
    }
}
