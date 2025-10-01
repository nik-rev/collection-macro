//! Collection Macros
//!
//! Provides the `seq!` and `map!` macros for easily initializing collections.

use core::cmp::Ord;
use core::hash::{BuildHasher, Hash};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[cfg(feature = "indexmap")]
use indexmap::{IndexMap, IndexSet};
#[cfg(feature = "mitsein")]
use mitsein::NonEmpty;

/// Trivially define maps like `HashMap` or `IndexMap`
#[macro_export]
macro_rules! map {
    // Specify type. Non-empty
    ($map:ty; $first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)?) => {{
        let capacity = $crate::__private_count!($first_key $($key)*);
        let mut map = <$map as $crate::Map1Plus<_, _>>::with_first_and_capacity(
            $first_key, $first_value, capacity
        );
        $(
            let _ = <$map as $crate::Map1Plus<_, _>>::insert(&mut map, $key, $value);
        )*
        map
    }};

    // Specify type. Empty.
    ($map:ty;) => { <$map as $crate::Map0<_, _>>::empty() };

    // Infer type. Non-empty
    ($first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)?) => {{
        // Count pairs by counting keys
        let capacity = $crate::__private_count!($first_key $($key)*);
        let mut map = <_ as $crate::Map1Plus<_, _>>::with_first_and_capacity(
            $first_key, $first_value, capacity
        );
        $(
            let _ = <_ as $crate::Map1Plus<_, _>>::insert(&mut map, $key, $value);
        )*
        map
    }};

    // Infer type. Empty
    () => { <_ as $crate::Map0<_, _>>::empty() };
}

/// Trivially define sequences like `Vec` or `HashSet`
#[macro_export]
macro_rules! seq {
    // Specify type. Non-empty
    ($seq:ty; $first:expr $(, $value:expr)* $(,)?) => {{
        let capacity = $crate::__private_count!(1 $($value)*);
        let mut seq = <$seq as $crate::Seq1Plus<_>>::with_capacity($first, capacity);
        $(
            <$seq as $crate::Seq1Plus<_>>::add(&mut seq, $value);
        )*
        seq
    }};

    // Specify type. Empty
    ($seq:ty;) => { <$seq as $crate::Seq0<_>>::empty() };

    // Specify type. Empty
    ($seq:ty; $value:expr; $amount:expr) => { <$seq as $crate::Seq<_>>::from_n($value, $amount) };

    // Infer type. Non-empty
    ($first:expr $(, $value:expr)* $(,)?) => {{
        // Count $first plus all subsequent $value tokens
        let capacity = $crate::__private_count!(1 $($value)*);
        let mut seq = <_ as $crate::Seq1Plus<_>>::with_capacity($first, capacity);
        $(
            // Use NonEmptySeq::add which must be implemented for all Seq types
            // (including those that are naturally non-empty).
            // This works because standard collections also implement NonEmptySeq
            // but the generated type will be the same (e.g., Vec<T>).
            // For mitsein types, this will call the NonEmptySeq impl.
            <_ as $crate::Seq1Plus<_>>::add(&mut seq, $value);
        )*
        seq
    }};

    // Infer type. Empty
    () => { <_ as $crate::Seq0<_>>::empty() };

    // Infer type. Empty
    ($value:expr; $amount:expr) => { <_ as $crate::Seq<_>>::from_n($value, $amount) };
}

/// Sequence that can be empty
pub trait Seq0<T> {
    /// Constructor for an empty collection.
    fn empty() -> Self;
}

/// Sequence that can have 1 or more elements
pub trait Seq1Plus<T> {
    /// Constructor with capacity, taking the first element.
    /// Capacity may be ignored for fixed-size collections.
    fn with_capacity(first: T, capacity: usize) -> Self;

    /// Add a subsequent element.
    fn add(&mut self, value: T);
}

/// Sequence. Allows using the `seq![value; amount]` syntax
///
/// Blanket implemented for types that implement both [`Seq0`] and [`Seq1Plus`]
pub trait Seq<T> {
    /// Create sequence with the specified number of elements
    fn from_n(value: T, n: usize) -> Self;
}

impl<T: Clone, S: Seq0<T> + Seq1Plus<T>> Seq<T> for S {
    fn from_n(value: T, n: usize) -> Self {
        if n == 0 {
            S::empty()
        } else {
            let mut seq = S::with_capacity(value.clone(), n);
            for _ in 1..n {
                seq.add(value.clone());
            }
            seq
        }
    }
}

/// Map that can be empty
pub trait Map0<K, V> {
    /// Constructor with capacity for non-empty or empty use.
    fn empty() -> Self;
}

/// Map that can have 1 or more elements
pub trait Map1Plus<K, V> {
    /// Constructor with capacity, taking the first key-value pair.
    fn with_first_and_capacity(first_key: K, first_value: V, capacity: usize) -> Self;

    /// Insert a key-value pair.
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

impl<T> Seq0<T> for std::vec::Vec<T> {
    fn empty() -> Self {
        std::vec::Vec::<T>::new()
    }
}

#[cfg(feature = "mitsein")]
impl<T> Seq1Plus<T> for NonEmpty<std::vec::Vec<T>> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        NonEmpty::<std::vec::Vec<T>>::from_one_with_capacity(first, capacity)
    }
    fn add(&mut self, value: T) {
        self.push(value);
    }
}

impl<T> Seq1Plus<T> for std::vec::Vec<T> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut vec = std::vec::Vec::with_capacity(capacity);
        vec.push(first);
        vec
    }
    fn add(&mut self, value: T) {
        self.push(value);
    }
}

impl<T> Seq0<T> for std::collections::VecDeque<T> {
    fn empty() -> Self {
        std::collections::VecDeque::<T>::new()
    }
}

impl<T> Seq1Plus<T> for std::collections::VecDeque<T> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut deque = std::collections::VecDeque::with_capacity(capacity);
        deque.push_back(first);
        deque
    }
    fn add(&mut self, value: T) {
        self.push_back(value);
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> Seq0<T> for std::collections::HashSet<T, S> {
    fn empty() -> Self {
        std::collections::HashSet::<T, S>::with_hasher(S::default())
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> Seq1Plus<T> for std::collections::HashSet<T, S> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut hashset =
            std::collections::HashSet::with_capacity_and_hasher(capacity, S::default());
        hashset.insert(first);
        hashset
    }
    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

impl<T: Ord> Seq0<T> for std::collections::BTreeSet<T> {
    fn empty() -> Self {
        std::collections::BTreeSet::<T>::new()
    }
}

impl<T: Ord> Seq1Plus<T> for std::collections::BTreeSet<T> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        std::collections::BTreeSet::from_iter([first])
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

#[cfg(feature = "mitsein")]
impl<T: Ord> Seq1Plus<T> for NonEmpty<BTreeSet<T>> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        NonEmpty::<BTreeSet<T>>::from_one(first)
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> Map0<K, V> for std::collections::HashMap<K, V, S> {
    fn empty() -> Self {
        std::collections::HashMap::<K, V, S>::with_hasher(S::default())
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> Map1Plus<K, V>
    for std::collections::HashMap<K, V, S>
{
    fn with_first_and_capacity(first_key: K, first_value: V, capacity: usize) -> Self {
        let mut map =
            std::collections::HashMap::<K, V, S>::with_capacity_and_hasher(capacity, S::default());
        map.insert(first_key, first_value);
        map
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

// NOTE: mitsein does not support `NonEmpty<HashMap>`

impl<K: Ord, V> Map0<K, V> for std::collections::BTreeMap<K, V> {
    fn empty() -> Self {
        std::collections::BTreeMap::<K, V>::new()
    }
}

impl<K: Ord, V> Map1Plus<K, V> for std::collections::BTreeMap<K, V> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        std::collections::BTreeMap::<K, V>::from_iter([(first_key, first_value)])
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "mitsein")]
impl<K: Ord, V> Map1Plus<K, V> for NonEmpty<BTreeMap<K, V>> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        NonEmpty::<BTreeMap<K, V>>::from_one((first_key, first_value))
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "indexmap")]
impl<T: Hash + Eq, S: Default + BuildHasher> Seq0<T> for indexmap::IndexSet<T, S> {
    fn empty() -> Self {
        indexmap::IndexSet::<T, S>::with_hasher(S::default())
    }
}

#[cfg(feature = "indexmap")]
impl<T: Hash + Eq, S: Default + BuildHasher> Seq1Plus<T> for indexmap::IndexSet<T, S> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut indexset = indexmap::IndexSet::with_capacity_and_hasher(capacity, S::default());
        indexset.insert(first);
        indexset
    }
    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

#[cfg(feature = "mitsein")]
#[cfg(feature = "indexmap")]
impl<T: Hash + Eq, S: Default + BuildHasher> Seq1Plus<T> for NonEmpty<IndexSet<T, S>> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        NonEmpty::<IndexSet<T, S>>::from_one_with_hasher(first, S::default())
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

#[cfg(feature = "indexmap")]
impl<K: Hash + Eq, V, S: Default + BuildHasher> Map0<K, V> for indexmap::IndexMap<K, V, S> {
    fn empty() -> Self {
        indexmap::IndexMap::<K, V, S>::with_hasher(S::default())
    }
}

#[cfg(feature = "indexmap")]
impl<K: Hash + Eq, V, S: Default + BuildHasher> Map1Plus<K, V> for indexmap::IndexMap<K, V, S> {
    fn with_first_and_capacity(first_key: K, first_value: V, capacity: usize) -> Self {
        let mut map =
            indexmap::IndexMap::<K, V, S>::with_capacity_and_hasher(capacity, S::default());
        map.insert(first_key, first_value);
        map
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "mitsein")]
#[cfg(feature = "indexmap")]
impl<K: Hash + Eq, V, S: Default + BuildHasher> Map1Plus<K, V> for NonEmpty<IndexMap<K, V, S>> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        NonEmpty::<IndexMap<K, V, S>>::from_one_with_hasher((first_key, first_value), S::default())
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "mitsein")]
impl<T> Seq1Plus<T> for NonEmpty<VecDeque<T>> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        NonEmpty::<VecDeque<T>>::from_one_with_capacity(first, capacity)
    }
    fn add(&mut self, value: T) {
        self.push_back(value);
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
    use crate::{__private_count, map, seq};
    use std::collections::{HashMap, HashSet};

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
        // Tests: ($map:ty; $first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)?)
        let map = map! { BTreeMap<&str, i32>; "a" => 1, "b" => 2, "c" => 3 };
        assert_eq!(map.len(), 3);
        assert!(map.contains_key("b"));
        let _: BTreeMap<&str, i32> = map;
    }

    #[test]
    fn map_explicit_non_empty_hashmap() {
        let map = map! { HashMap<i32, i32>; 1 => 10, 2 => 20 };
        assert_eq!(map.len(), 2);
        assert_eq!(map.get(&2), Some(&20));
    }

    #[test]
    fn map_explicit_empty() {
        // Tests: ($map:ty;)
        let map = map! { BTreeMap<u8, bool>; };
        assert!(map.is_empty());
        let _: BTreeMap<u8, bool> = map;
    }

    #[cfg(feature = "indexmap")]
    #[test]
    fn map_indexmap_non_empty() {
        let map = map! { IndexMap<&str, i32>; "a" => 1, "b" => 2 };
        assert_eq!(map.len(), 2);
        assert_eq!(map.get_index(0).unwrap().0, &"a");
    }

    #[cfg(feature = "indexmap")]
    #[test]
    fn map_indexmap_empty() {
        let map = map! { IndexMap<i32, i32>; };
        assert!(map.is_empty());
    }

    #[cfg(feature = "mitsein")]
    #[test]
    fn map_mitsein_btreemap_non_empty() {
        let map = map! { NonEmpty<BTreeMap<i32, i32>>; 5 => 50, 6 => 60 };
        assert_eq!(map.len().get(), 2);
        assert_eq!(map.get(&5), Some(&50));
    }

    #[cfg(all(feature = "mitsein", feature = "indexmap"))]
    #[test]
    fn map_mitsein_indexmap_non_empty() {
        let map = map! { NonEmpty<IndexMap<i32, i32>>; 1 => 10, 2 => 20 };
        assert_eq!(map.len().get(), 2);
    }

    #[test]
    fn seq_infer_non_empty() {
        let seq: Vec<_> = seq! { 10, 20, 30 };
        assert_eq!(seq, vec![10, 20, 30]);
    }

    #[test]
    fn seq_infer_non_empty_trailing_comma() {
        let seq: Vec<_> = seq! { "a", "b", };
        assert_eq!(seq, vec!["a", "b"]);
    }

    #[test]
    fn seq_infer_empty() {
        let seq: Vec<&str> = seq! {};
        assert!(seq.is_empty());
    }

    #[test]
    fn seq_infer_repeat() {
        let seq: Vec<i32> = seq! { 5; 3 };
        assert_eq!(seq, vec![5, 5, 5]);
    }

    #[test]
    fn seq_explicit_non_empty_vec() {
        let seq = seq! { Vec<f64>; 1.1, 2.2 };
        assert_eq!(seq.len(), 2);
    }

    #[test]
    fn seq_explicit_non_empty_btreeset() {
        let set = seq! { BTreeSet<i32>; 5, 1, 3 };
        assert_eq!(set.len(), 3);
        assert_eq!(set.into_iter().collect::<Vec<_>>(), vec![1, 3, 5]); // BTreeSet orders
    }

    #[test]
    fn seq_explicit_non_empty_hashset() {
        let set = seq! { HashSet<i32>; 5, 1, 5 };
        assert_eq!(set.len(), 2);
        assert!(set.contains(&1));
    }

    #[test]
    fn seq_explicit_non_empty_vecdeque() {
        let deque = seq! { VecDeque<i32>; 1, 2, 3 };
        assert_eq!(deque.front(), Some(&1));
    }

    #[test]
    fn seq_explicit_empty() {
        let seq = seq! { BTreeSet<u8>; };
        assert!(seq.is_empty());
    }

    #[test]
    fn seq_explicit_repeat_non_empty() {
        // Tests: ($seq:ty; $value:expr; $amount:expr)
        let seq = seq! { VecDeque<char>; 'x'; 2 };
        assert_eq!(seq, VecDeque::from(vec!['x', 'x']));
    }

    #[test]
    fn seq_explicit_repeat_empty() {
        let seq = seq! { Vec<i32>; 10; 0 };
        assert!(seq.is_empty());
    }

    #[cfg(feature = "indexmap")]
    #[test]
    fn seq_indexset_non_empty() {
        let set = seq! { IndexSet<i32>; 1, 3, 2, 3 };
        assert_eq!(set.len(), 3);
        assert!(set.contains(&3));
    }

    #[cfg(feature = "indexmap")]
    #[test]
    fn seq_indexset_empty() {
        let set = seq! { IndexSet<i32>; };
        assert!(set.is_empty());
    }

    #[cfg(feature = "mitsein")]
    #[test]
    fn seq_mitsein_vec_non_empty() {
        let seq = seq! { NonEmpty<Vec<i32>>; 1, 2 };
        assert_eq!(seq.len().get(), 2);
        assert_eq!(*seq.first(), 1);
    }

    #[cfg(feature = "mitsein")]
    #[test]
    fn seq_mitsein_btreeset_non_empty() {
        let seq = seq! { NonEmpty<BTreeSet<i32>>; 3, 1 };
        assert_eq!(seq.len().get(), 2);
        assert!(seq.contains(&1));
    }

    #[allow(unused_mut)]
    #[cfg(feature = "mitsein")]
    #[test]
    fn seq_mitsein_vecdeque_non_empty() {
        let seq = seq! { NonEmpty<VecDeque<i32>>; 10 };
        assert_eq!(seq.len().get(), 1);
    }

    #[cfg(all(feature = "mitsein", feature = "indexmap"))]
    #[test]
    fn seq_mitsein_indexset_non_empty() {
        let set = seq! { NonEmpty<IndexSet<i32>>; 1, 2 };
        assert_eq!(set.len().get(), 2);
    }
}
