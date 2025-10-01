//! Collection Macros
//!
//! Provides the `seq!` and `map!` macros for easily initializing collections.

use core::cmp::Ord;
use core::hash::{BuildHasher, Hash};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use indexmap::{IndexMap, IndexSet};
#[cfg(feature = "mitsein")]
use mitsein::NonEmpty;

/// Trivially define maps like `HashMap` or `IndexMap`
#[macro_export]
macro_rules! map {
    // Specify type. Non-empty
    ($map:ty; $first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)?) => {{
        let capacity = $crate::__private_count!($first_key $($key)*);
        let mut map = <$map as $crate::NonEmptyMap<_, _>>::with_first_and_capacity(
            $first_key, $first_value, capacity
        );
        $(
            let _ = <$map as $crate::NonEmptyMap<_, _>>::insert(&mut map, $key, $value);
        )*
        map
    }};

    // Specify type. Empty.
    ($map:ty;) => { <$map as $crate::Map<_, _>>::new() };

    // Infer type. Non-empty
    ($first_key:expr => $first_value:expr $(, $key:expr => $value:expr)* $(,)?) => {{
        // Count pairs by counting keys
        let capacity = $crate::__private_count!($first_key $($key)*);
        let mut map = <_ as $crate::NonEmptyMap<_, _>>::with_first_and_capacity(
            $first_key, $first_value, capacity
        );
        $(
            let _ = <_ as $crate::NonEmptyMap<_, _>>::insert(&mut map, $key, $value);
        )*
        map
    }};

    // Infer type. Empty
    () => { <_ as $crate::Map<_, _>>::new() };
}

/// Trivially define sequences like `Vec` or `HashSet`
#[macro_export]
macro_rules! seq {
    // Specify type. Non-empty
    ($seq:ty; $first:expr $(, $value:expr)* $(,)?) => {{
        let capacity = $crate::__private_count!(1 $($value)*);
        let mut seq = <$seq as $crate::NonEmptySeq<_>>::with_capacity($first, capacity);
        $(
            <$seq as $crate::NonEmptySeq<_>>::add(&mut seq, $value);
        )*
        seq
    }};

    // Specify type. Empty
    ($seq:ty;) => { <$seq as $crate::Seq<_>>::new() };

    // Infer type. Non-empty
    ($first:expr $(, $value:expr)* $(,)?) => {{
        // Count $first plus all subsequent $value tokens
        let capacity = $crate::__private_count!(1 $($value)*);
        let mut seq = <_ as $crate::NonEmptySeq<_>>::with_capacity($first, capacity);
        $(
            // Use NonEmptySeq::add which must be implemented for all Seq types
            // (including those that are naturally non-empty).
            // This works because standard collections also implement NonEmptySeq
            // but the generated type will be the same (e.g., Vec<T>).
            // For mitsein types, this will call the NonEmptySeq impl.
            <_ as $crate::NonEmptySeq<_>>::add(&mut seq, $value);
        )*
        seq
    }};

    // Infer type. Empty
    () => { <_ as $crate::Seq<_>>::new() };
}

/// # Traits for Sequences
///
/// Types implementing this trait can be used with empty `seq![]`
pub trait Seq<T> {
    /// Constructor for an empty collection.
    fn new() -> Self;
}

/// Non-empty sequence trait
pub trait NonEmptySeq<T> {
    /// Constructor with capacity, taking the first element.
    /// Capacity may be ignored for fixed-size collections.
    fn with_capacity(first: T, capacity: usize) -> Self;

    /// Add a subsequent element.
    fn add(&mut self, value: T);
}

/// # Traits for Maps
///
/// Types implementing this trait can be used with empty and non-empty `map! {}`
pub trait Map<K, V> {
    /// Constructor with capacity for non-empty or empty use.
    fn new() -> Self;
}

/// Non-empty map trait
///
/// This trait is necessary to enable the use of `mitsein`'s non-empty map types.
pub trait NonEmptyMap<K, V> {
    /// Constructor with capacity, taking the first key-value pair.
    fn with_first_and_capacity(first_key: K, first_value: V, capacity: usize) -> Self;

    /// Insert a key-value pair.
    fn insert(&mut self, key: K, value: V) -> Option<V>;
}

impl<T> Seq<T> for std::vec::Vec<T> {
    fn new() -> Self {
        std::vec::Vec::<T>::new()
    }
}

#[cfg(feature = "mitsein")]
impl<T> NonEmptySeq<T> for NonEmpty<std::vec::Vec<T>> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        NonEmpty::<std::vec::Vec<T>>::from_one_with_capacity(first, capacity)
    }
    fn add(&mut self, value: T) {
        self.push(value);
    }
}

impl<T> NonEmptySeq<T> for std::vec::Vec<T> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut vec = std::vec::Vec::with_capacity(capacity);
        vec.push(first);
        vec
    }
    fn add(&mut self, value: T) {
        self.push(value);
    }
}

impl<T> Seq<T> for std::collections::VecDeque<T> {
    fn new() -> Self {
        std::collections::VecDeque::<T>::new()
    }
}

impl<T> NonEmptySeq<T> for std::collections::VecDeque<T> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        let mut deque = std::collections::VecDeque::with_capacity(capacity);
        deque.push_back(first);
        deque
    }
    fn add(&mut self, value: T) {
        self.push_back(value);
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> Seq<T> for std::collections::HashSet<T, S> {
    fn new() -> Self {
        std::collections::HashSet::<T, S>::with_hasher(S::default())
    }
}

impl<T: Hash + Eq, S: Default + BuildHasher> NonEmptySeq<T> for std::collections::HashSet<T, S> {
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

impl<T: Ord> Seq<T> for std::collections::BTreeSet<T> {
    fn new() -> Self {
        std::collections::BTreeSet::<T>::new()
    }
}

impl<T: Ord> NonEmptySeq<T> for std::collections::BTreeSet<T> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        std::collections::BTreeSet::from_iter([first])
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

#[cfg(feature = "mitsein")]
impl<T: Ord> NonEmptySeq<T> for NonEmpty<BTreeSet<T>> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        NonEmpty::<BTreeSet<T>>::from_one(first)
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> Map<K, V> for std::collections::HashMap<K, V, S> {
    fn new() -> Self {
        std::collections::HashMap::<K, V, S>::with_hasher(S::default())
    }
}

impl<K: Hash + Eq, V, S: Default + BuildHasher> NonEmptyMap<K, V>
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

impl<K: Ord, V> Map<K, V> for std::collections::BTreeMap<K, V> {
    fn new() -> Self {
        std::collections::BTreeMap::<K, V>::new()
    }
}

impl<K: Ord, V> NonEmptyMap<K, V> for std::collections::BTreeMap<K, V> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        std::collections::BTreeMap::<K, V>::from_iter([(first_key, first_value)])
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "mitsein")]
impl<K: Ord, V> NonEmptyMap<K, V> for NonEmpty<BTreeMap<K, V>> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        NonEmpty::<BTreeMap<K, V>>::from_one((first_key, first_value))
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "indexmap")]
impl<T: Hash + Eq, S: Default + BuildHasher> Seq<T> for indexmap::IndexSet<T, S> {
    fn new() -> Self {
        indexmap::IndexSet::<T, S>::with_hasher(S::default())
    }
}

#[cfg(feature = "indexmap")]
impl<T: Hash + Eq, S: Default + BuildHasher> NonEmptySeq<T> for indexmap::IndexSet<T, S> {
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
impl<T: Hash + Eq, S: Default + BuildHasher> NonEmptySeq<T> for NonEmpty<IndexSet<T, S>> {
    fn with_capacity(first: T, _capacity: usize) -> Self {
        NonEmpty::<IndexSet<T, S>>::from_one_with_hasher(first, S::default())
    }

    fn add(&mut self, value: T) {
        self.insert(value);
    }
}

#[cfg(feature = "indexmap")]
impl<K: Hash + Eq, V, S: Default + BuildHasher> Map<K, V> for indexmap::IndexMap<K, V, S> {
    fn new() -> Self {
        indexmap::IndexMap::<K, V, S>::with_hasher(S::default())
    }
}

#[cfg(feature = "indexmap")]
impl<K: Hash + Eq, V, S: Default + BuildHasher> NonEmptyMap<K, V> for indexmap::IndexMap<K, V, S> {
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
impl<K: Hash + Eq, V, S: Default + BuildHasher> NonEmptyMap<K, V> for NonEmpty<IndexMap<K, V, S>> {
    fn with_first_and_capacity(first_key: K, first_value: V, _capacity: usize) -> Self {
        NonEmpty::<IndexMap<K, V, S>>::from_one_with_hasher((first_key, first_value), S::default())
    }
    fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.insert(key, value)
    }
}

#[cfg(feature = "mitsein")]
impl<T> NonEmptySeq<T> for NonEmpty<VecDeque<T>> {
    fn with_capacity(first: T, capacity: usize) -> Self {
        NonEmpty::<VecDeque<T>>::from_one_with_capacity(first, capacity)
    }
    fn add(&mut self, value: T) {
        self.push_back(value);
    }
}

/// Counts how many tokens there are
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
    use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

    // --- SEQ TESTS (Your existing tests plus new ones) ---

    #[test]
    fn vec_seq_macro_non_empty() {
        let v: std::vec::Vec<_> = seq![1, 2, 3];
        assert_eq!(v, vec![1, 2, 3]);
        assert_eq!(v.capacity(), 3);
    }

    #[test]
    fn vec_seq_macro_empty() {
        let v: std::vec::Vec<i32> = seq![Vec<i32>;];
        assert_eq!(v.len(), 0);
    }

    #[test]
    fn vec_deque_seq_macro_non_empty() {
        let d: std::collections::VecDeque<i32> = seq![4, 5, 6];
        assert_eq!(d.iter().copied().collect::<Vec<_>>(), vec![4, 5, 6]);
    }

    #[test]
    fn hashset_seq_macro() {
        let hs = seq![HashSet<_>; 1, 2, 3, 3];
        assert_eq!(hs.len(), 3);
        assert!(hs.contains(&1));
    }

    #[test]
    fn btreeset_seq_macro() {
        let bs = seq![BTreeSet::<_>; 3, 1, 2, 2];
        let collected: Vec<_> = bs.iter().copied().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    #[cfg(feature = "indexmap")]
    fn indexset_seq_macro() {
        let is = seq![indexmap::IndexSet::<&str>; "a", "b", "c", "b"];
        let collected: Vec<_> = is.iter().copied().collect();
        assert_eq!(collected, vec!["a", "b", "c"]);
    }

    // --- MAP TESTS (Updated to use Map/NonEmptyMap) ---

    #[test]
    fn hashmap_macro_inferred() {
        let hm: HashMap<_, _> = map![1 => "one", 2 => "two", 3 => "three"];
        // Type is inferred as std::collections::HashMap<i32, &str, RandomState>
        assert_eq!(hm.len(), 3);
        assert_eq!(hm.get(&1), Some(&"one"));
        // Capacity check is tricky due to hash collision, but should be at least 3
    }

    #[test]
    fn hashmap_macro_specified() {
        let hm = map![HashMap<i32, &str>; 1 => "one", 2 => "two", 3 => "three"];
        assert_eq!(hm.len(), 3);
        assert_eq!(hm.get(&2), Some(&"two"));
    }

    #[test]
    fn hashmap_macro_empty_specified() {
        let hm: HashMap<i32, &str> = map![HashMap<i32, &str>;];
        assert_eq!(hm.len(), 0);
        assert_eq!(hm.capacity(), 0);
    }

    #[test]
    fn btreemap_macro_non_empty() {
        let bm = map![BTreeMap::<_, _>; 3 => "c", 1 => "a", 2 => "b"];
        let keys: Vec<_> = bm.keys().copied().collect();
        assert_eq!(keys, vec![1, 2, 3]); // BTreeMap keeps sorted order
    }

    #[test]
    fn btreemap_macro_overwrite() {
        let bm = map![BTreeMap<_, _>; 1 => "one", 1 => "uno"];
        assert_eq!(bm.len(), 1);
        assert_eq!(bm.get(&1), Some(&"uno")); // last insert wins
    }

    #[test]
    #[cfg(feature = "indexmap")]
    fn indexmap_macro_order() {
        let im = map![indexmap::IndexMap<_, _>; 3 => "c", 1 => "a", 2 => "b"];
        let keys: Vec<_> = im.keys().copied().collect();
        // IndexMap preserves insertion order
        assert_eq!(keys, vec![3, 1, 2]);
    }

    // --- MITSEIN TESTS ---
    #[test]
    #[cfg(feature = "mitsein")]
    fn mitsein_vec1_seq() {
        let v: NonEmpty<Vec<i32>> = seq![NonEmpty<Vec<i32>>; 10, 20];
        assert_eq!(v.len().get(), 2);
        assert_eq!(v.first(), &10);
    }

    #[test]
    #[cfg(feature = "mitsein")]
    fn mitsein_btree_map1() {
        let bm1: NonEmpty<BTreeMap<i32, &str>> =
            map![NonEmpty::<BTreeMap<i32, &str>>; 1 => "one", 2 => "two"];
        assert_eq!(bm1.len().get(), 2);
        assert_eq!(bm1.get(&1), Some(&"one"));
    }

    #[test]
    #[cfg(feature = "mitsein")]
    fn mitsein_index_map1() {
        let im1: NonEmpty<IndexMap<i32, &str>> =
            map![NonEmpty::<IndexMap<i32, &str>>; 5 => "five", 1 => "one"];
        assert_eq!(im1.len().get(), 2);
        let keys: Vec<_> = im1.keys1().copied().into_iter().collect();
        // Preserves order
        assert_eq!(keys, vec![5, 1]);
    }
}
