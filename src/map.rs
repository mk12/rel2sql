/// Hash map data structure.

use std::collections::{hash_map, HashMap};
use std::fmt;
use std::hash::Hash;

/// A hash map that remembers insertion order.
///
/// To simplify the implementation, the key type `K` is required to be `Copy`.
/// This makes it easier to store in both the vector and the map without
/// worrying about references or cloning.
pub struct OrderMap<K, V> {
    /// Index of the next entry to be inserted.
    index: usize,
    /// The underlying hash map.
    map: HashMap<K, Value<V>>,
}

/// A wrapper type for storing the insertion index.
#[derive(Debug, PartialEq, Eq)]
pub struct Value<V> {
    /// Index of the value.
    index: usize,
    /// The actual value.
    value: V,
}

/// A set view of the keys of an `OrderMap`.
pub struct KeySet<'a, K: 'a, V: 'a>(&'a OrderMap<K, V>);

impl<K, V> PartialEq for OrderMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &OrderMap<K, V>) -> bool {
        self.index == other.index && self.map == other.map
    }
}

impl<K, V> Eq for OrderMap<K, V>
where
    K: Eq + Hash,
    V: Eq,
{
}

impl<K, V> fmt::Debug for OrderMap<K, V>
where
    K: Eq + Hash + fmt::Debug,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "OrderMap {{ index: {:?}, map: {:?} }}",
            self.index, self.map
        )
    }
}

impl<K, V> OrderMap<K, V>
where
    K: Eq + Hash + Copy,
{
    /// Creates a new `OrderMap`.
    pub fn new() -> OrderMap<K, V> {
        OrderMap {
            index: 0,
            map: HashMap::new(),
        }
    }

    /// Checks if the map contains a key.
    pub fn contains(&self, k: K) -> bool {
        self.map.contains_key(&k)
    }

    /// Gets a value from the map by key.
    pub fn get(&self, k: K) -> Option<&V> {
        self.map.get(&k).map(|v| &v.value)
    }

    ///
    pub fn get_indexed(&self, k: K) -> Option<(usize, &V)> {
        self.map.get(&k).map(|v| (v.index, &v.value))
    }

    /// Returns an iterator over the keys of the map.
    pub fn keys(&self) -> hash_map::Keys<K, Value<V>> {
        self.map.keys()
    }

    /// Returns a view of the map's keys, as a set.
    pub fn key_set(&self) -> KeySet<K, V> {
        KeySet(&self)
    }

    /// Inserts an entry into the map.
    pub fn insert<T>(&mut self, k: K, v: T)
    where
        T: Into<V>,
    {
        let index = self.index;
        let value = v.into();
        self.index += 1;
        self.map.insert(k, Value { index, value });
    }

    /// Removes an entry from the map.
    pub fn remove(&mut self, k: K) {
        self.map.remove(&k);
    }

    /// Clears all entries from the map.
    pub fn clear(&mut self) {
        self.map.clear();
    }
}

impl<'a, K, V> KeySet<'a, K, V>
where
    K: Eq + Hash + Copy,
{
    /// Checks if the set contains a key.
    pub fn contains(&self, k: K) -> bool {
        self.0.contains(k)
    }

    /// Checks if the set is a subset of another.
    pub fn is_subset(&self, other: &KeySet<K, V>) -> bool {
        self.0.keys().all(|&k| other.contains(k))
    }
}

impl<'a, K, V> PartialEq for KeySet<'a, K, V>
where
    K: Eq + Hash + Copy,
{
    fn eq(&self, other: &KeySet<K, V>) -> bool {
        self.is_subset(other) && other.is_subset(self)
    }
}

impl<'a, K, V> Eq for KeySet<'a, K, V>
where
    K: Eq + Hash + Copy,
{
}
