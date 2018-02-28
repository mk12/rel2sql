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
    /// The keys in the order they were inserted.
    keys: Vec<K>,
    /// The underlying hash map.
    map: HashMap<K, V>,
}

/// A set view of the keys of an `OrderMap`.
pub struct KeySet<'a, K: 'a, V: 'a>(&'a OrderMap<K, V>);

impl<K, V> PartialEq for OrderMap<K, V>
where
    K: Eq + Hash,
    V: PartialEq,
{
    fn eq(&self, other: &OrderMap<K, V>) -> bool {
        self.keys == other.keys && self.map == other.map
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
            "OrderMap {{ keys: {:?}, map: {:?} }}",
            self.keys, self.map
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
            keys: vec![],
            map: HashMap::new(),
        }
    }

    /// Checks if the map contains a key.
    pub fn contains(&self, k: K) -> bool {
        self.map.contains_key(&k)
    }

    /// Gets a value from the map by key.
    pub fn get(&self, k: K) -> Option<&V> {
        self.map.get(&k)
    }

    /// Returns an iterator over the keys of the map.
    pub fn keys(&self) -> hash_map::Keys<K, V> {
        self.map.keys()
    }

    /// Returns a view of the map's keys, as a set.
    pub fn key_set(&self) -> KeySet<K, V> {
        KeySet(&self)
    }

    /// Inserts an entry into the map.
    pub fn insert<T>(&mut self, k: K, v: T) -> Option<V>
    where
        T: Into<V>,
    {
        self.keys.push(k);
        self.map.insert(k, v.into())
    }

    /// Removes an entry from the map.
    ///
    /// Leaves the key in the `keys` vector to preserve indices.
    pub fn remove(&mut self, k: K) -> Option<V> {
        self.map.remove(&k)
    }
}

impl<'a, K, V> KeySet<'a, K, V>
where
    K: Eq + Hash + Copy,
{
    /// Checks if the set contains a key.
    pub fn contains(&self, k: K) -> bool {
        self.0.map.contains_key(&k)
    }

    /// Checks if the set is a subset of another.
    pub fn is_subset(&self, other: &KeySet<K, V>) -> bool {
        self.0.map.keys().all(|&k| other.contains(k))
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
