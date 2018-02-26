/// Hash map data structure.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;

/// A hash map that remembers insertion order.
///
/// To simplify the implementation, the key types `K` and `V` are required to be
/// `Copy`. This makes it easier to store in both the vector and the map.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct OrderMap<K, V>
where
    K: fmt::Debug + PartialEq + Eq + Hash,
{
    /// The keys in the order they were inserted.
    keys: Vec<K>,
    /// The underlying hash map.
    map: HashMap<K, V>,
}

impl<K, V> OrderMap<K, V>
where
    K: fmt::Debug + PartialEq + Eq + Hash + Copy,
    V: Copy,
{
    /// Creates a new `OrderMap`.
    pub fn new() -> OrderMap<K, V> {
        OrderMap {
            keys: vec![],
            map: HashMap::new(),
        }
    }

    /// Checks if the map contains a key.
    pub fn contains_key(&self, k: K) -> bool {
        self.map.contains_key(&k)
    }

    /// Gets a value from the map by key.
    pub fn get(&self, k: K) -> Option<V> {
        self.map.get(&k).cloned()
    }

    /// Inserts an entry into the map.
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.keys.push(k);
        self.map.insert(k, v)
    }

    /// Removes an entry from the map.
    ///
    /// Leaves the key in the `keys` vector to preserve indices.
    pub fn remove(&mut self, k: K) -> Option<V> {
        self.map.remove(&k)
    }
}
