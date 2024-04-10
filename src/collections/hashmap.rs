use crate::{Cursor, DoublyLinkedList};

use std::{collections::HashMap, fmt::Display, hash::Hash};

#[cfg(not(feature = "sync"))]
use std::rc::{Rc, Weak};

#[cfg(feature = "sync")]
use {std::sync::Arc as Rc, std::sync::Weak};

/// Provides a basic LRU HashMap implementation based
/// on a [DoublyLinkedList]
///
/// # Example
///
/// ```
/// use lru_st::collections::LruHashMap;
///
/// let mut lru_map = LruHashMap::with_max_entries(10);
/// lru_map.insert(42, "test");
///
/// assert_eq!(lru_map.get(&42), Some("test").as_ref());
/// assert_eq!(lru_map.len(), 1);
///
/// // we fill the map entirely
/// for i in 0..lru_map.cap(){
///     lru_map.insert(i, "fill");
/// }
///
/// assert_eq!(lru_map.len(), 10);
///
/// // this element disapeared from the map as we filled
/// // all the map without fetching it
/// assert_eq!(lru_map.get(&42), None);
/// ```
pub struct LruHashMap<K, V> {
    map: HashMap<Rc<K>, Cursor>,
    lru: DoublyLinkedList<(Weak<K>, V)>,
    max_entries: usize,
}

impl<K, V> LruHashMap<K, V>
where
    K: Hash + Eq,
{
    /// Creates a new [LruHashMap] with a given number of entries
    pub fn with_max_entries(max_entries: usize) -> Self {
        LruHashMap {
            map: HashMap::with_capacity(max_entries),
            lru: DoublyLinkedList::with_capacity(max_entries),
            max_entries,
        }
    }

    #[inline]
    /// Get element from the HashMap
    pub fn get(&mut self, k: &K) -> Option<&V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front(*cursor).unwrap();
            self.lru.front()
        }) {
            return Some(v);
        }
        None
    }

    #[inline]
    /// Get a mut element from the HashMap
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        if let Some((_k, v)) = self.map.get(k).and_then(|cursor| {
            self.lru.move_front(*cursor).unwrap();
            self.lru.front_mut()
        }) {
            return Some(v);
        }
        None
    }

    #[inline]
    /// Returns true if there is an element for this key in the HashMap
    pub fn contains_key(&mut self, k: &K) -> bool {
        self.get(k).is_some()
    }

    #[inline]
    /// Inserts a new element in the HashMap
    pub fn insert(&mut self, k: K, v: V) {
        // we update value if already there
        if self.map.contains_key(&k) {
            let old = self.get_mut(&k).expect("value must exist");
            *old = v;
            return;
        }
        // if we arrive here the key/value needs to be inserted
        // if we reached capacity, we must delete the last used entry first
        if self.map.len() == self.max_entries {
            if let Some((k, _v)) = self.lru.pop_back() {
                // we put this in a block so that we can debug_assert latter
                {
                    let key = k.upgrade().expect("weak reference must be valid");
                    self.map.remove(&key);
                }
                // Rc should have been dropped now because we have removed item from map
                debug_assert!(k.upgrade().is_none());
            };
        }
        let k = Rc::new(k);
        let cursor = self.lru.push_front((Rc::downgrade(&k), v));
        self.map.insert(k, cursor);
    }

    #[inline(always)]
    /// Returns the length of the HashMap
    pub fn len(&self) -> usize {
        self.map.len()
    }

    #[inline(always)]
    /// Returns the capacity of the HashMap
    pub fn cap(&self) -> usize {
        self.max_entries
    }

    #[inline(always)]
    /// Returns true if the HashMap is empty
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

impl<K, V> Display for LruHashMap<K, V>
where
    K: Display,
    V: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        write!(f, "{{")?;
        for v in self.lru.iter() {
            let key = v.0.upgrade().expect("weak reference must be valid");
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}:{}", key, v.1)?;
            first = false;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_lru_hashmap() {
        let max_entries = 1000;
        let mut lru = LruHashMap::with_max_entries(max_entries);
        assert!(lru.is_empty());
        assert_eq!(lru.len(), 0);
        for i in 0..max_entries * 2 {
            lru.insert(i, i)
        }
        assert_eq!(lru.len(), max_entries);
        assert_eq!(lru.get(&0), None);
        assert_eq!(lru.get(&max_entries), Some(&max_entries));
        lru.insert(max_entries + 42, 42);
        assert_eq!(lru.get(&(max_entries + 42)), Some(&42));
        println!("{}", lru);
    }
}
