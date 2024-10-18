#![deny(unused_imports)]
#![deny(missing_docs)]

//! # lru-st
//!
//! This crate provides a Vec based doubly linked list implementation.
//! It also aims at providing data structures built on top of
//! doubly linked list such as LRU HashMap.
//!
//! # Features
//! - `sync`: to enable when `collections` structures needs to be used in threads
//!
//! # Example: DoublyLinkedList
//!
//! ```
//! use lru_st::{dll, Cursor};
//!
//! let mut dll = dll![1, 2, 3, 4];
//! assert_eq!(dll.len(), 4);
//!
//! let c = dll.push_front(0);
//! // even though the element has been pushed
//! // at front (i.e. 0th position in the list)
//! // its [Cursor] is 4. This is because the
//! // Cursor is a reference to the item not
//! // related to its position in the list.
//! assert_eq!(c, Cursor(4));
//!
//! // first element is 0
//! assert_eq!(dll.front(), Some(&0));
//! assert_eq!(dll.get(Cursor(4)), Some(&0));
//!
//! // we move item with value 4 at front of
//! // the list
//! dll.move_front(Cursor(3)).unwrap();
//! assert_eq!(dll.get_nth(0), Some(&4));
//! assert_eq!(dll.get_nth(1), Some(&0));
//! // even if order of list items changed cursors
//! // are never affected by those changes
//! assert_eq!(dll.get(Cursor(4)), Some(&0));
//! ```
//!
//! # Example: LRU HashMap
//!
//! ```
//! use lru_st::collections::LruHashMap;
//!
//! let mut lru_map = LruHashMap::with_max_entries(10);
//! lru_map.insert(42, "test");
//!
//! assert_eq!(lru_map.get(&42), Some("test").as_ref());
//! assert_eq!(lru_map.len(), 1);
//!
//! // we fill the map entirely
//! for i in 0..lru_map.cap(){
//!     lru_map.insert(i, "fill");
//! }
//!
//! assert_eq!(lru_map.len(), 10);
//!
//! // this element disapeared from the map as we filled
//! // all the map without fetching it
//! assert_eq!(lru_map.get(&42), None);
//! ```
//!
//! # Example: LRU HashSet
//!
//! ```
//! use lru_st::collections::LruHashSet;
//!
//! let mut lru_set = LruHashSet::with_max_entries(10);
//!
//! assert_eq!(lru_set.insert("test"), true);
//! assert_eq!(lru_set.insert("test"), false);
//!
//! assert_eq!(lru_set.contains(&"test"), true);
//!
//! // we remove one element
//! assert_eq!(lru_set.remove(&"test"), true);
//! assert_eq!(lru_set.remove(&"test"), false);
//!
//! assert!(lru_set.is_empty());
//!
//! let mut lru_set = LruHashSet::with_max_entries(10);
//!
//! assert_eq!(lru_set.insert(String::from("will_be_erased")), true);
//!
//! for i in 0..10{
//!     assert_eq!(lru_set.insert(format!("erase_{i}")), true);
//! }
//!
//! // the item vanished as the LRU got full
//! assert_eq!(lru_set.contains(&String::from("will_be_erased")), false);
//! assert!(lru_set.is_full());
//! ```

use std::{
    fmt::{Debug, Display},
    hash::Hash,
};
use thiserror::Error;

/// Module exposing structures implemented
/// on top of [DoublyLinkList]
pub mod collections;

/// Structure representing a **reference** of an element
/// within a [DoublyLinkedList]. It is important to
/// remember that a [Cursor] does not represent the
/// position of an element.
#[derive(Debug, Clone, Hash, Copy, Eq, PartialEq)]
pub struct Cursor(pub usize);

/// A node of the doubly linked list
struct Node<T> {
    prev: Option<Cursor>,
    next: Option<Cursor>,
    value: Option<T>,
    free: bool,
}

impl<T> Node<T> {
    fn free(&mut self) {
        self.prev = None;
        self.next = None;
        self.value = None;
        self.free = true;
    }
}

impl<T> Debug for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "prev={:?} next={:?} free={:?}",
            self.prev, self.next, self.free
        )
    }
}

/// [Vec] based doubly linked list implementation
///
/// # Example
///
/// ```
/// use lru_st::DoublyLinkedList;
///
/// let mut dll = DoublyLinkedList::new();
/// dll.push_front(42);
/// dll.push_front(43);
///
/// assert_eq!(dll.back(), Some(&42));
/// assert_eq!(dll.front(), Some(&43));
///
/// dll.push_back(44);
/// assert_eq!(dll.front(), Some(&43));
/// assert_eq!(dll.back(), Some(&44));
/// ```
pub struct DoublyLinkedList<T> {
    // the head of the list
    head: Option<Cursor>,
    // the tail of the list
    tail: Option<Cursor>,
    // list of nodes
    list: Vec<Node<T>>,
    // free list to use for new node insertion
    free: Vec<Cursor>,
}

impl<T> Default for DoublyLinkedList<T> {
    fn default() -> Self {
        DoublyLinkedList {
            head: None,
            tail: None,
            list: Vec::new(),
            free: Vec::new(),
        }
    }
}

impl<T> Debug for DoublyLinkedList<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{:?}", v)?;
            first = false;
        }
        write!(f, "]")
    }
}

impl<T> Display for DoublyLinkedList<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let mut first = true;
        for v in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "{}", v)?;
            first = false;
        }
        write!(f, "]")
    }
}

/// Enum of the possible [Error] encountered while using
/// a [DoublyLinkedList]
#[derive(Debug, Error, PartialEq, PartialOrd, Ord, Eq)]
pub enum Error {
    /// Error returned when trying to access
    /// an out of bound index
    #[error("out of bound index: {0}")]
    OutOfBound(usize),

    /// Error raised when trying to use a
    /// node alread freed.
    #[error("trying to use a freed node")]
    Uaf,
}

impl<T> PartialEq for DoublyLinkedList<T>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        let mut other_it = other.iter();

        for v in self.iter() {
            match other_it.next() {
                Some(ov) => {
                    if v != ov {
                        return false;
                    }
                }
                None => return false,
            }
        }

        true
    }
}

impl<T> DoublyLinkedList<T> {
    /// Creates a new empty [DoublyLinkedList]
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new empty [DoublyLinkedList] with a given capacity
    pub fn with_capacity(capacity: usize) -> Self {
        DoublyLinkedList {
            list: Vec::with_capacity(capacity),
            ..Default::default()
        }
    }

    /// Creates a new [DoublyLinkedList] from a [Vec]
    pub fn from_vec(v: Vec<T>) -> Self {
        let mut d = Self::new();
        for e in v {
            d.push_back(e);
        }
        d
    }

    /// Returns true if the list is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    fn next_available_cursor(&mut self) -> Cursor {
        self.free.pop().unwrap_or(Cursor(self.list.len()))
    }

    #[inline]
    fn put(&mut self, e: Node<T>, at: Cursor) {
        if at.0 == self.list.len() {
            self.list.push(e);
            return;
        }
        self.list[at.0] = e;
    }

    /// Get the cursor of nth element
    #[inline(always)]
    fn get_nth_cursor(&self, n: usize) -> Option<Cursor> {
        let mut n = n;
        let mut next = self.head;
        while let Some(cursor) = next {
            next = self.list[cursor.0].next;
            if n == 0 {
                return Some(cursor);
            }
            n -= 1;
        }
        None
    }

    #[inline]
    /// Pushes an element to the front of the list
    pub fn push_front(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        let node = Node {
            prev: None,
            next: self.head,
            value: Some(v),
            free: false,
        };

        // if there is no tail
        if self.tail.is_none() {
            self.tail = Some(cursor);
        }

        // we link the old head (if existing) to the new one
        self.new_prev(self.head, Some(cursor));

        // we insert element at position
        self.put(node, cursor);
        // new head
        self.head = Some(cursor);
        cursor
    }

    #[inline]
    /// Pushes an element to the back of the list and returning
    /// the [Cursor] pointing to this element. The [Cursor] can
    /// then be used to directly access/move/pop element.
    pub fn push_back(&mut self, v: T) -> Cursor {
        let cursor = self.next_available_cursor();
        // element to be inserted at the end
        let e = Node {
            prev: self.tail,
            next: None,
            value: Some(v),
            free: false,
        };

        // if there is no head we set it
        if self.head.is_none() {
            self.head = Some(cursor);
        }

        // we link the old tail (if existing) to the new one
        self.new_next(self.tail, Some(cursor));

        // we insert element at position
        self.put(e, cursor);
        // new tail
        self.tail = Some(cursor);
        cursor
    }

    /// Get the element in the list at a given [Cursor] or None
    /// if there is no element. If wanting to get an element at
    /// a given position see [DoublyLinkedList::get_nth].
    #[inline(always)]
    pub fn get(&self, c: Cursor) -> Option<&T> {
        if let Some(e) = self.list.get(c.0) {
            // we return None if node is freed
            if e.free {
                return None;
            }
            return e.value.as_ref();
        }
        None
    }

    /// Get an element given its position in the list
    #[inline(always)]
    pub fn get_nth(&self, n: usize) -> Option<&T> {
        self.get(self.get_nth_cursor(n)?)
    }

    /// Get a mutable element at a given position in the list or None
    /// if there is no element.
    #[inline(always)]
    pub fn get_mut(&mut self, c: Cursor) -> Option<&mut T> {
        if let Some(e) = self.list.get_mut(c.0) {
            // we return None if node is freed
            if e.free {
                return None;
            }
            return e.value.as_mut();
        }
        None
    }

    /// Get an element given its position in the list
    #[inline(always)]
    pub fn get_mut_nth(&mut self, n: usize) -> Option<&mut T> {
        self.get_mut(self.get_nth_cursor(n)?)
    }

    /// Get the element at the front of the list
    #[inline(always)]
    pub fn front(&self) -> Option<&T> {
        if let Some(c) = self.head {
            return self.get(c);
        }
        None
    }

    /// Get a mutable reference to the element at the front of the list
    #[inline(always)]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if let Some(c) = self.head {
            return self.get_mut(c);
        }
        None
    }

    /// Get the element a the back of the list
    #[inline(always)]
    pub fn back(&self) -> Option<&T> {
        if let Some(c) = self.tail {
            return self.get(c);
        }
        None
    }

    /// Get a mutable reference to the element at the back of the list
    #[inline(always)]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if let Some(c) = self.tail {
            return self.get_mut(c);
        }
        None
    }

    /// Returns the number of elements in the list
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.list.len() - self.free.len()
    }

    #[inline]
    fn node(&self, at: Cursor) -> Option<&Node<T>> {
        self.list.get(at.0)
    }

    /// Pops the element a the back of the list
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        if let Some(tail_curs) = self.tail {
            return self._pop(tail_curs);
        }
        None
    }

    #[inline]
    fn new_prev(&mut self, at: Option<Cursor>, prev: Option<Cursor>) {
        // if there is something at pos
        if let Some(at) = at {
            // we modify element at pos
            self.list[at.0].prev = prev
        }
    }

    #[inline]
    fn new_next(&mut self, at: Option<Cursor>, next: Option<Cursor>) {
        // if there is something at pos
        if let Some(at) = at {
            // we modify element at pos
            self.list[at.0].next = next;
        }
    }

    /// Provides an iterator (i.e. [DoublyLinkedListIter]) over the elements of the list
    #[inline]
    pub fn iter(&self) -> DoublyLinkedListIter<T> {
        DoublyLinkedListIter {
            dll: self,
            front_cursor: self.head,
            back_cursor: self.tail,
            cross: false,
        }
    }

    /// Move item at cursor to the head of list
    #[inline]
    pub fn move_front(&mut self, at: Cursor) -> Result<(), Error> {
        if at.0 >= self.list.len() {
            return Err(Error::OutOfBound(at.0));
        }

        // we are trying to move a freed node to the top of the list
        if self.list[at.0].free {
            return Err(Error::Uaf);
        }

        // if we are not processing head
        if self.list[at.0].prev.is_some() {
            // we link next to prev
            self.new_prev(self.list[at.0].next, self.list[at.0].prev);
            // we link prev to next
            self.new_next(self.list[at.0].prev, self.list[at.0].next);

            // we are processing the tail so we have to assign a new
            // self.tail
            if self.list[at.0].next.is_none() {
                self.tail = self.list[at.0].prev
            }

            // linking old head to the new head
            self.new_prev(self.head, Some(at));

            // we make item the new head
            self.list[at.0].next = self.head;
            self.list[at.0].prev = None;
            self.head = Some(at);
        }

        Ok(())
    }

    /// Pops the item at front of the doubly linked list
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        match self.head {
            Some(head) => self._pop(head),
            None => None,
        }
    }

    /// Pops the item located at `at` [Cursor] in the doubly linked list.
    /// This API pops an element according to its [Cursor] which is
    /// not corresponding to its position within the linked list.
    /// To pop an item according to its position in the linked list
    /// use `pop_nth`.
    #[inline]
    pub fn pop(&mut self, at: Cursor) -> Option<T> {
        if !self.list[at.0].free {
            return self._pop(at);
        }
        None
    }

    /// Pops the nth element of linked list
    #[inline]
    pub fn pop_nth(&mut self, n: usize) -> Option<T> {
        let mut n = n;
        let mut next = self.head;
        while let Some(cursor) = next {
            next = self.list[cursor.0].next;
            if n == 0 {
                return self.pop(cursor);
            }
            n -= 1;
        }
        None
    }

    #[inline(always)]
    fn _pop(&mut self, at: Cursor) -> Option<T> {
        debug_assert!(!self.list[at.0].free);

        // if we want to remove head
        if Some(at) == self.head {
            let new_head = self.list[at.0].next;
            self.head = new_head;
        }

        // if we want to remove tail
        if Some(at) == self.tail {
            let new_tail = self.list[at.0].prev;
            self.tail = new_tail;
        }

        // actually unlinking the at Cursor
        self.new_prev(self.list[at.0].next, self.list[at.0].prev);
        self.new_next(self.list[at.0].prev, self.list[at.0].next);

        let out = self.list[at.0].value.take();
        // mark node at Cursor as free
        self.list[at.0].free();
        self.free.push(at);
        out
    }

    #[inline]
    #[allow(dead_code)]
    fn verify(&self) {
        let mut prev = None;
        let mut oc = self.head;
        while let Some(c) = oc {
            let node = self.list.get(c.0).unwrap();
            // we check back link
            assert_eq!(node.prev, prev);
            prev = Some(c);
            oc = node.next;
        }
    }
}

/// [DoublyLinkedList] iterator
pub struct DoublyLinkedListIter<'a, T> {
    dll: &'a DoublyLinkedList<T>,
    front_cursor: Option<Cursor>,
    back_cursor: Option<Cursor>,
    cross: bool,
}

impl<'a, T> Iterator for DoublyLinkedListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cross {
            return None;
        }

        if self.front_cursor == self.back_cursor {
            self.cross = true
        }

        let cursor = self.front_cursor?;
        let node = self.dll.node(cursor).expect("node must be found at cursor");
        self.front_cursor = node.next;
        node.value.as_ref()
    }
}

impl<'a, T> DoubleEndedIterator for DoublyLinkedListIter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.cross {
            return None;
        }

        if self.front_cursor == self.back_cursor {
            self.cross = true
        }

        let cursor = self.back_cursor?;
        // nodes pointed by others should always be valid
        let node = self.dll.node(cursor).expect("node must be found at cursor");
        self.back_cursor = node.prev;
        node.value.as_ref()
    }
}

/// Macro used to create a [DoublyLinkedList]
///
/// # Example
///
/// ```
/// use lru_st::dll;
///
/// let d = dll![1,2,3];
/// assert_eq!(d, dll![1,2,3]);
/// assert_ne!(d, dll![3,2,1]);
/// ```
#[macro_export]
macro_rules! dll {
    [$($item:literal),*] => {
        {
            let mut dll=$crate::DoublyLinkedList::new();
            $(dll.push_back($item);)*
            dll
        }
    };
}

#[cfg(test)]
mod tests {
    use rand::prelude::*;

    use super::*;

    #[test]
    fn dll_from_vec_test() {
        let len = 100;
        let d = DoublyLinkedList::from_vec((0..len).collect());
        println!("{}", d);
        let mut i = 0;

        // from_vec must insert values in the same order they appear in the vector
        #[allow(clippy::explicit_counter_loop)]
        for v in d.iter() {
            assert_eq!(v, &i);
            i += 1;
        }
    }

    #[test]
    fn dll_rev_iter_test() {
        let d = DoublyLinkedList::from_vec(vec![1, 2, 3, 4, 5]);
        println!("{}", d);
        let mut iter = d.iter();
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next_back(), Some(&5));
        assert_eq!(iter.next_back(), Some(&4));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next_back(), Some(&3));
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }

    #[test]
    fn dll_iter_test() {
        let len = 100;
        let d = DoublyLinkedList::from_vec((0..len).collect());

        let mut i = len - 1;
        for v in d.iter().rev() {
            assert_eq!(v, &i);
            i -= 1;
        }

        assert_eq!(i, -1);
    }

    #[test]
    fn dll_push_back_test() {
        let len = 100;
        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_back(i);
        }

        assert_eq!(d.len(), len);

        for i in (0..len).rev() {
            let back = d.pop_back();
            assert!(back.is_some(), "iteration {i}");
            assert_eq!(back.unwrap(), i, "iteration {i}");
            assert!(d.node(Cursor(i)).unwrap().free);
            d.free
                .iter()
                .for_each(|i| assert!(d.node(*i).unwrap().free));
        }

        assert!(d.is_empty());
        assert_eq!(d.head, None);
        assert_eq!(d.tail, None);
        assert_eq!(d.free.len(), len);
        d.list.iter().for_each(|n| assert!(n.free));
    }

    #[test]
    fn dll_push_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in (0..len).rev() {
            d.push_front(i);
        }

        assert_eq!(d.len(), len);

        for i in (0..len).rev() {
            assert_eq!(d.pop_back().unwrap(), i);
            assert!(d.node(Cursor(len - i - 1)).unwrap().free);
            d.free
                .iter()
                .for_each(|i| assert!(d.node(*i).unwrap().free));
        }

        assert!(d.is_empty());
        assert_eq!(d.head, None);
        assert_eq!(d.tail, None);
        assert_eq!(d.free.len(), len);
        d.list.iter().for_each(|n| assert!(n.free));
    }

    #[test]
    fn dll_move_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        for i in (0..len).rev() {
            println!("moving {} to front", d.get(Cursor(i)).unwrap());
            d.move_front(Cursor(i)).unwrap();
            assert_eq!(d.front().unwrap(), &i);
        }
    }

    #[test]
    fn dll_pop_front_test() {
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        for i in (0..len).rev() {
            d.verify();
            assert_eq!(d.pop_front(), Some(i));
        }

        assert_eq!(d.len(), 0);
    }

    #[test]
    fn dll_pop_test_simple() {
        let mut dll = dll![1, 2, 3, 4, 5];
        assert_eq!(dll.pop(Cursor(2)), Some(3));
        assert_eq!(dll.pop(Cursor(3)), Some(4));
        // two values got popped in the middle so pop_front
        // should not return them
        assert_eq!(dll.pop_front(), Some(1));
        assert_eq!(dll.pop_front(), Some(2));
        assert_eq!(dll.pop_back(), Some(5));
        assert!(dll.is_empty());
    }

    #[test]
    fn dll_pop_nth() {
        let mut dll = dll![1, 2, 3, 4, 5];
        dll.move_front(Cursor(2)).unwrap();
        assert_eq!(dll.pop_nth(2), Some(2));
    }

    #[test]
    fn dll_pop_test() {
        let mut rng = thread_rng();
        let len = 100;

        let mut d = DoublyLinkedList::new();

        for i in 0..len {
            d.push_front(i);
        }

        let mut cursors: Vec<usize> = (0..len).collect();
        cursors.shuffle(&mut rng);

        for i in cursors {
            d.verify();
            assert_eq!(d.pop(Cursor(i)), Some(i));
            assert_eq!(d.pop(Cursor(i)), None);
        }

        assert_eq!(d.len(), 0);
    }

    #[test]
    fn dll_eq_test() {
        assert_eq!(dll![1, 2, 3], dll![1, 2, 3]);
        assert_ne!(dll![1, 2, 3], dll![1, 2]);
    }
}
