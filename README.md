[![Crates.io Version](https://img.shields.io/crates/v/lru-st?style=for-the-badge)](https://crates.io/crates/lru-st)
[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/lru-st/rust.yml?style=for-the-badge)](https://github.com/qjerome/lru-st/actions/workflows/rust.yml)
[![docs.rs](https://img.shields.io/docsrs/lru-st?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/lru-st)
![Crates.io MSRV](https://img.shields.io/crates/msrv/lru-st?style=for-the-badge)

<!-- cargo-rdme start -->

# lru-st

This crate provides a Vec based doubly linked list implementation.
It also aims at providing data structures built on top of
doubly linked list such as LRU HashMap.

# Example: DoublyLinkedList

```rust
use lru_st::{dll, Cursor};

let mut dll = dll![1, 2, 3, 4];
assert_eq!(dll.len(), 4);

let c = dll.push_front(0);
// even though the element has been pushed
// at front (i.e. 0th position in the list)
// its [Cursor] is 4. This is because the
// Cursor is a reference to the item not
// related to its position in the list.
assert_eq!(c, Cursor(4));

// first element is 0
assert_eq!(dll.front(), Some(&0));
assert_eq!(dll.get(Cursor(4)), Some(&0));

// we move item with value 4 at front of
// the list
dll.move_front(Cursor(3)).unwrap();
assert_eq!(dll.get_nth(0), Some(&4));
assert_eq!(dll.get_nth(1), Some(&0));
// even if order of list items changed cursors
// are never affected by those changes
assert_eq!(dll.get(Cursor(4)), Some(&0));
```

# Example: LRU HashMap

```rust
use lru_st::collections::LruHashMap;

let mut lru_map = LruHashMap::with_max_entries(10);
lru_map.insert(42, "test");

assert_eq!(lru_map.get(&42), Some("test").as_ref());
assert_eq!(lru_map.len(), 1);

// we fill the map entirely
for i in 0..lru_map.cap(){
    lru_map.insert(i, "fill");
}

assert_eq!(lru_map.len(), 10);

// this element disapeared from the map as we filled
// all the map without fetching it
assert_eq!(lru_map.get(&42), None);
```

# Example: LRU HashSet

```rust
use lru_st::collections::LruHashSet;

let mut lru_set = LruHashSet::with_max_entries(10);

assert_eq!(lru_set.insert("test"), true);
assert_eq!(lru_set.insert("test"), false);

assert_eq!(lru_set.contains(&"test"), true);

// we remove one element
assert_eq!(lru_set.remove(&"test"), true);
assert_eq!(lru_set.remove(&"test"), false);

assert!(lru_set.is_empty());

let mut lru_set = LruHashSet::with_max_entries(10);

assert_eq!(lru_set.insert(String::from("will_be_erased")), true);

for i in 0..10{
    assert_eq!(lru_set.insert(format!("erase_{i}")), true);
}

// the item vanished as the LRU got full
assert_eq!(lru_set.contains(&String::from("will_be_erased")), false);
assert!(lru_set.is_full());
```

<!-- cargo-rdme end -->

# License

GNU General Public License v3.0

Permissions of this strong copyleft license are conditioned on making available complete source code 
of licensed works and modifications, which include larger works using a licensed work, under the 
same license. Copyright and license notices must be preserved. Contributors provide an express grant
of patent rights.
