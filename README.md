[![Crates.io Version](https://img.shields.io/crates/v/lru-st?style=for-the-badge)](https://crates.io/crates/lru-st)
[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/qjerome/lru-st/rust.yml?style=for-the-badge)](https://github.com/qjerome/lru-st/actions/workflows/rust.yml)
[![docs.rs](https://img.shields.io/docsrs/lru-st?style=for-the-badge&logo=docs.rs&color=blue)](https://docs.rs/lru-st)
![Crates.io MSRV](https://img.shields.io/crates/msrv/lru-st?style=for-the-badge)

<!-- cargo-rdme start -->

# lru-st

A doubly linked list stored in a single [`Vec`](https://doc.rust-lang.org/stable/alloc/vec/struct.Vec.html), and the LRU collections
built on top of it.

Nodes live in one contiguous buffer and are linked by index instead of
by pointer. Freed slots are recycled, so pushing and popping at either
end does not go through the allocator once the buffer has grown. Every
push returns a [`Cursor`](https://docs.rs/lru-st/latest/lru_st/struct.Cursor.html), a stable handle that gives O(1) access to,
removal of, or promotion of that element regardless of its position:
the operations an LRU cache needs.

The crate is written entirely in safe Rust (`#![deny(unsafe_code)]`).

# Data structures

| Type | Description |
|------|-------------|
| [`LinkedList`](https://docs.rs/lru-st/latest/lru_st/struct.LinkedList.html) | `Vec`-backed doubly linked list with O(1) push/pop at both ends |
| [`collections::LruHashMap`](https://docs.rs/lru-st/latest/lru_st/collections/hashmap/struct.LruHashMap.html) | Bounded map evicting the least recently used entry |
| [`collections::LruHashSet`](https://docs.rs/lru-st/latest/lru_st/collections/hashset/struct.LruHashSet.html) | Bounded set evicting the least recently used value |

# Performance

Compared with [`std::collections::LinkedList`](https://doc.rust-lang.org/stable/alloc/collections/linked_list/struct.LinkedList.html), which allocates every
node separately:

- pushing and popping at either end, and building a list with
  `collect`, are several times faster, and the gap grows with the
  list length;
- iteration still follows links one node at a time and is somewhat
  slower than std's.

Run `cargo bench --features cursor` to measure on your hardware.

# Feature flags

| Feature | Description |
|---------|-------------|
| `cursor` | Makes the [`LinkedList`](https://docs.rs/lru-st/latest/lru_st/struct.LinkedList.html) methods taking a [`Cursor`](https://docs.rs/lru-st/latest/lru_st/struct.Cursor.html) public (`get`, `get_mut`, `pop`, `move_front`) for building custom structures. Read the [stale cursors](https://docs.rs/lru-st/latest/lru_st/struct.Cursor.html#stale-cursors) section first. |
| `sync` | Uses `Arc` instead of `Rc` inside `collections` so they can be sent across threads. |
| `hashbrown` | Uses [hashbrown](https://docs.rs/hashbrown)'s `HashMap` in `collections`. Its default hasher (foldhash) is faster but **not** resistant to HashDoS: avoid it when keys come from untrusted input. |

# Example: LinkedList

```rust
use lru_st::LinkedList;

let mut dll: LinkedList<_> = (1..=4).collect();
assert_eq!(dll.len(), 4);

dll.push_front(0);
assert_eq!(dll.front(), Some(&0));
assert_eq!(dll.back(), Some(&4));
assert_eq!(dll.get_nth(2), Some(&2));

assert_eq!(dll.pop_nth(2), Some(2));
assert_eq!(dll.iter().copied().collect::<Vec<_>>(), [0, 1, 3, 4]);
```

# Example: LinkedList with cursors

Requires the `cursor` feature.

```rust
use lru_st::LinkedList;

let mut dll = LinkedList::new();
dll.push_back(1);
let c2 = dll.push_back(2);

// a Cursor references an item, not its position in the list
let c0 = dll.push_front(0);
assert_eq!(dll.get(c0), Some(&0));

dll.move_front(c2).unwrap();
assert_eq!(dll.get_nth(0), Some(&2));
// cursors are not affected by reordering
assert_eq!(dll.get(c0), Some(&0));
```

# Example: LRU HashMap

```rust
use lru_st::collections::LruHashMap;

let mut lru_map = LruHashMap::with_max_entries(10);
lru_map.insert(42, "test");

assert_eq!(lru_map.get(&42), Some("test").as_ref());
assert_eq!(lru_map.len(), 1);

// fill the map without touching key 42 again
for i in 0..lru_map.cap() {
    lru_map.insert(i, "fill");
}

assert_eq!(lru_map.len(), 10);

// 42 was the least recently used entry, so it was evicted
assert_eq!(lru_map.get(&42), None);
```

# Example: LRU HashSet

```rust
use lru_st::collections::LruHashSet;

let mut lru_set = LruHashSet::with_max_entries(10);

assert_eq!(lru_set.insert("test"), true);
assert_eq!(lru_set.insert("test"), false);

assert_eq!(lru_set.contains(&"test"), true);

assert_eq!(lru_set.remove(&"test"), true);
assert_eq!(lru_set.remove(&"test"), false);

assert!(lru_set.is_empty());

let mut lru_set = LruHashSet::with_max_entries(10);

assert_eq!(lru_set.insert(String::from("will_be_erased")), true);

for i in 0..10 {
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
