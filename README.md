[![Crates.io](https://img.shields.io/crates/v/drop-tracker)](https://crates.io/crates/drop-tracker) [![docs.rs](https://img.shields.io/docsrs/drop-tracker)](https://docs.rs/drop-tracker/latest/drop_tracker/) [![Crates.io](https://img.shields.io/crates/l/drop-tracker)](https://choosealicense.com/licenses/bsd-3-clause/)

Rust crate to check if a variable got correctly [dropped]. This crate is mostly useful in unit
tests for code involving [`ManuallyDrop`], [`MaybeUninit`], unsafe memory management,
custom containers, and more.

More specifically, this crate allows you to test if a variable is alive or has been dropped, and
also detects when a variable gets dropped twice. These features can be used to detect bugs in your
custom wrappers or containers that make use of unsafe memory management and cannot be checked at
compile time by the Rust compiler.

[dropped]: https://doc.rust-lang.org/reference/destructors.html
[`ManuallyDrop`]: std::mem::ManuallyDrop
[`MaybeUninit`]: std::mem::MaybeUninit

# Concepts

The main struct of this crate is `DropTracker`. Once you initialize a tracker, you call
`DropTracker::track` on it to get a `DropItem`. Each drop item is identified by a key;
the key can be used at any time to check the state of the item and see if it's alive or
if it has been dropped.

# Examples

This is how you would test that a container like `Vec` drops all its items when the container
is dropped:

```
use drop_tracker::DropTracker;

let mut tracker = DropTracker::new();

// Create a new vector and add a bunch of elements to it. The elements in this case are
// identified by integer keys (1, 2, 3), but any hashable type would work.
let v = vec![tracker.track(1),
             tracker.track(2),
             tracker.track(3)];

// Assert that all elements in the vector are alive
tracker.all_alive(1..=3)
       .expect("expected all elements to be alive");

// Once the vector is dropped, all items should be dropped with it
drop(v);
tracker.all_dropped(1..=3)
       .expect("expected all elements to be dropped");
```

This is how you would test a struct that involves `MaybeUninit`:

```
# #![allow(dead_code)]
use std::mem::MaybeUninit;

struct MyOption<T> {
    set: bool,
    data: MaybeUninit<T>,
}

impl<T> MyOption<T> {
    fn none() -> Self {
        Self { set: false, data: MaybeUninit::uninit() }
    }

    fn some(x: T) -> Self {
        Self { set: true, data: MaybeUninit::new(x) }
    }
}

// BUG: MyOption<T> does not implement Drop!
// BUG: The instance inside `data` may be initialized but not be properly destructed!

// BUG: The following code will silently leak memory:
let opt = MyOption::some(String::from("hello"));
drop(opt); // the String does not get deallocated

// DropTracker is able to catch this sort of bugs:
use drop_tracker::DropTracker;

let mut tracker = DropTracker::new();
let opt = MyOption::some(tracker.track("item"));

tracker.state(&"item")
       .alive()
       .expect("item is expected to be alive"); // works

drop(opt);

tracker.state(&"item")
       .dropped()
       .expect("item is expected to be dropped"); // panics, meaning that the bug was detected
```
