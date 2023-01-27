//! Crate to check if a variable got correctly [dropped]. This crate is mostly useful in unit
//! tests for code involving [`ManuallyDrop`], [`MaybeUninit`], unsafe memory management,
//! custom containers, and more.
//!
//! [dropped]: https://doc.rust-lang.org/reference/destructors.html
//! [`ManuallyDrop`]: std::mem::ManuallyDrop
//! [`MaybeUninit`]: std::mem::MaybeUninit
//!
//! # Concepts
//!
//! The main struct of this crate is [`DropTracker`]. Once you initialize a tracker, you call
//! [`DropTracker::track`] on it to get a [`DropItem`]. Each drop item is identified by a key;
//! the key can be used at any time to check the state of the item and see if it's alive or if
//! it has been dropped.
//!
//! # Examples
//!
//! This is how you would test that a container like [`Vec`] drops all its items when the container
//! is dropped:
//!
//! ```
//! use drop_tracker::DropTracker;
//!
//! let mut tracker = DropTracker::new();
//!
//! // Create a new vector and add a bunch of elements to it. The elements in this case are
//! // identified by integer keys (1, 2, 3), but any hashable type would work.
//! let v = vec![tracker.track(1),
//!              tracker.track(2),
//!              tracker.track(3)];
//!
//! // Assert that all elements in the vector are alive
//! tracker.all_alive(1..=3)
//!        .expect("expected all elements to be alive");
//!
//! // Once the vector is dropped, all items should be dropped with it
//! drop(v);
//! tracker.all_dropped(1..=3)
//!        .expect("expected all elements to be dropped");
//! ```
//!
//! This is how you would test a struct that involves [`MaybeUninit`]:
//!
//! ```should_panic
//! # #![allow(dead_code)]
//! use std::mem::MaybeUninit;
//!
//! struct MyOption<T> {
//!     set: bool,
//!     data: MaybeUninit<T>,
//! }
//!
//! impl<T> MyOption<T> {
//!     fn none() -> Self {
//!         Self { set: false, data: MaybeUninit::uninit() }
//!     }
//!
//!     fn some(x: T) -> Self {
//!         Self { set: true, data: MaybeUninit::new(x) }
//!     }
//! }
//!
//! // BUG: MyOption<T> does not implement Drop!
//! // BUG: The instance inside `data` may be initialized but not be properly destructed!
//!
//! // BUG: The following code will silently leak memory:
//! let opt = MyOption::some(String::from("hello"));
//! drop(opt); // the String does not get deallocated
//!
//! // DropTracker is able to catch this sort of bugs:
//! use drop_tracker::DropTracker;
//!
//! let mut tracker = DropTracker::new();
//! let opt = MyOption::some(tracker.track("item"));
//!
//! tracker.state(&"item")
//!        .alive()
//!        .expect("item is expected to be alive"); // works
//!
//! drop(opt);
//!
//! tracker.state(&"item")
//!        .dropped()
//!        .expect("item is expected to be dropped"); // panics, meaning that the bug was detected
//! ```
//!
//! # Double drop
//!
//! [`DropItem`] will panic if it gets dropped twice or more, as this is generally a bug and may
//! cause undefined behavior. This feature can be used to identify bugs with code using
//! [`ManuallyDrop`](std::mem::ManuallyDrop), [`MaybeUninit`](std::mem::MaybeUninit) or
//! [`std::ptr::drop_in_place`], like in the following example:
//!
//! ```should_panic
//! use std::ptr;
//! use drop_tracker::DropTracker;
//!
//! let mut tracker = DropTracker::new();
//! let mut item = tracker.track("something");
//!
//! unsafe { ptr::drop_in_place(&mut item); } // ok
//! unsafe { ptr::drop_in_place(&mut item); } // panic!
//! ```
//!
//! # Use in collections
//!
//! The [`DropItem`] instances returned by [`DropTracker::track`] hold a clone of the key passed
//! to `track`. The `DropItem`s are [comparable](std::cmp) and [hashable](std::hash) if the
//! underlying key is. This makes `DropItem` instances usable directly in collections like
//! [`HashMap`](std::collections::HashMap), [`BTreeMap`](std::collections::BTreeMap),
//! [`HashSet`](std::collections::HashSet) and many more.
//!
//! Here is an example involving [`HashSet`](std::collections::HashSet):
//!
//! ```
//! use drop_tracker::DropTracker;
//! use std::collections::HashSet;
//!
//! let mut tracker = DropTracker::new();
//!
//! let mut set = HashSet::from([
//!     tracker.track(1),
//!     tracker.track(2),
//!     tracker.track(3),
//! ]);
//!
//! set.remove(&3);
//!
//! tracker.state(&1).alive().expect("first item should be alive");
//! tracker.state(&2).alive().expect("second item should be alive");
//! tracker.state(&3).dropped().expect("third item should be dropped");
//! ```
//!
//! Keys are required to be hashable and unique. If you need [`DropItem`] to hold a non-hashable
//! value, or a repeated value, you can construct a [`DropItem`] with an arbitrary value using
//! [`DropTracker::track_with_value`]:
//!
//! ```
//! use drop_tracker::DropTracker;
//!
//! let mut tracker = DropTracker::new();
//!
//! // Construct items identified by integers and holding floats (which are not hashable)
//! let item1 = tracker.track_with_value(1, 7.52);
//! let item2 = tracker.track_with_value(2, 3.89);
//!
//! // Items compare according to their value
//! assert!(item1 > item2); // 7.52 > 3.89
//!
//! // Items that support comparison can be put in a vector and sorted
//! let mut v = vec![item1, item2];
//! v.sort_by(|x, y| x.partial_cmp(y).unwrap());
//! ```

#![warn(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(pointer_structural_match)]
#![warn(unreachable_pub)]
#![warn(unused_crate_dependencies)]
#![warn(unused_qualifications)]

#![doc(test(attr(deny(warnings))))]

#[cfg(test)]
mod tests;

mod itemtraits;

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
use std::iter::FusedIterator;
use std::mem::MaybeUninit;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

/// A type that represents the state of a [`DropItem`]: either alive or dropped.
///
/// See the [module documentation](self) for details.
#[must_use = "you should check whether the status is alive or dropped"]
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum State {
    /// The item is alive.
    Alive,
    /// The item has been dropped, and its destructor has been called.
    Dropped,
}

impl State {
    /// Returns `true` if the state is [`Alive`](State::Alive).
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::State;
    ///
    /// assert!(State::Alive.is_alive());
    /// assert!(!State::Dropped.is_alive());
    /// ```
    #[inline]
    #[must_use = "if you intended to assert that this is alive, consider `.alive().expect()`"]
    pub const fn is_alive(&self) -> bool {
        match self {
            Self::Alive => true,
            Self::Dropped => false,
        }
    }

    /// Returns `true` if the state is [`Dropped`](State::Dropped).
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::State;
    ///
    /// assert!(State::Dropped.is_dropped());
    /// assert!(!State::Alive.is_dropped());
    /// ```
    #[inline]
    #[must_use = "if you intended to assert that this is dropped, consider `.dropped().expect()`"]
    pub const fn is_dropped(&self) -> bool {
        match self {
            Self::Alive => false,
            Self::Dropped => true,
        }
    }

    /// Returns [`Ok`] if the state is [`Alive`](State::Alive), [`Err`] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DroppedError;
    /// use drop_tracker::State;
    ///
    /// assert_eq!(State::Alive.alive(), Ok(()));
    /// assert_eq!(State::Dropped.alive(), Err(DroppedError));
    /// ```
    #[inline]
    #[must_use = "if you intended to assert that this is alive, consider `.alive().expect()`"]
    pub const fn alive(&self) -> Result<(), DroppedError> {
        match self {
            Self::Alive => Ok(()),
            Self::Dropped => Err(DroppedError),
        }
    }

    /// Returns [`Ok`] if the state is [`Dropped`](State::Dropped), [`Err`] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::AliveError;
    /// use drop_tracker::State;
    ///
    /// assert_eq!(State::Dropped.dropped(), Ok(()));
    /// assert_eq!(State::Alive.dropped(), Err(AliveError));
    /// ```
    #[inline]
    #[must_use = "if you intended to assert that this is dropped, consider `.dropped().expect()`"]
    pub const fn dropped(&self) -> Result<(), AliveError> {
        match self {
            Self::Alive => Err(AliveError),
            Self::Dropped => Ok(()),
        }
    }
}

// Uses an `AtomicBool` (as opposed to e.g. a `RefCell`) to ensure that `DropTracker` and
// `DropItem` are `Send`, `Sync` and `UnwindSafe`.
#[derive(Clone, Debug)]
struct StateCell(Arc<AtomicBool>);

impl StateCell {
    #[inline]
    #[must_use]
    fn new(state: State) -> Self {
        Self(Arc::new(AtomicBool::new(state.is_dropped())))
    }

    #[inline]
    fn get(&self) -> State {
        match self.0.load(Ordering::Relaxed) {
            false => State::Alive,
            true  => State::Dropped,
        }
    }

    #[inline]
    fn replace(&mut self, state: State) -> State {
        match self.0.swap(state.is_dropped(), Ordering::Relaxed) {
            false => State::Alive,
            true  => State::Dropped,
        }
    }

    #[inline]
    #[must_use]
    fn is_alive(&self) -> bool {
        self.get().is_alive()
    }

    #[inline]
    #[must_use]
    fn is_dropped(&self) -> bool {
        self.get().is_dropped()
    }
}

/// Creates [`DropItem`]s and tracks their state.
///
/// [`DropItem`]s can be created using [`track`](DropTracker::track) or
/// [`try_track`](DropTracker::try_track) and their state can be later checked using
/// [`state`](DropTracker::state).
///
/// [`DropItem`]s are identified by keys. A key can be of any type that implement the [`Hash`]
/// and [`Eq`] traits, which include, for example: [`u32`], [`char`], [`str`], ...
///
/// See the [module documentation](self) for details.
#[derive(Default, Debug)]
pub struct DropTracker<K> {
    tracked: HashMap<K, StateCell>,
}

impl<K> DropTracker<K> {
    /// Creates a new empty `DropTracker`.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    ///
    /// let tracker = DropTracker::<u32>::new();
    /// assert_eq!(tracker.tracked().count(), 0);
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self {
            tracked: HashMap::new(),
        }
    }

    /// Returns an iterator over the keys tracked by this `DropTracker`.
    ///
    /// The order of keys returned by this iterator is non deterministic.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// let item_a = tracker.track("a");
    /// let item_b = tracker.track("b");
    /// let item_c = tracker.track("c");
    ///
    /// let mut keys = tracker.tracked()
    ///                       .collect::<Vec<&&str>>();
    /// keys.sort();
    /// assert_eq!(keys, [&"a", &"b", &"c"]);
    /// ```
    pub fn tracked(&self) -> impl Clone + Iterator<Item = &K> + ExactSizeIterator + FusedIterator {
        self.tracked.keys()
    }

    /// Returns an iterator over the keys tracked by this `DropTracker` that are alive.
    ///
    /// The order of keys returned by this iterator is non deterministic.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// let item_a = tracker.track("a");
    /// let item_b = tracker.track("b");
    /// let item_c = tracker.track("c");
    ///
    /// drop(item_c);
    ///
    /// let mut alive_keys = tracker.alive()
    ///                             .collect::<Vec<&&str>>();
    /// alive_keys.sort();
    /// assert_eq!(alive_keys, [&"a", &"b"]);
    ///
    /// drop(item_a);
    /// drop(item_b);
    ///
    /// assert_eq!(tracker.alive().count(), 0);
    /// ```
    pub fn alive(&self) -> impl Clone + Iterator<Item = &K> + FusedIterator {
        self.tracked.iter()
                    .filter(|(_, state)| state.is_alive())
                    .map(|(key, _)| key)
    }

    /// Returns an iterator over the keys tracked by this `DropTracker` that have been dropped.
    ///
    /// The order of keys returned by this iterator is non deterministic.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// let item_a = tracker.track("a");
    /// let item_b = tracker.track("b");
    /// let item_c = tracker.track("c");
    ///
    /// assert_eq!(tracker.dropped().count(), 0);
    ///
    /// drop(item_a);
    /// drop(item_b);
    ///
    /// let mut alive_keys = tracker.dropped()
    ///                             .collect::<Vec<&&str>>();
    /// alive_keys.sort();
    /// assert_eq!(alive_keys, [&"a", &"b"]);
    /// ```
    pub fn dropped(&self) -> impl Clone + Iterator<Item = &K> + FusedIterator {
        self.tracked.iter()
                    .filter(|(_, state)| state.is_dropped())
                    .map(|(key, _)| key)
    }

    /// Forgets all the items tracked by this `DropTracker`.
    ///
    /// The `DropItem`s previously returned by the tracker will still work normally, but it will no
    /// longer be possible to query their status after forgetting them.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// assert_eq!(tracker.tracked().count(), 0);
    ///
    /// let item_a = tracker.track("a");
    /// let item_b = tracker.track("b");
    /// let item_c = tracker.track("c");
    /// assert_eq!(tracker.tracked().count(), 3);
    ///
    /// tracker.forget_all();
    /// assert_eq!(tracker.tracked().count(), 0);
    /// ```
    pub fn forget_all(&mut self) {
        self.tracked.clear();
    }

    /// Forgets all the items tracked by this `DropTracker` that have been dropped.
    ///
    /// The `DropItem`s previously returned by the tracker will still work normally, but it will no
    /// longer be possible to query their status after forgetting them.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// assert_eq!(tracker.tracked().count(), 0);
    ///
    /// let item_a = tracker.track("a");
    /// let item_b = tracker.track("b");
    /// let item_c = tracker.track("c");
    /// assert_eq!(tracker.tracked().count(), 3);
    ///
    /// // After dropping an item, the item is still tracked
    /// drop(item_a);
    /// drop(item_b);
    /// assert_eq!(tracker.tracked().count(), 3);
    ///
    /// // Use `forget_dropped` to lose track of items that have been dropped
    /// tracker.forget_dropped();
    /// assert_eq!(tracker.tracked().count(), 1);
    ///
    /// let mut keys = tracker.tracked()
    ///                       .collect::<Vec<&&str>>();
    /// keys.sort();
    /// assert_eq!(keys, [&"c"]);
    /// ```
    pub fn forget_dropped(&mut self) {
        self.tracked.retain(|_, state| state.is_alive())
    }
}

impl<K: Hash + Eq> DropTracker<K> {
    /// Creates a new [`DropItem`] identified by the given key.
    ///
    /// The value held by the `DropItem` is a clone of the key. Use
    /// [`DropTracker::track_with_value`] if you wish to specify a custom value.
    ///
    /// # Panics
    ///
    /// Panics if the key is already used by another tracked item.
    ///
    /// Call [`forget`](DropTracker::forget),
    /// [`forget_dropped`](DropTracker::forget_dropped) or
    /// [`forget_all`](DropTracker::forget_all) if you wish to reuse a key from an item you no
    /// longer need to track.
    ///
    /// See [`try_track`](DropTracker::try_track) for a variant of this method that does not panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("abc");
    /// assert_eq!(tracker.state("abc"), State::Alive);
    ///
    /// drop(item);
    /// assert_eq!(tracker.state("abc"), State::Dropped);
    /// ```
    ///
    /// Using the same key twice causes a panic:
    ///
    /// ```should_panic
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track("abc");
    /// let item2 = tracker.track("abc"); // panics!
    /// ```
    ///
    /// Use [`forget`](DropTracker::forget) to reuse the same key:
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track("abc");
    /// let _ = tracker.forget("abc");
    /// let item2 = tracker.track("abc"); // works
    /// ```
    pub fn track(&mut self, key: K) -> DropItem<K>
        where K: Clone
    {
        self.try_track(key).expect("cannot track key")
    }

    /// Creates a new [`DropItem`] identified by the given key, or [`Err`] if the key is
    /// already in use.
    ///
    /// The value held by the `DropItem` is a clone of the key. Use
    /// [`DropTracker::try_track_with_value`] if you wish to specify a custom value.
    ///
    /// See also [`track`](DropTracker::track).
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.try_track("abc");
    /// assert!(item.is_ok());
    ///
    /// let item = tracker.try_track("abc");
    /// assert!(item.is_err()); // key is already used
    /// ```
    pub fn try_track(&mut self, key: K) -> Result<DropItem<K>, CollisionError>
        where K: Clone
    {
        let value = key.clone();
        self.try_track_with_value(key, value)
    }

    /// Creates a new [`DropItem`] identified by the given key and holding the given value.
    ///
    /// # Panics
    ///
    /// Panics if the key is already used by another tracked item.
    ///
    /// Call [`forget`](DropTracker::forget),
    /// [`forget_dropped`](DropTracker::forget_dropped) or
    /// [`forget_all`](DropTracker::forget_all) if you wish to reuse a key from an item you no
    /// longer need to track.
    ///
    /// See [`try_track_with_value`](DropTracker::try_track_with_value) for a variant of this
    /// method that does not panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track_with_value("abc", vec![1, 2, 3]);
    /// assert_eq!(tracker.state("abc"), State::Alive);
    ///
    /// drop(item);
    /// assert_eq!(tracker.state("abc"), State::Dropped);
    /// ```
    ///
    /// Using the same key twice causes a panic:
    ///
    /// ```should_panic
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track_with_value("abc", vec![1, 2, 3]);
    /// let item2 = tracker.track_with_value("abc", vec![4, 5, 6]); // panics!
    /// ```
    ///
    /// Use [`forget`](DropTracker::forget) to reuse the same key:
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track_with_value("abc", vec![1, 2, 3]);
    /// let _ = tracker.forget("abc");
    /// let item2 = tracker.track_with_value("abc", vec![4, 5, 6]); // works
    /// ```
    pub fn track_with_value<V>(&mut self, key: K, value: V) -> DropItem<V> {
        self.try_track_with_value(key, value).expect("cannot track key")
    }

    /// Creates a new [`DropItem`] identified by the given key and holding the given value, or
    /// [`Err`] if the key is already in use.
    ///
    /// See also [`track_with_value`](DropTracker::track_with_value).
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.try_track_with_value("abc", vec![1, 2, 3]);
    /// assert!(item.is_ok());
    ///
    /// let item = tracker.try_track_with_value("abc", vec![4, 5, 6]);
    /// assert!(item.is_err()); // key is already used
    /// ```
    pub fn try_track_with_value<V>(&mut self, key: K, value: V) -> Result<DropItem<V>, CollisionError> {
        let state = StateCell::new(State::Alive);
        match self.tracked.entry(key) {
            Entry::Occupied(_) => Err(CollisionError),
            Entry::Vacant(entry) => {
                entry.insert(state.clone());
                Ok(DropItem::new(value, state))
            },
        }
    }
}

impl<K: Hash + Eq> DropTracker<K> {
    /// Checks the state of a [`DropItem`] tracked by this `DropTracker`: [alive](State::Alive) or
    /// [dropped](State::Dropped).
    ///
    /// # Panics
    ///
    /// Panics if the given key is not tracked.
    ///
    /// See [`try_state`](DropTracker::try_state) for a variant of this method that does not panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("abc");
    /// assert_eq!(tracker.state("abc"), State::Alive);
    ///
    /// drop(item);
    /// assert_eq!(tracker.state("abc"), State::Dropped);
    /// ```
    ///
    /// Querying a key that is not tracked causes a panic:
    ///
    /// ```should_panic
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("abc");
    /// let state = tracker.state("def"); // panics!
    /// ```
    pub fn state<Q>(&self, key: &Q) -> State
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized
    {
        self.try_state(key).expect("cannot get state")
    }

    /// Checks the state of a [`DropItem`] tracked by this `DropTracker`: [alive](State::Alive) or
    /// [dropped](State::Dropped). Returns [`Err`] it the given key is not tracked.
    ///
    /// See also [`state`](DropTracker::state).
    ///
    /// # Examples
    ///
    /// ```
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::NotTrackedError;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("abc");
    /// assert_eq!(tracker.try_state("abc"), Ok(State::Alive));
    /// assert_eq!(tracker.try_state("def"), Err(NotTrackedError));
    ///
    /// drop(item);
    /// assert_eq!(tracker.try_state("abc"), Ok(State::Dropped));
    /// assert_eq!(tracker.try_state("def"), Err(NotTrackedError));
    /// ```
    pub fn try_state<Q>(&self, key: &Q) -> Result<State, NotTrackedError>
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized
    {
        self.tracked.get(key)
                    .ok_or(NotTrackedError)
                    .map(|state| state.get())
    }

    /// Forgets an item tracked by this `DropTracker`, and returns its current state
    /// ([alive](State::Alive) or [dropped](State::Dropped)).
    ///
    /// The `DropItem`s previously returned by the tracker will still work normally, but it will no
    /// longer be possible to query their status after forgetting them.
    ///
    /// # Panics
    ///
    /// Panics if the given key is not tracked.
    ///
    /// See [`try_forget`](DropTracker::try_forget) for a variant of this method that does not panic.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("a");
    /// assert!(tracker.is_tracked("a"));
    ///
    /// assert_eq!(tracker.forget("a"), State::Alive);
    /// assert!(!tracker.is_tracked("a"));
    /// ```
    ///
    /// Forgetting a key that is not tracked causes a panic:
    ///
    /// ```should_panic
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("abc");
    /// let state = tracker.forget("def"); // panics!
    /// ```
    pub fn forget<Q>(&mut self, key: &Q) -> State
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized
    {
        self.try_forget(key).expect("cannot forget item")
    }

    /// Forgets an item tracked by this `DropTracker`, and returns its current state
    /// ([alive](State::Alive) or [dropped](State::Dropped)), or [`Err`] if the item is not
    /// tracked.
    ///
    /// The `DropItem`s previously returned by the tracker will still work normally, but it will no
    /// longer be possible to query their status after forgetting them.
    ///
    /// See also [`forget`](DropTracker::forget).
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::NotTrackedError;
    /// use drop_tracker::State;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item = tracker.track("a");
    /// assert!(tracker.is_tracked("a"));
    ///
    /// assert_eq!(tracker.try_forget("a"), Ok(State::Alive));
    /// assert_eq!(tracker.try_forget("b"), Err(NotTrackedError));
    /// ```
    pub fn try_forget<Q>(&mut self, key: &Q) -> Result<State, NotTrackedError>
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized
    {
        self.tracked.remove(key)
                    .ok_or(NotTrackedError)
                    .map(|state| state.get())
    }

    /// Returns [`true`] if an item identified by the given key is tracked by this `DropTracker`,
    /// [`false`] otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    ///
    /// let mut tracker = DropTracker::new();
    /// assert!(!tracker.is_tracked("abc"));
    ///
    /// let item = tracker.track("abc");
    /// assert!(tracker.is_tracked("abc"));
    /// ```
    #[must_use]
    pub fn is_tracked<Q>(&self, key: &Q) -> bool
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized
    {
        self.try_state(key).is_ok()
    }

    /// Returns [`Ok`] if all the given keys point to items that are [alive](State::Alive),
    /// [`Err`] otherwise.
    ///
    /// An error may be returned in two cases: either a key is not tracked, or it has been dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::NotAllAliveError;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track(1);
    /// let item2 = tracker.track(2);
    /// let item3 = tracker.track(3);
    /// let item4 = tracker.track(4);
    ///
    /// drop(item3);
    /// drop(item4);
    ///
    /// assert_eq!(tracker.all_alive([1, 2]), Ok(()));
    ///
    /// assert_eq!(tracker.all_alive([1, 2, 3, 4, 5, 6]),
    ///            Err(NotAllAliveError {
    ///                dropped: vec![3, 4],
    ///                untracked: vec![5, 6],
    ///            }));
    /// ```
    pub fn all_alive<Q, Item, Iter>(&self, iter: Iter) -> Result<(), NotAllAliveError<Item>>
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized,
              Item: Borrow<Q>,
              Iter: IntoIterator<Item = Item>
    {
        // Vec won't allocate any memory until items are pushed to it, so if this method does not
        // fail, no memory will be allocated
        let mut err = NotAllAliveError {
            dropped: Vec::new(),
            untracked: Vec::new(),
        };

        for key in iter {
            match self.try_state(key.borrow()) {
                Ok(State::Alive) => (),
                Ok(State::Dropped) => err.dropped.push(key),
                Err(NotTrackedError) => err.untracked.push(key),
            }
        }

        if err.dropped.is_empty() && err.untracked.is_empty() {
            Ok(())
        } else {
            Err(err)
        }
    }

    /// Returns [`Ok`] if all the given keys point to items that are [dropped](State::Dropped),
    /// [`Err`] otherwise.
    ///
    /// An error may be returned in two cases: either a key is not tracked, or it has been dropped.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::NotAllDroppedError;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track(1);
    /// let item2 = tracker.track(2);
    /// let item3 = tracker.track(3);
    /// let item4 = tracker.track(4);
    ///
    /// drop(item3);
    /// drop(item4);
    ///
    /// assert_eq!(tracker.all_dropped([3, 4]), Ok(()));
    ///
    /// assert_eq!(tracker.all_dropped([1, 2, 3, 4, 5, 6]),
    ///            Err(NotAllDroppedError {
    ///                alive: vec![1, 2],
    ///                untracked: vec![5, 6],
    ///            }));
    /// ```
    pub fn all_dropped<Q, Item, Iter>(&self, iter: Iter) -> Result<(), NotAllDroppedError<Item>>
        where K: Borrow<Q>,
              Q: Hash + Eq + ?Sized,
              Item: Borrow<Q>,
              Iter: IntoIterator<Item = Item>
    {
        // Vec won't allocate any memory until items are pushed to it, so if this method does not
        // fail, no memory will be allocated
        let mut err = NotAllDroppedError {
            alive: Vec::new(),
            untracked: Vec::new(),
        };

        for key in iter {
            match self.try_state(key.borrow()) {
                Ok(State::Alive) => err.alive.push(key),
                Ok(State::Dropped) => (),
                Err(NotTrackedError) => err.untracked.push(key),
            }
        }

        if err.alive.is_empty() && err.untracked.is_empty() {
            Ok(())
        } else {
            Err(err)
        }
    }

    /// Returns [`Ok`] if all the keys tracked are [alive](State::Alive), [`Err`] otherwise.
    ///
    /// The error returned references an arbitrary keys that was found [dropped](State::Dropped).
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::SomeDroppedError;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track(1);
    /// let item2 = tracker.track(2);
    /// let item3 = tracker.track(3);
    ///
    /// assert_eq!(tracker.fully_alive(), Ok(()));
    ///
    /// drop(item1);
    ///
    /// assert_eq!(tracker.fully_alive(), Err(SomeDroppedError { dropped: &1 }));
    /// ```
    pub fn fully_alive(&self) -> Result<(), SomeDroppedError<'_, K>> {
        let dropped = self.tracked.iter()
                          .find(|(_, state)| state.is_dropped())
                          .map(|(key, _)| key);
        match dropped {
            None => Ok(()),
            Some(dropped) => Err(SomeDroppedError { dropped }),
        }
    }

    /// Returns [`Ok`] if all the keys tracked are [dropped](State::Dropped), [`Err`] otherwise.
    ///
    /// The error returned references an arbitrary keys that was found [alive](State::Alive).
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_variables)]
    /// use drop_tracker::DropTracker;
    /// use drop_tracker::SomeAliveError;
    ///
    /// let mut tracker = DropTracker::new();
    ///
    /// let item1 = tracker.track(1);
    /// let item2 = tracker.track(2);
    /// let item3 = tracker.track(3);
    ///
    /// drop(item1);
    /// drop(item2);
    ///
    /// assert_eq!(tracker.fully_dropped(), Err(SomeAliveError { alive: &3 }));
    ///
    /// drop(item3);
    ///
    /// assert_eq!(tracker.fully_dropped(), Ok(()));
    /// ```
    pub fn fully_dropped(&self) -> Result<(), SomeAliveError<'_, K>> {
        let alive = self.tracked.iter()
                        .find(|(_, state)| state.is_alive())
                        .map(|(key, _)| key);
        match alive {
            None => Ok(()),
            Some(alive) => Err(SomeAliveError { alive }),
        }
    }
}

/// An item that will notify the parent [`DropTracker`] once it gets dropped.
///
/// `DropItem` instances are created by [`DropTracker::track`], [`DropTracker::track_with_value`],
/// and related functions. `DropItem` instances may contain an "underlying value" that affects the
/// item behavior when used with standard traits. The underlying value is either:
///
/// * a clone of `key` when constructing an item using `track(key)` (implicit); or
/// * `value` when constructing an item using `track_with_value(key, value)` (explicit).
///
/// To check whether an item is alive or has been dropped, use [`DropTracker::state`] or see the
/// documentation for [`DropTracker`] for alternatives.
///
/// # Coercing and borrowing
///
/// `DropItem` instances may be [_coerced_](std::ops::Deref) and [_borrowed_](std::borrow::Borrow)
/// as the the underlying value type. This means that, for example, if you create a `DropItem`
/// using `track(String::from("abc"))`, you may call all of the `String` methods on that item.
///
/// `DropItem` also implements the standard traits [`PartialEq`](std::cmp::PartialEq),
/// [`Eq`](std::cmp::Eq), [`PartialOrd`](std::cmp::PartialOrd), [`Ord`](std::cmp::Ord) and
/// [`Hash`](std::hash::Hash), [`Display`](std::fmt::Display), [`Debug`](std::fmt::Debug) if the
/// type of the underlying value implements them.
///
/// # Cloning
///
/// `DropItem` does not implement the [`Clone`] trait as it would introduce ambiguity with respect
/// to understanding whether the item has been dropped or is still alive when using
/// [`DropTracker::state`].
///
/// # Double drop
///
/// `DropItem` instances can be dropped twice or more. Doing so will cause a panic, but will not
/// cause undefined behavior (unless you're calling drop on an invalid memory location). The panic
/// on double drop is an useful feature to detect logic errors in destructors.
///
/// # Safety
///
/// Borrowing or performing operations on the underlying value of a `DropItem` is generally safe
/// when using safe Rust code. However, `DropItem`s are often used in unsafe code and are used to
/// detect potential bugs. In those circumstances, it is possible to trigger undefined behavior.
/// In particular, borrowing or performing operations on a `DropItem` while another thread is
/// dropping will result in undefined behavior (although it must be noted that this is a bug in the
/// caller code and is not something that should happen in safe Rust code).
///
/// Only [`Drop`](std::ops::Drop) on a `DropItem` is guaranteed to be safe in all circumstances.
///
/// # Examples
///
/// ```
/// use drop_tracker::DropTracker;
///
/// let mut tracker = DropTracker::<u32>::new();
///
/// // Create an item using `123u32` as the key. Implicitly, this also sets its value to `123u32`
/// let item = tracker.track(123);
///
/// // Check that the item is alive
/// tracker.state(&123).alive().expect("item should be alive");
///
/// // Dereference the value of the item
/// assert_eq!(*item, 123);
/// assert!(!item.is_power_of_two());
///
/// // Drop the item and check that it really got dropped
/// drop(item);
/// tracker.state(&123).dropped().expect("item should be dropped");
///
/// // Create a new item, this time using an explicit `String` value
/// let abc_item = tracker.track_with_value(111, String::from("abc"));
///
/// // Comparison with other items using `String` work using the underlying `String`
/// // operations
/// assert_eq!(abc_item, tracker.track_with_value(222, String::from("abc")));
/// assert_ne!(abc_item, tracker.track_with_value(333, String::from("def")));
/// assert!(abc_item < tracker.track_with_value(444, String::from("def")));
///
/// // Display, debug and hashing also work using the underlying `String` operations
/// assert_eq!(format!("{}", abc_item), "abc");
/// assert_eq!(format!("{:?}", abc_item), "DropItem { value: \"abc\", state: Alive }");
///
/// use std::collections::hash_map::DefaultHasher;
/// use std::hash::Hash;
/// use std::hash::Hasher;
/// fn hash<T: Hash + ?Sized>(x: &T) -> u64 {
///     let mut hasher = DefaultHasher::new();
///     x.hash(&mut hasher);
///     hasher.finish()
/// }
/// assert_eq!(hash(&abc_item), hash(&"abc"));
///
/// // Methods on `String` can be called transparently on items
/// assert_eq!(abc_item.to_ascii_uppercase(), "ABC");
/// ```
///
/// Using hashable items in a set, with an implicit underlying value:
///
/// ```
/// use drop_tracker::DropTracker;
/// use std::collections::HashSet;
///
/// let mut tracker = DropTracker::new();
///
/// let mut set = HashSet::from([
///     tracker.track(1),
///     tracker.track(2),
///     tracker.track(3),
/// ]);
///
/// set.remove(&3);
///
/// tracker.state(&1).alive().expect("first item should be alive");
/// tracker.state(&2).alive().expect("second item should be alive");
/// tracker.state(&3).dropped().expect("third item should be dropped");
/// ```
///
/// Using hashable items in a set, with an explicit underlying value:
///
/// ```
/// use drop_tracker::DropTracker;
/// use std::collections::HashSet;
///
/// let mut tracker = DropTracker::new();
///
/// let mut set = HashSet::from([
///     tracker.track_with_value(1, String::from("first")),
///     tracker.track_with_value(2, String::from("second")),
///     tracker.track_with_value(3, String::from("third")),
/// ]);
///
/// set.remove("third");
///
/// tracker.state(&1).alive().expect("first item should be alive");
/// tracker.state(&2).alive().expect("second item should be alive");
/// tracker.state(&3).dropped().expect("third item should be dropped");
/// ```
#[must_use = "if you don't use this item, it will get automatically dropped"]
pub struct DropItem<V> {
    value: MaybeUninit<V>,
    state: Option<StateCell>,
}

impl<V> DropItem<V> {
    const fn new(value: V, state: StateCell) -> Self {
        Self {
            value: MaybeUninit::new(value),
            state: Some(state),
        }
    }
}

impl<V> Drop for DropItem<V> {
    fn drop(&mut self) {
        // The use of an Option might seem redundant, but it's actually needed to safely detect and
        // report double drops. Without the Option, we would be touching shared memory behind an Rc
        // that probably does not exist anymore, causing memory corruption. The Option makes this a
        // bit safer (assuming that the DropItem memory has not been moved or altered), and also
        // prevents a double drop on the Rc.
        match self.state.take() {
            Some(mut state) => {
                if state.replace(State::Dropped).is_dropped() {
                    panic!("item dropped twice");
                }
                // SAFETY: `state` was `Some(State::Alive)`, which means that `value` has not been
                // dropped yet and that `value` is initialized.
                unsafe { self.value.assume_init_drop() };
            },
            None => {
                panic!("item dropped twice");
            },
        }
    }
}

/// Error signaling that an item was expected to have been dropped, but it's [alive](State::Alive).
///
/// See [`State::dropped`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct AliveError;

impl fmt::Display for AliveError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt("item is alive", f)
    }
}

impl Error for AliveError {
}

/// Error signaling that an item was expected to be alive, but it was [dropped](State::Dropped).
///
/// See [`State::alive`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct DroppedError;

impl fmt::Display for DroppedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt("item is dropped", f)
    }
}

impl Error for DroppedError {
}

/// Error returned when trying to place multiple items with the same key inside the same [`DropTracker`].
///
/// See [`DropTracker::try_track`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct CollisionError;

impl fmt::Display for CollisionError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt("another item with the same key is already tracked", f)
    }
}

impl Error for CollisionError {
}

/// Error returned when failing to query the status of an item with a key that is not known to [`DropTracker`].
///
/// See [`DropTracker::try_state`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct NotTrackedError;

impl fmt::Display for NotTrackedError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt("item is not tracked", f)
    }
}

impl Error for NotTrackedError {
}

/// Error returned when failing to assert that a set of items is all [alive](State::Alive).
///
/// See [`DropTracker::all_alive`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct NotAllAliveError<K> {
    /// Sequence of keys that were expected to be alive, but were dropped.
    pub dropped: Vec<K>,
    /// Sequence of keys that were expected to be alive, but are not tracked by the
    /// [`DropTracker`].
    pub untracked: Vec<K>,
}

impl<K: fmt::Debug> fmt::Display for NotAllAliveError<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "not all items are alive: ")?;
        if !self.dropped.is_empty() {
            write!(f, "dropped: {:?}", &self.dropped)?;
        }
        if !self.untracked.is_empty() {
            if !self.dropped.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "not tracked: {:?}", &self.untracked)?;
        }
        Ok(())
    }
}

impl<K: fmt::Debug> Error for NotAllAliveError<K> {
}

/// Error returned when failing to assert that a set of items is all [dropped](State::Dropped).
///
/// See [`DropTracker::all_dropped`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct NotAllDroppedError<K> {
    /// Sequence of keys that were expected to be dropped, but are alive.
    pub alive: Vec<K>,
    /// Sequence of keys that were expected to be dropped, but are not tracked by the
    /// [`DropTracker`].
    pub untracked: Vec<K>,
}

impl<K: fmt::Debug> fmt::Display for NotAllDroppedError<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "not all items are dropped: ")?;
        if !self.alive.is_empty() {
            write!(f, "alive: {:?}", &self.alive)?;
        }
        if !self.untracked.is_empty() {
            if !self.alive.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "not tracked: {:?}", &self.untracked)?;
        }
        Ok(())
    }
}

impl<K: fmt::Debug> Error for NotAllDroppedError<K> {
}

/// Error returned when failing to assert that all tracked items are [dropped](State::Dropped).
///
/// See [`DropTracker::fully_dropped`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct SomeAliveError<'a, K> {
    /// Reference to the first key that was found [alive](State::Alive).
    pub alive: &'a K,
}

impl<'a, K: fmt::Debug> fmt::Display for SomeAliveError<'a, K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "item is alive: {:?}", self.alive)
    }
}

impl<'a, K: fmt::Debug> Error for SomeAliveError<'a, K> {
}

/// Error returned when failing to assert that all tracked items are [alive](State::Alive).
///
/// See [`DropTracker::fully_alive`] for more information and examples.
#[derive(PartialEq, Eq, Debug)]
pub struct SomeDroppedError<'a, K> {
    /// Reference to the first key that was found to have been be [dropped](State::Dropped).
    pub dropped: &'a K,
}

impl<'a, K: fmt::Debug> fmt::Display for SomeDroppedError<'a, K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "item is dropped: {:?}", self.dropped)
    }
}

impl<'a, K: fmt::Debug> Error for SomeDroppedError<'a, K> {
}
