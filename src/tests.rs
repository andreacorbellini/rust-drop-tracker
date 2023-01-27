#![cfg(test)]

use crate::DropTracker;
use crate::State::Alive;
use crate::State::Dropped;
use std::collections::HashSet;
use std::mem::ManuallyDrop;
use std::panic::UnwindSafe;
use std::panic;

#[test]
fn state() {
    let mut tracker = DropTracker::new();

    let item = tracker.track(123);
    assert_eq!(tracker.state(&123), Alive);
    assert!(tracker.state(&123).is_alive());
    assert!(!tracker.state(&123).is_dropped());

    drop(item);
    assert_eq!(tracker.state(&123), Dropped);
    assert!(!tracker.state(&123).is_alive());
    assert!(tracker.state(&123).is_dropped());
}

#[test]
fn iterators() {
    let mut tracker = DropTracker::new();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    let item1 = tracker.track(1);
    let item2 = tracker.track(2);
    let item3 = tracker.track(3);
    let item4 = tracker.track(4);
    let item5 = tracker.track(5);

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    drop(item1);
    drop(item2);

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([3, 4, 5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2]));

    drop(item3);
    drop(item4);

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4]));

    drop(item5);

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
}

#[test]
fn forget_dropped() {
    let mut tracker = DropTracker::new();
    tracker.forget_dropped();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    let item1 = tracker.track(1);
    let item2 = tracker.track(2);
    let item3 = tracker.track(3);
    let item4 = tracker.track(4);
    let item5 = tracker.track(5);
    tracker.forget_dropped();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([1, 2, 3, 4, 5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    drop(item1);
    drop(item2);
    tracker.forget_dropped();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([3, 4, 5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([3, 4, 5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    drop(item3);
    drop(item4);
    tracker.forget_dropped();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([5]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([5]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));

    drop(item5);
    tracker.forget_dropped();

    assert_eq!(tracker.tracked().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.alive().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
    assert_eq!(tracker.dropped().copied().collect::<HashSet<_>>(),
               HashSet::from([]));
}

fn catch_panic_error<F: FnOnce() + UnwindSafe>(f: F) -> String {
    let err = panic::catch_unwind(f)
                    .expect_err("expected a panic");
    if let Some(s) = err.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = err.downcast_ref::<String>() {
        s.clone()
    } else {
        panic!("expected the panic payload to be a string");
    }
}

#[test]
fn state_errors() {
    let mut tracker = DropTracker::new();
    let item = tracker.track(());

    let state = tracker.state(&());
    let err = state.dropped()
                   .expect_err("item is expected to be alive");
    assert_eq!(err.to_string(), "item is alive");

    let panic_err = catch_panic_error(move || state.dropped().expect("foo"));
    assert_eq!(panic_err, "foo: AliveError");

    drop(item);

    let state = tracker.state(&());
    let err = state.alive()
                   .expect_err("item is expected to be dropped");
    assert_eq!(err.to_string(), "item is dropped");

    let panic_err = catch_panic_error(move || state.alive().expect("foo"));
    assert_eq!(panic_err, "foo: DroppedError");
}

#[test]
fn all_alive() {
    let mut tracker = DropTracker::new();

    let item1 = tracker.track(1);
    let item2 = tracker.track(2);
    let item3 = tracker.track(3);
    let item4 = tracker.track(4);

    drop(item3);
    drop(item4);

    let res = tracker.all_alive([&1, &2]);
    assert_eq!(res, Ok(()));

    let err = tracker.all_alive([&1, &2, &3, &4, &5, &6])
                     .expect_err("not all items are expected to be alive");
    assert_eq!(err.dropped, [&3, &4]);
    assert_eq!(err.untracked, [&5, &6]);
    assert_eq!(err.to_string(), "not all items are alive: dropped: [3, 4], not tracked: [5, 6]");

    let res = tracker.all_alive([&1, &2, &3, &4, &5, &6]);
    let panic_err = catch_panic_error(move || res.expect("foo"));
    assert_eq!(panic_err, "foo: NotAllAliveError { dropped: [3, 4], untracked: [5, 6] }");

    drop(item1);
    drop(item2);
}

#[test]
fn all_dropped() {
    let mut tracker = DropTracker::new();

    let item1 = tracker.track(1);
    let item2 = tracker.track(2);
    let item3 = tracker.track(3);
    let item4 = tracker.track(4);

    drop(item3);
    drop(item4);

    let res = tracker.all_dropped([&3, &4]);
    assert_eq!(res, Ok(()));

    let err = tracker.all_dropped([&1, &2, &3, &4, &5, &6])
                     .expect_err("not all items are expected to be dropped");
    assert_eq!(err.alive, [&1, &2]);
    assert_eq!(err.untracked, [&5, &6]);
    assert_eq!(err.to_string(), "not all items are dropped: alive: [1, 2], not tracked: [5, 6]");

    let res = tracker.all_dropped([&1, &2, &3, &4, &5, &6]);
    let panic_err = catch_panic_error(move || res.expect("foo"));
    assert_eq!(panic_err, "foo: NotAllDroppedError { alive: [1, 2], untracked: [5, 6] }");

    drop(item1);
    drop(item2);
}

#[test]
fn double_drop() {
    let mut tracker = DropTracker::new();

    let mut item = ManuallyDrop::new(tracker.track(()));
    tracker.state(&()).alive().expect("item should be alive");

    unsafe { ManuallyDrop::drop(&mut item); }
    tracker.state(&()).dropped().expect("item should be dropped");

    // Our DropItem implementation is safe and can be dropped twice or more
    let panic_err = catch_panic_error(panic::AssertUnwindSafe(
        || unsafe { ManuallyDrop::drop(&mut item) }
    ));
    assert_eq!(panic_err, "item dropped twice");
}

#[test]
fn assertions() {
    let mut tracker = DropTracker::new();

    tracker.assert_all_alive([0u32; 0]);
    tracker.assert_all_dropped([0u32; 0]);
    tracker.assert_fully_alive();
    tracker.assert_fully_dropped();

    let panic_err = catch_panic_error(|| tracker.assert_alive(&1));
    assert_eq!(panic_err, "item is not tracked");
    let panic_err = catch_panic_error(|| tracker.assert_dropped(&1));
    assert_eq!(panic_err, "item is not tracked");
    let panic_err = catch_panic_error(|| tracker.assert_all_alive([1]));
    assert_eq!(panic_err, "not all items are alive: not tracked: [1]");
    let panic_err = catch_panic_error(|| tracker.assert_all_dropped([1]));
    assert_eq!(panic_err, "not all items are dropped: not tracked: [1]");

    let item = tracker.track(1);

    tracker.assert_alive(&1);
    tracker.assert_all_alive([1]);
    tracker.assert_fully_alive();

    let panic_err = catch_panic_error(|| tracker.assert_dropped(&1));
    assert_eq!(panic_err, "item is alive");
    let panic_err = catch_panic_error(|| tracker.assert_all_dropped([1]));
    assert_eq!(panic_err, "not all items are dropped: alive: [1]");
    let panic_err = catch_panic_error(|| tracker.assert_fully_dropped());
    assert_eq!(panic_err, "item is alive: 1");

    drop(item);

    tracker.assert_dropped(&1);
    tracker.assert_all_dropped([1]);
    tracker.assert_fully_dropped();

    let panic_err = catch_panic_error(|| tracker.assert_alive(&1));
    assert_eq!(panic_err, "item is dropped");
    let panic_err = catch_panic_error(|| tracker.assert_all_alive([1]));
    assert_eq!(panic_err, "not all items are alive: dropped: [1]");
    let panic_err = catch_panic_error(|| tracker.assert_fully_alive());
    assert_eq!(panic_err, "item is dropped: 1");
}

#[test]
fn primitive_eq() {
    assert_eq!(DropTracker::new().track(123i8),                  123i8);
    assert_eq!(DropTracker::new().track(123i16),                 123i16);
    assert_eq!(DropTracker::new().track(123i32),                 123i32);
    assert_eq!(DropTracker::new().track(123i64),                 123i64);
    assert_eq!(DropTracker::new().track(123i128),                123i128);

    assert_eq!(DropTracker::new().track(123u8),                  123u8);
    assert_eq!(DropTracker::new().track(123u16),                 123u16);
    assert_eq!(DropTracker::new().track(123u32),                 123u32);
    assert_eq!(DropTracker::new().track(123u64),                 123u64);
    assert_eq!(DropTracker::new().track(123u128),                123u128);

    assert_eq!(DropTracker::new().track_with_value('a', 123f32), 123f32);
    assert_eq!(DropTracker::new().track_with_value('b', 123f64), 123f64);

    assert_eq!(DropTracker::new().track('x'),                    'x');
    assert_eq!(DropTracker::new().track(true),                   true);
    assert_eq!(DropTracker::new().track(false),                  false);
    assert_eq!(DropTracker::new().track(()),                     ());
    assert_eq!(DropTracker::new().track("abc"),                  "abc");
    assert_eq!(DropTracker::new().track("abc".to_owned()),       "abc");
    assert_eq!(DropTracker::new().track([1, 2, 3]),              [1, 2, 3][..]);
    assert_eq!(DropTracker::new().track(vec![1, 2, 3]),          [1, 2, 3][..]);

    assert_eq!(123i8,         DropTracker::new().track(123i8));
    assert_eq!(123i16,        DropTracker::new().track(123i16));
    assert_eq!(123i32,        DropTracker::new().track(123i32));
    assert_eq!(123i64,        DropTracker::new().track(123i64));
    assert_eq!(123i128,       DropTracker::new().track(123i128));

    assert_eq!(123u8,         DropTracker::new().track(123u8));
    assert_eq!(123u16,        DropTracker::new().track(123u16));
    assert_eq!(123u32,        DropTracker::new().track(123u32));
    assert_eq!(123u64,        DropTracker::new().track(123u64));
    assert_eq!(123u128,       DropTracker::new().track(123u128));

    assert_eq!(123f32,        DropTracker::new().track_with_value('a', 123f32));
    assert_eq!(123f64,        DropTracker::new().track_with_value('b', 123f64));

    assert_eq!('x',           DropTracker::new().track('x'));
    assert_eq!(true,          DropTracker::new().track(true));
    assert_eq!(false,         DropTracker::new().track(false));
    assert_eq!((),            DropTracker::new().track(()));
    assert_eq!("abc",         DropTracker::new().track("abc"));
    assert_eq!("abc",         DropTracker::new().track("abc".to_owned()));
    assert_eq!([1, 2, 3][..], DropTracker::new().track([1, 2, 3]));
    assert_eq!([1, 2, 3][..], DropTracker::new().track(vec![1, 2, 3]));
}

#[test]
fn primitive_ne() {
    assert_ne!(DropTracker::new().track(123i8),                  100i8);
    assert_ne!(DropTracker::new().track(123i16),                 100i16);
    assert_ne!(DropTracker::new().track(123i32),                 100i32);
    assert_ne!(DropTracker::new().track(123i64),                 100i64);
    assert_ne!(DropTracker::new().track(123i128),                100i128);

    assert_ne!(DropTracker::new().track(123u8),                  100u8);
    assert_ne!(DropTracker::new().track(123u16),                 100u16);
    assert_ne!(DropTracker::new().track(123u32),                 100u32);
    assert_ne!(DropTracker::new().track(123u64),                 100u64);
    assert_ne!(DropTracker::new().track(123u128),                100u128);

    assert_ne!(DropTracker::new().track_with_value('a', 123f32), 100f32);
    assert_ne!(DropTracker::new().track_with_value('b', 123f64), 100f64);

    assert_ne!(DropTracker::new().track('x'),                    'y');
    assert_ne!(DropTracker::new().track(true),                   false);
    assert_ne!(DropTracker::new().track(false),                  true);
    assert_ne!(DropTracker::new().track("abc"),                  "def");
    assert_ne!(DropTracker::new().track("abc".to_owned()),       "def");
    assert_ne!(DropTracker::new().track([1, 2, 3]),              [4, 5, 6][..]);
    assert_ne!(DropTracker::new().track(vec![1, 2, 3]),          [4, 5, 6][..]);

    assert_ne!(100i8,         DropTracker::new().track(123i8));
    assert_ne!(100i16,        DropTracker::new().track(123i16));
    assert_ne!(100i32,        DropTracker::new().track(123i32));
    assert_ne!(100i64,        DropTracker::new().track(123i64));
    assert_ne!(100i128,       DropTracker::new().track(123i128));

    assert_ne!(100u8,         DropTracker::new().track(123u8));
    assert_ne!(100u16,        DropTracker::new().track(123u16));
    assert_ne!(100u32,        DropTracker::new().track(123u32));
    assert_ne!(100u64,        DropTracker::new().track(123u64));
    assert_ne!(100u128,       DropTracker::new().track(123u128));

    assert_ne!(100f32,        DropTracker::new().track_with_value('a', 123f32));
    assert_ne!(100f64,        DropTracker::new().track_with_value('b', 123f64));

    assert_ne!('y',           DropTracker::new().track('x'));
    assert_ne!(false,         DropTracker::new().track(true));
    assert_ne!(true,          DropTracker::new().track(false));
    assert_ne!("def",         DropTracker::new().track("abc"));
    assert_ne!("def",         DropTracker::new().track("abc".to_owned()));
    assert_ne!([4, 5, 6][..], DropTracker::new().track([1, 2, 3]));
    assert_ne!([4, 5, 6][..], DropTracker::new().track(vec![1, 2, 3]));
}

#[test]
fn primitive_lt() {
    assert!(DropTracker::new().track(123i8)                  < 127i8);
    assert!(DropTracker::new().track(123i16)                 < 200i16);
    assert!(DropTracker::new().track(123i32)                 < 200i32);
    assert!(DropTracker::new().track(123i64)                 < 200i64);
    assert!(DropTracker::new().track(123i128)                < 200i128);

    assert!(DropTracker::new().track(123u8)                  < 200u8);
    assert!(DropTracker::new().track(123u16)                 < 200u16);
    assert!(DropTracker::new().track(123u32)                 < 200u32);
    assert!(DropTracker::new().track(123u64)                 < 200u64);
    assert!(DropTracker::new().track(123u128)                < 200u128);

    assert!(DropTracker::new().track_with_value('a', 123f32) < 200f32);
    assert!(DropTracker::new().track_with_value('b', 123f64) < 200f64);

    assert!(DropTracker::new().track('x')                    < 'y');
    assert!(DropTracker::new().track(false)                  < true);

    assert!(100i8   < DropTracker::new().track(123i8));
    assert!(100i16  < DropTracker::new().track(123i16));
    assert!(100i32  < DropTracker::new().track(123i32));
    assert!(100i64  < DropTracker::new().track(123i64));
    assert!(100i128 < DropTracker::new().track(123i128));

    assert!(100u8   < DropTracker::new().track(123u8));
    assert!(100u16  < DropTracker::new().track(123u16));
    assert!(100u32  < DropTracker::new().track(123u32));
    assert!(100u64  < DropTracker::new().track(123u64));
    assert!(100u128 < DropTracker::new().track(123u128));

    assert!(100f32  < DropTracker::new().track_with_value('a', 123f32));
    assert!(100f64  < DropTracker::new().track_with_value('b', 123f64));

    assert!('w'     < DropTracker::new().track('x'));
    assert!(false   < DropTracker::new().track(true));
}

#[test]
fn primitive_gt() {
    assert!(DropTracker::new().track(123i8)                  > 100i8);
    assert!(DropTracker::new().track(123i16)                 > 100i16);
    assert!(DropTracker::new().track(123i32)                 > 100i32);
    assert!(DropTracker::new().track(123i64)                 > 100i64);
    assert!(DropTracker::new().track(123i128)                > 100i128);

    assert!(DropTracker::new().track(123u8)                  > 100u8);
    assert!(DropTracker::new().track(123u16)                 > 100u16);
    assert!(DropTracker::new().track(123u32)                 > 100u32);
    assert!(DropTracker::new().track(123u64)                 > 100u64);
    assert!(DropTracker::new().track(123u128)                > 100u128);

    assert!(DropTracker::new().track_with_value('a', 123f32) > 100f32);
    assert!(DropTracker::new().track_with_value('b', 123f64) > 100f64);

    assert!(DropTracker::new().track('x')                    > 'w');
    assert!(DropTracker::new().track(true)                   > false);

    assert!(127i8   > DropTracker::new().track(123i8));
    assert!(200i16  > DropTracker::new().track(123i16));
    assert!(200i32  > DropTracker::new().track(123i32));
    assert!(200i64  > DropTracker::new().track(123i64));
    assert!(200i128 > DropTracker::new().track(123i128));

    assert!(200u8   > DropTracker::new().track(123u8));
    assert!(200u16  > DropTracker::new().track(123u16));
    assert!(200u32  > DropTracker::new().track(123u32));
    assert!(200u64  > DropTracker::new().track(123u64));
    assert!(200u128 > DropTracker::new().track(123u128));

    assert!(200f32  > DropTracker::new().track_with_value('a', 123f32));
    assert!(200f64  > DropTracker::new().track_with_value('b', 123f64));

    assert!('y'     > DropTracker::new().track('x'));
    assert!(true    > DropTracker::new().track(false));
}
