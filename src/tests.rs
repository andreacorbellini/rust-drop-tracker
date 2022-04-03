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
