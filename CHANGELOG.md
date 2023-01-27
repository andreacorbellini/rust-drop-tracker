# Changelog

## drop-tracker 0.1.2

* Added assertions methods to `DropTracker` (`assert_alive()`,
  `assert_dropped()`, etc) to make test code more concise.

* Added `fully_alive()` and `fully_dropped()` to `DropTracker` to quickly check
  if all the tracked keys are in a the desired state.

* `DropItem` now implements traits to compare its keys with primitive types
  (`i32`, `char`, `bool`, `str`, ...).

## drop-tracker 0.1.1

* `DropItem` can now hold arbitrary values, making it easy to implement items
  that are comparable and hashable.

* `DropItem` is now marked with `#[must_use]`.

## drop-tracker 0.1.0

* Initial release
