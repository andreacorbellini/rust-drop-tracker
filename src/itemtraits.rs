use crate::DropItem;
use crate::DroppedError;
use crate::State;
use std::borrow::Borrow;
use std::borrow::BorrowMut;
use std::cmp::Ordering;
use std::fmt;
use std::hash;
use std::ops::Deref;
use std::ops::DerefMut;

impl<V> DropItem<V> {
    fn inner_ref(&self) -> &V {
        self.try_inner_ref().expect("cannot borrow value")
    }

    fn try_inner_ref(&self) -> Result<&V, DroppedError> {
        match self.state {
            Some(ref state) if state.is_alive() => {
                // SAFETY: The item is alive. It is possible that another thread may have dropped
                // the item since we last checked, but in that case it's the caller's
                // responsibility to ensure safety.
                Ok(unsafe { self.value.assume_init_ref() })
            },
            _ => Err(DroppedError),
        }
    }

    fn inner_mut(&mut self) -> &mut V {
        self.try_inner_mut().expect("cannot borrow mutable value")
    }

    fn try_inner_mut(&mut self) -> Result<&mut V, DroppedError> {
        match self.state {
            Some(ref state) if state.is_alive() => {
                // SAFETY: The item is alive. It is possible that another thread may have dropped
                // the item since we last checked, but in that case it's the caller's
                // responsibility to ensure safety.
                Ok(unsafe { self.value.assume_init_mut() })
            },
            _ => Err(DroppedError),
        }
    }
}

impl<V> Deref for DropItem<V> {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        self.inner_ref()
    }
}

impl<V> DerefMut for DropItem<V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner_mut()
    }
}

macro_rules! impl_ref_trait {
    () => {};
    ( impl <{ $( $params:tt )* }> Borrow < $target:ty > for DropItem < $type_bound:ty > ; $( $rest:tt )* ) => {
        impl<$($params)*> Borrow<$target> for DropItem<$type_bound> {
            #[inline(always)]
            fn borrow(&self) -> &$target {
                self.inner_ref().borrow()
            }
        }

        impl_ref_trait! { $($rest)* }
    };
    ( impl <{ $( $params:tt )* }> BorrowMut < $target:ty > for DropItem < $type_bound:ty > ; $( $rest:tt )* ) => {
        impl<$($params)*> BorrowMut<$target> for DropItem<$type_bound> {
            #[inline(always)]
            fn borrow_mut(&mut self) -> &mut $target {
                self.inner_mut().borrow_mut()
            }
        }

        impl_ref_trait! { $($rest)* }
    };
    ( impl <{ $( $params:tt )* }> AsRef < $target:ty > for DropItem < $type_bound:ty > ; $( $rest:tt )* ) => {
        impl<$($params)*> AsRef<$target> for DropItem<$type_bound> {
            #[inline(always)]
            fn as_ref(&self) -> &$target {
                self.inner_ref().as_ref()
            }
        }

        impl_ref_trait! { $($rest)* }
    };
    ( impl <{ $( $params:tt )* }> AsMut < $target:ty > for DropItem < $type_bound:ty > ; $( $rest:tt )* ) => {
        impl<$($params)*> AsMut<$target> for DropItem<$type_bound> {
            #[inline(always)]
            fn as_mut(&mut self) -> &mut $target {
                self.inner_mut().as_mut()
            }
        }

        impl_ref_trait! { $($rest)* }
    };
}

impl_ref_trait! {
    impl<{V}>                       Borrow<V>       for DropItem<V>;
    impl<{V: Borrow<str>}>          Borrow<str>     for DropItem<V>;
    impl<{V: Borrow<[T]>, T}>       Borrow<[T]>     for DropItem<V>;

    impl<{V}>                       BorrowMut<V>    for DropItem<V>;
    impl<{V: BorrowMut<str>}>       BorrowMut<str>  for DropItem<V>;
    impl<{V: BorrowMut<[T]>, T}>    BorrowMut<[T]>  for DropItem<V>;

    impl<{V: AsRef<T>, T}>          AsRef<T>        for DropItem<V>;
    impl<{V: AsMut<T>, T}>          AsMut<T>        for DropItem<V>;
}

impl<V: PartialEq<W>, W> PartialEq<DropItem<W>> for DropItem<V> {
    fn eq(&self, other: &DropItem<W>) -> bool {
        self.inner_ref().eq(other.inner_ref())
    }
}

impl<V: Eq> Eq for DropItem<V> {
}

impl<V: PartialOrd<W>, W> PartialOrd<DropItem<W>> for DropItem<V> {
    fn partial_cmp(&self, other: &DropItem<W>) -> Option<Ordering> {
        self.inner_ref().partial_cmp(other.inner_ref())
    }
}

impl<V: hash::Hash> hash::Hash for DropItem<V> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner_ref().hash(state)
    }
}

impl<V: fmt::Display> fmt::Display for DropItem<V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.inner_ref().fmt(f)
    }
}

impl<V: fmt::Debug> fmt::Debug for DropItem<V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.try_inner_ref() {
            Ok(value) => {
                f.debug_struct("DropItem")
                 .field("value", value)
                 .field("state", &State::Alive)
                 .finish()
            },
            Err(_) => {
                f.debug_struct("DropItem")
                 .field("value", &"<dropped>")
                 .field("state", &State::Dropped)
                 .finish()
            }
        }
    }
}
