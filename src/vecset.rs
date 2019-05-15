use std::borrow::Borrow;
use std::ops::{Deref, DerefMut};
use std::slice::{Iter, IterMut};

#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
pub enum Order {
    /// The set is always Sorted.
    Sorted,

    /// No order constraint.
    Unsorted,
}

pub struct VecSet<T, const ORDER: Order> {
    inner: Vec<T>,
}

impl <T, const ORDER: Order> VecSet<T, { ORDER }> {
    /// Returns the [`Order`] of the set.
    #[inline(always)]
    pub const fn order(&self) -> Order {
        ORDER
    }

    /// Pops an item from the set
    #[inline(always)]
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    /// Returns an iterator over the set.
    #[inline(always)]
    pub fn iter(&self) -> Iter<T> {
        self.inner.iter()
    }
}


impl<T> VecSet<T, { Order::Sorted }> {
    /// Returns true if the set contains `item`, false otherwise.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    /// use vecset::vecset::{Order, VecSet};
    ///
    /// let mut set = VecSet::<_, { Order::Sorted}>::new();
    /// set.push(String::from("hello"));
    /// set.push(String::from("world"));
    /// assert!(set.contains("hello"));
    /// ```
    #[inline]
    pub fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        match self.inner.binary_search_by(|elem| elem.borrow().cmp(item)) {
            Ok(_) => true,
            Err(_) => false,
        }
    }

    /// Converts the set into an Unsorted Set.
    #[inline]
    pub fn into_unsorted(self) -> VecSet<T, { Order::Unsorted }> {
        VecSet::<T, { Order::Unsorted }> { inner: self.inner }
    }
}

impl<T: Ord> VecSet<T, { Order::Sorted }> {
    /// Pushes `item` into the set.
    /// Returns `true` if the item was already in the set, `false` otherwise.
    #[inline]
    pub fn push(&mut self, item: T) -> bool {
        match self.inner.binary_search(&item) {
            Ok(_) => true,
            Err(idx) => {
                if idx > self.inner.len() {
                    self.inner.push(item);
                } else {
                    self.inner.insert(idx, item);
                }
                false
            }
        }
    }
}

impl<T> VecSet<T, { Order::Unsorted }> {

    /// Pushes `item` into the set.
    #[inline]
    pub fn push(&mut self, item: T) {
        self.inner.push(item)
    }

    /// Returns true if the set contains `item`, false otherwise.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    /// use vecset::vecset::{Order, VecSet};
    ///
    /// let mut set = VecSet::<_, { Order::Unsorted}>::new();
    /// set.push(String::from("hello"));
    /// set.push(String::from("world"));
    /// assert!(set.contains("hello"));
    /// ```
    #[inline]
    pub fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.inner
            .iter()
            .find(|elem| (*elem).borrow() == item)
            .is_some()
    }

    /// Returns an iterator that allows modifying each value.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T> {
        self.inner.iter_mut()
    }
}

impl<T: Ord> VecSet<T, { Order::Unsorted }> {
    /// Converts the set into a Sorted set.
    #[inline]
    pub fn into_sorted(mut self) -> VecSet<T, { Order::Sorted }> {
        self.inner.sort();

        VecSet::<T, { Order::Sorted }> { inner: self.inner }
    }
}

macro_rules! impl_vecset {
    ($($impls:tt)*) => {
        impl <T> VecSet<T, {Order::Sorted}> {
            $($impls)*
        }

        impl <T> VecSet<T, {Order::Unsorted}> {
            $($impls)*
        }
    }
}

impl_vecset!(
    /// Creates a new VecSet with the specified order.
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }
);

impl<T, const ORDER: Order> Deref for VecSet<T, { ORDER }> {
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T> DerefMut for VecSet<T, { Order::Unsorted }> {

    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsorted() {
        let mut set = VecSet::<_, { Order::Unsorted }>::new();
        set.push(String::from("hello"));
        set.push(String::from("world"));

        assert!(set.contains("hello"));

        assert_eq!(set.pop(), Some(String::from("world")));
        assert_eq!(set.pop(), Some(String::from("hello")));
    }

    #[test]
    fn test_sorted() {
        let mut set = VecSet::<_, { Order::Sorted }>::new();
        set.push(10);
        set.push(5);
        set.push(22);

        assert!(set.contains(&22));

        assert_eq!(set.pop(), Some(22));
        assert_eq!(set.pop(), Some(10));
        assert_eq!(set.pop(), Some(5));

        let mut unordered = set.into_unsorted();
        assert!(unordered.order() == Order::Unsorted);

        let x: &[i32] = unordered.deref_mut();
    }
}
