use crate::{
    sliceset::{SearchResult, SliceSet},
    entry::{Entry, VacantEntry, OccupiedEntry},
    order::Order,
};

use core::{
    borrow::Borrow,
    iter::FromIterator,
    ops::{Deref, DerefMut, RangeBounds},
    slice::{Iter, IterMut},
};

use alloc::vec::{Drain, IntoIter, Vec};

/// A vecset is a set of items.
/// It is paremeterized with an [`Order`], to denote whether
/// the set is always Ordered, or Unordered.
/// A Ordered set is guaranteed to always be sorted,
/// and contains no duplicates,
/// while in an Unordered set, the order is unspecified,
/// and may contain duplicates.
///
/// To convert a Ordered set into an Unordered set, or vice versa,
/// use the [`VecSet::into_sorted`] and [`VecSet::into_unsorted`] methods.
///
/// Items in a Ordered set can not be mutated, as that mutations change their order.
/// To mutate the items, use the [`VecSet::mutate_in_place`] method.
/// # Examples
/// ```
/// #![feature(const_generics)]
/// use vecset::vecset::{Order, VecSet, Entry};
///
/// let mut set = (0..10).rev().collect::<VecSet<_, {Order::Ordered}>>();
///
/// assert!(set.contains(&9));
///
/// match set.entry(15) {
///     Entry::Occupied(entry) => {
///         entry.remove();
///     },
///     Entry::Vacant(entry) => {
///         entry.insert();
///     }
/// }
///
/// assert!(set.remove(&15));
/// assert!(!set.contains(&15));
///
/// assert_eq!(set.as_slice, &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9])
/// ```
pub struct VecSet<T, const ORDER: Order> {
    pub(crate) inner: Vec<T>,
}

impl<T, const ORDER: Order> Default for VecSet<T, { ORDER }> {
    #[inline(always)]
    fn default() -> Self {
        VecSet::<T, { ORDER }> { inner: Vec::new() }
    }
}

/// Private implementations that *could* break
/// the invariant that a Ordered set is always sorted,
/// due to returning mutable references to the inners.
///
/// # Private
/// All methods in here are marked private because it is not known whether
/// `ORDER` is `Ordered`, in which case it is disallowed
/// to mutate any value within the set.
///
/// The public API uses these methods internally, but only exposes
/// what they see fit.
#[doc(hidden)]
impl<T, const ORDER: Order> VecSet<T, { ORDER }> {
    fn as_sliceset(&self) -> &SliceSet<T, { ORDER }> {
        <&SliceSet<T, { ORDER }>>::from(&**self)
    }

    fn as_sliceset_mut(&mut self) -> &mut SliceSet<T, { ORDER }> {
        <&mut SliceSet<T, { ORDER }>>::from(&mut *self.inner)
    }

    /// Searches for `item` in the set.
    /// Returns `Ok` with the corresponding index if the item is found,
    /// `Err` with the index `item` should be placed at otherwise.
    #[inline(always)]
    fn search<Q: ?Sized>(&self, item: &Q) -> SearchResult
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.as_sliceset().search(item)
    }

    /// Inserts `item` into the set if not present, then returns a reference to the value in the set.
    fn get_or_insert_priv(&mut self, item: T) -> &mut T
    where
        T: Ord,
    {
        self.entry(item).insert_priv()
    }
}

impl<T, const ORDER: Order> VecSet<T, { ORDER }> {
    /// Returns the [`Order`] of the set.
    #[inline(always)]
    pub const fn order(&self) -> Order {
        ORDER
    }

    /// Returns the length of the set.
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns the capacity of the set.
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns true if the set is empty.
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Pops the last item from the set
    #[inline(always)]
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    /// Returns an iterator over the set.
    #[inline(always)]
    pub fn iter(&self) -> Iter<T> {
        self.as_sliceset().iter()
    }

    /// Returns a slice over the set
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    /// Clears the set, removing all values.
    pub fn clear(&mut self) {
        self.inner.clear()
    }

    pub fn reserv(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }
    

    /// Converts the set into it's backing Vector.
    #[inline(always)]
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }

    /// Converts the set into an Unordered Set.
    #[inline]
    pub fn into_unordered(self) -> VecSet<T, { Order::Unordered }> {
        VecSet::<T, { Order::Unordered }> { inner: self.inner }
    }

    /// Converts the set into a Ordered set.
    #[inline]
    pub fn into_ordered(self) -> VecSet<T, { Order::Ordered }>
    where
        T: Ord,
    {
        // We need T: Ord here,
        // if the Order is Ordered already,
        // this bound is required anyway by most methods,
        // and if the order is Unordered, we need to sort the inner vector,
        // which requires T: Ord.
        let mut inner = self.inner;

        if ORDER.is_ordered() {
            VecSet::<T, { Order::Ordered }> { inner }
        } else {
            inner.sort();
            inner.dedup();
            VecSet::<T, { Order::Ordered }> { inner }
        }
    }

    /// Returns true if the set contains `item`, false otherwise.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    /// use vecset::vecset::{Order, VecSet};
    ///
    /// let mut set = VecSet::<_, { Order::Ordered}>::default();
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
        self.as_sliceset().contains(item)
    }

    /// Gets the given items entry in the map for in-place manipulations.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    ///
    /// use vecset::vecset::{Order, VecSet, Entry};
    /// let mut set = VecSet::<_, {Order::Unordered}>::default();
    ///
    /// set.push(10);
    /// set.push(11);
    ///
    /// for n in 10..13 {
    ///     match set.entry(n) {
    ///         Entry::Occupied(mut entry) => {
    ///             *entry.get_mut() += 10;
    ///         }
    ///         Entry::Vacant(entry) => {
    ///             entry.insert()
    ///         }
    ///     }
    /// }
    ///
    /// let slice = set.as_slice();
    ///
    /// assert_eq!(slice, &[20, 21, 12]);
    /// ```
    #[inline]
    pub fn entry(&mut self, item: T) -> Entry<T, { ORDER }>
    where
        T: Ord,
    {
        match self.search(&item) {
            Ok(idx) => Entry::Occupied(OccupiedEntry::<T, { ORDER }> {
                set: self,
                index: idx,
            }),
            Err(idx) => Entry::Vacant(VacantEntry::<T, { ORDER }> {
                entry: item,
                set: self,
                index: idx,
            }),
        }
    }

    /// Removes item from the set. Returns whether the value was present in the set.
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        match self.search(item) {
            Ok(idx) => {
                self.inner.remove(idx);
                true
            }
            Err(_) => false,
        }
    }

    /// Creates a draining iterator that removes the specified range in the set and yields the removed items.
    /// Note 1: The element range is removed even if the iterator is only partially consumed or not consumed at all.
    /// Note 2: It is unspecified how many elements are removed from the set if the Drain value is leaked.
    #[inline]
    pub fn drain<R>(&mut self, range: R) -> Drain<T>
    where
        R: RangeBounds<usize>,
    {
        self.inner.drain(range)
    }

    /// Retains the elements specified by the predicate.
    /// In other words, remove all elements that `f(&e)` returns false.
    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&T) -> bool,
    {
        self.inner.retain(f)
    }
}

impl<T: Ord> VecSet<T, { Order::Ordered }> {
    /// Inserts `item` into the set if not present, then returns a reference to the value in the set.
    pub fn get_or_insert(&mut self, item: T) -> &T {
        self.get_or_insert_priv(item)
    }

    /// Pushes `item` into the set.
    /// Returns `true` if the item was already in the set, `false` otherwise.
    #[inline]
    pub fn push(&mut self, item: T) -> bool {
        match self.entry(item) {
            Entry::Occupied(_) => true,
            Entry::Vacant(entry) => {
                entry.insert();
                false
            }
        }
    }
}

impl<T> VecSet<T, { Order::Unordered }> {
    /// Pushes `item` into the set.
    #[inline]
    pub fn push(&mut self, item: T) {
        self.inner.push(item)
    }

    /// Returns the set as a mutable slice.
    #[inline]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        &mut self.inner
    }
    /// Returns an iterator that allows modifying each value.
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<T> {
        self.as_sliceset_mut().iter_mut()
    }
}

impl<T: Ord> VecSet<T, { Order::Unordered }> {
    /// Inserts `item` into the set if not present, then returns a reference to the value in the set.
    #[inline(always)]
    pub fn get_or_insert(&mut self, item: T) -> &mut T {
        self.get_or_insert_priv(item)
    }
}

impl<T, const ORDER: Order> Deref for VecSet<T, { ORDER }> {
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &[T] {
        &self.inner
    }
}

impl<T> DerefMut for VecSet<T, { Order::Unordered }> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: Ord> FromIterator<T> for VecSet<T, { Order::Ordered }> {
    #[inline(always)]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut v = iter.into_iter().collect::<Vec<_>>();

        v.sort();

        VecSet::<T, { Order::Ordered }> { inner: v }
    }
}

impl<T> FromIterator<T> for VecSet<T, { Order::Unordered }> {
    #[inline(always)]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = VecSet::<T, { Order::Unordered }>::default();

        for elem in iter {
            set.push(elem);
        }

        set
    }
}

impl <'a, T, const ORDER: Order> IntoIterator for &'a VecSet<T, {ORDER}> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl <'a, T> IntoIterator for &'a mut VecSet<T, {Order::Unordered}> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, const ORDER: Order> IntoIterator for VecSet<T, { ORDER }> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;

    #[test]
    fn test_unsorted() {
        let mut set = VecSet::<_, { Order::Unordered }>::default();
        set.push(String::from("hello"));
        set.push(String::from("world"));

        assert!(set.contains("hello"));

        assert_eq!(set.pop(), Some(String::from("world")));
        assert_eq!(set.pop(), Some(String::from("hello")));
    }

    #[test]
    fn test_sorted() {
        let mut set = VecSet::<_, { Order::Ordered }>::default();
        set.push(10);
        set.push(5);
        set.push(22);

        assert!(set.contains(&22));

        assert_eq!(set.pop(), Some(22));
        assert_eq!(set.pop(), Some(10));
        assert_eq!(set.pop(), Some(5));

        let unordered = set.into_unordered();
        assert!(unordered.order() == Order::Unordered);

        let _: &[i32] = unordered.as_slice();
    }

    #[test]
    fn test_unsorted_set_entry_insert() {
        let mut set = VecSet::<_, { Order::Unordered }>::default();

        set.push(10);
        set.push(11);

        for n in 10..13 {
            match set.entry(n) {
                Entry::Occupied(mut entry) => {
                    *entry.get_mut() += 10;
                }
                Entry::Vacant(entry) => {
                    *entry.insert() += 2;
                }
            }
        }

        let slice = set.as_slice();

        assert_eq!(slice, &[20, 21, 14]);
    }

    #[test]
    fn struct_def_test() {
        let mut set = (0..10).rev().collect::<VecSet<_, { Order::Ordered }>>();

        assert!(set.contains(&9));

        match set.entry(15) {
            Entry::Occupied(entry) => {
                entry.remove();
            }

            Entry::Vacant(entry) => {
                entry.insert();
            }
        }

        assert!(set.remove(&15));
        assert!(!set.contains(&15));

        assert_eq!(set.as_slice(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

    #[test]
    fn get_or_insert() {
        let mut set = (0..10).rev().collect::<VecSet<_, { Order::Ordered }>>();

        let r = set.entry(11).insert();

        assert!(*r == 11);
    }
}
