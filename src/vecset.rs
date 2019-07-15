use super::order::Order;
//use super::search::{Search, SearchResult};

use core::{
    borrow::Borrow,
    iter::FromIterator,
    ops::{Deref, DerefMut, RangeBounds},
    slice::{Iter, IterMut},
};

use alloc::vec::{Drain, IntoIter, Vec};

use crate::sliceset::{SliceSet, Search, SearchResult};

/// A vecset is a set of items.
/// It is paremeterized with an [`Order`], to denote whether
/// the set is always Sorted, or Unsorted.
/// A Sorted set is guaranteed to always be sorted,
/// and contains no duplicates,
/// while in an Unsorted set, the order is unspecified,
/// and may contain duplicates.
///
/// To convert a Sorted set into an Unsorted set, or vice versa,
/// use the [`VecSet::into_sorted`] and [`VecSet::into_unsorted`] methods.
///
/// Items in a Sorted set can not be mutated, as that mutations change their order.
/// To mutate the items, use the [`VecSet::mutate_in_place`] method.
/// # Examples
/// ```
/// #![feature(const_generics)]
/// use vecset::vecset::{Order, VecSet, Entry};
///
/// let mut set = (0..10).rev().collect::<VecSet<_, {Order::Sorted}>>();
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
    inner: Vec<T>,
}

impl<T, const ORDER: Order> Default for VecSet<T, { ORDER }> {
    #[inline(always)]
    fn default() -> Self {
        VecSet::<T, { ORDER }> { inner: Vec::new() }
    }
}

/// Private implementations that *could* break
/// the invariant that a Sorted set is always sorted,
/// due to returning mutable references to the inners.
///
/// # Private
/// All methods in here are marked private because it is not known whether
/// `ORDER` is `Sorted`, in which case it is disallowed
/// to mutate any value within the set.
///
/// The public API uses these methods internally, but only exposes
/// what they see fit.
#[doc(hidden)]
impl<T, const ORDER: Order> VecSet<T, { ORDER }> {
    /// Searches for `item` in the set.
    /// Returns `Ok` with the corresponding index if the item is found,
    /// `Err` with the index `item` should be placed at otherwise.
    #[inline(always)]
    pub(crate) fn search<Q: ?Sized>(&self, item: &Q) -> SearchResult
    where
        T: Borrow<Q>,
        Q: Ord,
        SliceSet<T, {ORDER}>: Search<Q>,
    {
        // // LLVM *should* constify this.
        // match ORDER {
        //     Order::Sorted => self.bin_search(item),
        //     Order::Unsorted => self.iter_search(item),
        // }
        let slice: &[T] = self;
                //let sset = SliceSet::<T>::from_slice(slice).search(item);
                //let sset = SliceSet::<_, {Order::Unsorted}>::from_slice(slice);
        //SliceSet::<T>::from_slice::<{ORDER}>(slice).search(item)
        //sliceset_from_slice::<T, {Order::Sorted}>(slice).search(item)
        SliceSet::<T, {ORDER}>::from_slice(slice).search(item)
    }

    /// Inserts `item` into the set if not present, then returns a reference to the value in the set.
    pub(crate) fn get_or_insert_priv(&mut self, item: T) -> &mut T
    where
        T: Ord,
        SliceSet<T, {ORDER}>: Search<T>,
    {
        self.entry(item).insert_priv()
    }

    /// Inserts the computed value from `f` given `item` is not present, then returns a reference to the value in the set.
    pub(crate) fn get_or_insert_with_priv<Q: ?Sized, F>(&mut self, item: &Q, f: F) -> &mut T
    where
        T: Borrow<Q>,
        Q: Ord,
        F: FnOnce(&Q) -> T,
        SliceSet<T, {ORDER}>: Search<Q>,
    {
        self.entry_with(item, f).insert_priv()
    }
}

impl<T, const ORDER: Order> VecSet<T, { ORDER }> {
    /// Returns the [`Order`] of the set.
    #[inline(always)]
    pub const fn order(&self) -> Order {
        ORDER
    }

    /// Pops the last item from the set
    #[inline(always)]
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    /// Returns an iterator over the set.
    #[inline(always)]
    pub fn iter(&self) -> Iter<T> {
        self.inner.iter()
    }

    /// Returns a slice over the set
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        &self.inner
    }

    /// Converts the set into an Unsorted Set.
    #[inline]
    pub fn into_unsorted(self) -> VecSet<T, { Order::Unsorted }> {
        VecSet::<T, { Order::Unsorted }> { inner: self.inner }
    }

    /// Converts the set into a Sorted set.
    #[inline]
    pub fn into_sorted(self) -> VecSet<T, { Order::Sorted }>
    where
        T: Ord,
    {
        // We need T: Ord here,
        // if the Order is Sorted already,
        // this bound is required anyway by most methods,
        // and if the order is Unsorted, we need to sort the inner vector,
        // which requires T: Ord.
        let mut inner = self.inner;

        if ORDER.is_sorted() {
            VecSet::<T, { Order::Sorted }> { inner }
        } else {
            inner.sort();
            inner.dedup();
            VecSet::<T, { Order::Sorted }> { inner }
        }
    }

    #[inline]
    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }

    /// Returns true if the set contains `item`, false otherwise.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    /// use vecset::vecset::{Order, VecSet};
    ///
    /// let mut set = VecSet::<_, { Order::Sorted}>::default();
    /// set.push(String::from("hello"));
    /// set.push(String::from("world"));
    /// assert!(set.contains("hello"));
    /// ```
    #[inline]
    pub fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
        SliceSet<T, {ORDER}>: Search<Q>
    {
        self.search(item).is_ok()
    }

    /// Gets the given items entry in the map for in-place manipulations.
    /// # Examples
    /// ```
    /// #![feature(const_generics)]
    ///
    /// use vecset::vecset::{Order, VecSet, Entry};
    /// let mut set = VecSet::<_, {Order::Unsorted}>::default();
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
        SliceSet<T, {ORDER}>: Search<T>,
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

    /// Creates an entry derived from `f` if `item` is not present in the set.
    pub fn entry_with<Q: ?Sized, F>(&mut self, item: &Q, f: F) -> Entry<T, { ORDER }>
    where
        T: Borrow<Q>,
        Q: Ord,
        F: FnOnce(&Q) -> T,
        SliceSet<T, {ORDER}>: Search<Q>,
    {
        match self.search(item) {
            Ok(idx) => Entry::Occupied(OccupiedEntry::<T, { ORDER }> {
                set: self,
                index: idx,
            }),

            Err(idx) => Entry::Vacant(VacantEntry::<T, { ORDER }> {
                entry: f(item),
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
        SliceSet<T, {ORDER}>: Search<Q>,
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

impl<T: Ord> VecSet<T, { Order::Sorted }> {
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

impl<T> VecSet<T, { Order::Sorted }> {
    /// Inserts the computed value from `f` given `item` is not present, then returns a reference to the value in the set.
    #[inline(always)]
    pub fn get_or_insert_with<Q: ?Sized, F>(&mut self, item: &Q, f: F) -> &T
    where
        T: Borrow<Q>,
        Q: Ord,
        F: FnOnce(&Q) -> T,
    {
        self.get_or_insert_with_priv(item, f)
    }
}

impl<T> VecSet<T, { Order::Unsorted }> {
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
        self.inner.iter_mut()
    }
}

impl<T: Ord> VecSet<T, { Order::Unsorted }> {
    /// Inserts `item` into the set if not present, then returns a reference to the value in the set.
    #[inline(always)]
    pub fn get_or_insert(&mut self, item: T) -> &mut T {
        self.get_or_insert_priv(item)
    }
}

impl<T> VecSet<T, { Order::Unsorted }> {
    /// Inserts the computed value from `f` given `item` is not present, then returns a reference to the value in the set.
    #[inline]
    pub fn get_or_insert_with<Q: ?Sized, F>(&mut self, item: &Q, f: F) -> &mut T
    where
        T: Borrow<Q>,
        Q: Ord,
        F: FnOnce(&Q) -> T,
    {
        self.get_or_insert_with_priv(item, f)
    }
}

impl<T, const ORDER: Order> Deref for VecSet<T, { ORDER }> {
    type Target = [T];

    #[inline(always)]
    fn deref(&self) -> &[T] {
        &self.inner
    }
}

impl<T> DerefMut for VecSet<T, { Order::Unsorted }> {
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

impl<T: Ord> FromIterator<T> for VecSet<T, { Order::Sorted }> {
    #[inline(always)]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut v = iter.into_iter().collect::<Vec<_>>();

        v.sort();

        VecSet::<T, { Order::Sorted }> { inner: v }
    }
}

impl<T> FromIterator<T> for VecSet<T, { Order::Unsorted }> {
    #[inline(always)]
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut set = VecSet::<T, { Order::Unsorted }>::default();

        for elem in iter {
            set.push(elem);
        }

        set
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

/// A view into a vacant entry in a `VecSet`. It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, T, const ORDER: Order> {
    entry: T,
    index: usize,
    set: &'a mut VecSet<T, { ORDER }>,
}

#[doc(hidden)]
impl<'a, T, const ORDER: Order> VacantEntry<'a, T, { ORDER }> {
    /// Inserts the entry into the set.
    ///
    /// # Private
    /// Marked private because it is not known whether
    /// `ORDER` is `Sorted`, in which case it is disallowed
    /// to mutate the entry.
    #[inline(always)]
    pub(crate) fn insert_priv(self) -> &'a mut T {
        let index = self.index;
        let entry = self.entry;
        self.set.inner.insert(index, entry);
        &mut self.set.inner[index]
    }
}

impl<'a, T, const ORDER: Order> VacantEntry<'a, T, { ORDER }> {
    /// Returns a reference to the `VacantEntry`'s value.
    #[inline(always)]
    pub fn get(&self) -> &T {
        &self.entry
    }
}

impl<'a, T> VacantEntry<'a, T, { Order::Sorted }> {
    /// Set's the value of the entry with the `VacantEntry`'s value,
    /// returning a reference to it.
    #[inline]
    pub fn insert(self) -> &'a T {
        self.insert_priv()
    }
}

impl<'a, T> VacantEntry<'a, T, { Order::Unsorted }> {
    /// set's the value of the entry with the `VacantEntry`'s value,
    /// returning a mutable reference to it.
    #[inline]
    pub fn insert(self) -> &'a mut T {
        self.insert_priv()
    }

    /// Returns a mutable reference to the `VacantEntry`'s value.
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.entry
    }
}

/// A view into an occupied entry in a `VecSet`. It is part of the [`Entry`] enum.
pub struct OccupiedEntry<'a, T, const ORDER: Order> {
    set: &'a mut VecSet<T, { ORDER }>,
    index: usize,
}

#[doc(hidden)]
impl<'a, T, const ORDER: Order> OccupiedEntry<'a, T, { ORDER }> {
    /// Gets a mutable reference to the entry's occupied entry.
    ///
    /// # Private
    /// Marked private because it is not known whether
    /// `ORDER` is `Sorted`, in which case it is disallowed
    /// to mutate the entry.
    pub(crate) fn get_mut_priv(self) -> &'a mut T {
        &mut self.set.inner[self.index]
    }
}

impl<'a, T, const ORDER: Order> OccupiedEntry<'a, T, { ORDER }> {
    /// Take ownership of the value from the set
    #[inline(always)]
    pub fn remove(self) -> T {
        self.set.inner.remove(self.index)
    }

    /// Returns a reference to the `OccupiedEntry`'s value.
    #[inline(always)]
    pub fn get(&self) -> &T {
        &self.set.as_slice()[self.index]
    }
}

impl<'a, T> OccupiedEntry<'a, T, { Order::Unsorted }> {
    /// Returns a mutable reference to the `OccupiedEntry`'s value.
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.set.as_slice_mut()[self.index]
    }
}

/// A view into a single entry in a set, which may either be vacant or occupied.
/// this enum is constructed from the [`VecSet::entry`] method on a [`VecSet`].
pub enum Entry<'a, T, const ORDER: Order> {
    Vacant(VacantEntry<'a, T, { ORDER }>),
    Occupied(OccupiedEntry<'a, T, { ORDER }>),
}

impl<'a, T, const ORDER: Order> Entry<'a, T, { ORDER }> {
    pub(crate) fn insert_priv(self) -> &'a mut T {
        match self {
            Entry::Vacant(v) => v.insert_priv(),
            Entry::Occupied(o) => o.get_mut_priv(),
        }
    }
}

impl<'a, T> Entry<'a, T, { Order::Sorted }> {
    #[inline(always)]
    pub fn insert(self) -> &'a T {
        self.insert_priv()
    }
}

impl<'a, T> Entry<'a, T, { Order::Unsorted }> {
    #[inline(always)]
    pub fn insert(self) -> &'a mut T {
        self.insert_priv()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::String;

    #[test]
    fn test_unsorted() {
        let mut set = VecSet::<_, { Order::Unsorted }>::default();
        set.push(String::from("hello"));
        set.push(String::from("world"));

        assert!(set.contains("hello"));

        assert_eq!(set.pop(), Some(String::from("world")));
        assert_eq!(set.pop(), Some(String::from("hello")));
    }

    #[test]
    fn test_sorted() {
        let mut set = VecSet::<_, { Order::Sorted }>::default();
        set.push(10);
        set.push(5);
        set.push(22);

        assert!(set.contains(&22));

        assert_eq!(set.pop(), Some(22));
        assert_eq!(set.pop(), Some(10));
        assert_eq!(set.pop(), Some(5));

        let unordered = set.into_unsorted();
        assert!(unordered.order() == Order::Unsorted);

        let _: &[i32] = unordered.as_slice();
    }

    #[test]
    fn test_unsorted_set_entry_insert() {
        let mut set = VecSet::<_, { Order::Unsorted }>::default();

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
        let mut set = (0..10).rev().collect::<VecSet<_, { Order::Sorted }>>();

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
        let mut set = (0..10).rev().collect::<VecSet<_, { Order::Sorted }>>();

        let r = set.get_or_insert(11);

        //assert!(set.contains(&10));

        assert!(*r == 11);
    }
}
