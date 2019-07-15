use crate::order::Order;

use core::{
    borrow::Borrow,
    mem,
    slice::{Iter, IterMut},
};

pub (crate) type SearchResult = Result<usize, usize>;

pub(crate) struct SliceSet<T, const ORDER: Order> {
    slice: [T],
}

#[allow(clippy::transmute_ptr_to_ptr)]
impl<'s, T, const ORDER: Order> From<&'s [T]> for &'s SliceSet<T, { ORDER }> {
    fn from(slice: &'s [T]) -> &'s SliceSet<T, { ORDER }> {
        unsafe { mem::transmute(slice) }
    }
}

#[allow(clippy::transmute_ptr_to_ptr)]
impl<'s, T, const ORDER: Order> From<&'s mut [T]> for &'s mut SliceSet<T, { ORDER }> {
    fn from(slice: &'s mut [T]) -> &'s mut SliceSet<T, { ORDER }> {
        unsafe { mem::transmute(slice) }
    }
}

impl<T, const ORDER: Order> SliceSet<T, { ORDER }> {
    #[inline]
    pub(crate) fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.search(item).is_ok()
    }

    #[inline]
    pub(crate) fn search<Q: ?Sized>(&self, value: &Q) -> SearchResult
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        match ORDER {
            Order::Ordered => self.binary_search(value),
            Order::Unordered => self.iter_search(value),
        }
    }

    #[inline(always)]
    pub(crate) fn iter(&self) -> Iter<T> {
        self.slice.iter()
    }

    #[inline(always)]
    pub(crate) fn iter_mut(&mut self) -> IterMut<T> {
        self.slice.iter_mut()
    }

    fn binary_search<Q: ?Sized>(&self, value: &Q) -> SearchResult
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.slice.binary_search_by(|elem| elem.borrow().cmp(value))
    }

    fn iter_search<Q: ?Sized>(&self, value: &Q) -> SearchResult
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.slice
            .iter()
            .enumerate()
            .find(|(_, elem)| (*elem).borrow() == value)
            .map(|(idx, _)| idx)
            .ok_or_else(|| self.slice.len())
    }
}
