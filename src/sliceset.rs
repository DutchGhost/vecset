use crate::order::Order;

use core::{mem, borrow::Borrow};

pub type SearchResult = Result<usize, usize>;

pub(crate) struct SliceSet<T, const ORDER: Order> {
    slice: [T]
}

impl <T, const ORDER: Order> SliceSet<T, {ORDER}> {
    pub(crate) fn from_slice<'s>(slice: &'s [T]) -> &'s SliceSet<T, {ORDER}> {
        unsafe {
            mem::transmute(slice)
        }
    }

    pub(crate) fn from_slice_mut<'s>(slice: &'s mut [T]) -> &'s mut SliceSet<T, {ORDER}> {
        unsafe {
            mem::transmute(slice)
        }
    }
}

pub(crate) trait Search<Q: ?Sized> {
    fn search(&self, value: &Q) -> SearchResult;
}

impl <T, Q: ?Sized> Search<Q> for SliceSet<T, {Order::Sorted}>
where
    T: Borrow<Q>,
    Q: Ord,
{
    fn search(&self, value: &Q) -> SearchResult {
        self.slice.binary_search_by(|elem| elem.borrow().cmp(value))
    }
}

impl <T, Q: ?Sized> Search<Q> for SliceSet<T, {Order::Unsorted}>
where
    T: Borrow<Q>,
    Q: Ord,
{
    fn search(&self, value: &Q) -> SearchResult {
        self.slice
            .iter()
            .enumerate().find(|(_, elem)| (*elem).borrow() == value)
            .map(|(idx, _)| idx)
            .ok_or_else(|| self.slice.len())
    }
}

impl <'a, Q: ?Sized, S> Search<Q> for &'a S
where
    S: Search<Q>
{
    fn search(&self, value: &Q) -> SearchResult {
        (**self).search(value)
    }
}