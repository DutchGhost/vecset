use core::borrow::Borrow;

pub(crate) type SearchResult = Result<usize, usize>;

/// Private trait providing 2 functions to search for `Q`
pub(crate) trait Search<Q: ?Sized> {
    /// Searches `Q` in the structure using binary search.
    fn bin_search(&self, item: &Q) -> SearchResult;

    /// Searches `Q` in the structure using linear search.
    fn iter_search(&self, item: &Q) -> SearchResult;
}

impl<Q: ?Sized, T> Search<Q> for [T]
where
    T: Borrow<Q>,
    Q: Ord,
{
    #[inline(always)]
    fn bin_search(&self, item: &Q) -> SearchResult {
        self.as_ref()
            .binary_search_by(|elem| elem.borrow().cmp(item))
    }

    #[inline(always)]
    fn iter_search(&self, item: &Q) -> SearchResult {
        self.as_ref()
            .iter()
            .enumerate()
            .find(|(_, elem)| (*elem).borrow() == item)
            .map(|(idx, _)| idx)
            .ok_or_else(|| self.len())
    }
}
