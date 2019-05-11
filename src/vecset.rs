use std::borrow::Borrow;

pub enum Order {
    /// The set is always Sorted.
    Sorted,

    /// No order constraint.
    Unsorted
}

pub struct VecSet<T, const ORDER: Order> {
    inner: Vec<T>,
}

impl <T> VecSet<T, {Order::Sorted}> {
    /// Creates a new Sorted VecSet.
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

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

    /// Pops the last item of the set.
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }

    /// Converts the set into an Unsorted Set.
    pub fn into_unsorted(self) -> VecSet<T, {Order::Unsorted}> {
        VecSet::<T, {Order::Unsorted}> {
            inner: self.inner
        }
    }
}

impl <T: Ord> VecSet<T, {Order::Sorted}> {
    /// Pushes `item` into the set.
    /// Returns `true` if the item was already in the set, `false` otherwise.
    pub fn push(&mut self, item: T) -> bool {
        match self.inner.binary_search(&item) {
            Ok(_) => {
                true
            }
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

impl <T> VecSet<T, {Order::Unsorted}> {
    /// Creates a new Unsorted VecSet.
    #[inline(always)]
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    /// Pushes `item` into the set.
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
    pub fn contains<Q: ?Sized>(&self, item: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.inner.iter().find(|elem| (*elem).borrow() == item).is_some()
    }

    /// Pops the last item of the set.
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsorted() {
        let mut set = VecSet::<_, {Order::Unsorted}>::new();
        set.push(String::from("hello"));
        set.push(String::from("world"));

        assert!(set.contains("hello"));

        assert_eq!(set.pop(), Some(String::from("world")));
        assert_eq!(set.pop(), Some(String::from("hello")));
    }

    #[test]
    fn test_sorted() {
        let mut set = VecSet::<_, {Order::Sorted}>::new();
        set.push(10);
        set.push(5);
        set.push(22);

        assert!(set.contains(&22));

        assert_eq!(set.pop(), Some(22));
        assert_eq!(set.pop(), Some(10));
        assert_eq!(set.pop(), Some(5));
    }
}
