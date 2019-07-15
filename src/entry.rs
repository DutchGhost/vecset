use crate::{order::Order, vecset::VecSet};

/// A view into a vacant entry in a `VecSet`. It is part of the [`Entry`] enum.
pub struct VacantEntry<'a, T, const ORDER: Order> {
    pub(crate) entry: T,
    pub(crate) index: usize,
    pub(crate) set: &'a mut VecSet<T, { ORDER }>,
}

impl<'a, T, const ORDER: Order> VacantEntry<'a, T, { ORDER }> {
    /// Inserts the entry into the set.
    ///
    /// # Private
    /// Marked private because it is not known whether
    /// `ORDER` is `Ordered`, in which case it is disallowed
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

impl<'a, T> VacantEntry<'a, T, { Order::Ordered }> {
    /// Set's the value of the entry with the `VacantEntry`'s value,
    /// returning a reference to it.
    #[inline]
    pub fn insert(self) -> &'a T {
        self.insert_priv()
    }
}

impl<'a, T> VacantEntry<'a, T, { Order::Unordered }> {
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
    pub(crate) set: &'a mut VecSet<T, { ORDER }>,
    pub(crate) index: usize,
}

impl<'a, T, const ORDER: Order> OccupiedEntry<'a, T, { ORDER }> {
    /// Gets a mutable reference to the entry's occupied entry.
    ///
    /// # Private
    /// Marked private because it is not known whether
    /// `ORDER` is `Ordered`, in which case it is disallowed
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

impl<'a, T> OccupiedEntry<'a, T, { Order::Unordered }> {
    /// Returns a mutable reference to the `OccupiedEntry`'s value.
    #[inline(always)]
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.set.as_slice_mut()[self.index]
    }
}

/// A view into a single entry in a set, which may either be vacant or occupied.
/// this enum is constructed from the [`VecSet::entry`] method on a [`VecSet`].
pub enum Entry<'a, T, const ORDER: Order> {
    /// A Vacant entry into the set.
    /// Can be inserted into the set.
    Vacant(VacantEntry<'a, T, { ORDER }>),

    /// An occupied entry into the set.
    /// Can be removed from the set.
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

impl<'a, T> Entry<'a, T, { Order::Ordered }> {
    /// Inserts the entry into the set if not already present.
    /// Then returns a reference to the entry.
    #[inline(always)]
    pub fn insert(self) -> &'a T {
        self.insert_priv()
    }
}

impl<'a, T> Entry<'a, T, { Order::Unordered }> {
    /// Inserts the entry into the set if not already present.
    /// Then returns a mutable reference to the entry.
    #[inline(always)]
    pub fn insert(self) -> &'a mut T {
        self.insert_priv()
    }
}
