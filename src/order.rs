#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
#[repr(u8)]
pub enum Order {
    /// The set is always Sorted.
    Sorted = 0,

    /// No order constraint.
    Unsorted = 1,
}

impl Order {
    #[inline(always)]
    pub const fn is_sorted(self) -> bool {
        self as u8 == Order::Sorted as u8
    }

    #[inline(always)]
    pub const fn is_unsorted(self) -> bool {
        !self.is_sorted()
    }
}
