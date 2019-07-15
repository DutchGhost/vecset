#[derive(Eq, PartialEq, Ord, PartialOrd, Copy, Clone, Hash)]
#[repr(u8)]
pub enum Order {
    /// The set is always Ordered.
    Ordered = 0,

    /// No order constraint.
    Unordered = 1,
}

impl Order {
    #[inline(always)]
    pub const fn is_ordered(self) -> bool {
        self as u8 == Order::Ordered as u8
    }

    #[inline(always)]
    pub const fn is_unordered(self) -> bool {
        !self.is_ordered()
    }
}
