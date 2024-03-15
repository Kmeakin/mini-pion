use core::fmt;
use std::ops::{Add, Deref, DerefMut};

use ecow::EcoVec;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct AbsoluteVar(usize);

impl From<usize> for AbsoluteVar {
    fn from(value: usize) -> Self { Self(value) }
}

impl From<AbsoluteVar> for usize {
    fn from(var: AbsoluteVar) -> Self { var.0 }
}

impl fmt::Display for AbsoluteVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl AbsoluteVar {
    pub fn iter() -> impl Iterator<Item = Self> { (0..).map(Self) }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct RelativeVar(usize);
impl RelativeVar {
    pub const fn new(value: usize) -> Self { Self(value) }
    pub const fn succ(self) -> Self { Self(self.0 + 1) }
    pub fn pred(self) -> Option<Self> { Some(Self(self.0.checked_sub(1)?)) }

    pub fn iter() -> impl Iterator<Item = Self> { (0..).map(Self) }
    pub fn iter_from(start: Self) -> impl Iterator<Item = Self> { (start.0..).map(Self) }
}

impl From<usize> for RelativeVar {
    fn from(value: usize) -> Self { Self(value) }
}

impl From<RelativeVar> for usize {
    fn from(var: RelativeVar) -> Self { var.0 }
}

impl fmt::Display for RelativeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

/// A specialized representation of an environment for when we don't care about
/// the elements themselves, just the number of elements in the environment.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct EnvLen(usize);

impl From<usize> for EnvLen {
    fn from(value: usize) -> Self { Self(value) }
}

impl From<EnvLen> for usize {
    fn from(var: EnvLen) -> Self { var.0 }
}

impl fmt::Display for EnvLen {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { self.0.fmt(f) }
}

impl EnvLen {
    /// New `EnvLen` representing an empty environment.
    pub const fn new() -> Self { Self(0) }

    /// Convert a `RelativeVar` to an `AbsoluteVar` in the current environment.
    pub fn relative_to_absolute(self, relative: RelativeVar) -> Option<AbsoluteVar> {
        Some(AbsoluteVar(self.0.checked_sub(relative.0)?.checked_sub(1)?))
    }

    /// Convert an `AbsoluteVar` to a `RelativeVar` in the current environment.
    pub fn absolute_to_relative(self, absolute: AbsoluteVar) -> Option<RelativeVar> {
        Some(RelativeVar(self.0.checked_sub(absolute.0)?.checked_sub(1)?))
    }

    /// Get an `AbsoluteVar` representing the most recent entry in the
    /// environment.
    pub const fn to_absolute(self) -> AbsoluteVar { AbsoluteVar(self.0) }

    /// Get a new environment with one extra element.
    pub const fn succ(self) -> Self { Self(self.0 + 1) }

    /// Get a new environment with one less element.
    pub fn pred(self) -> Option<Self> { Some(Self(self.0.checked_sub(1)?)) }

    /// Push a new element onto the environment.
    pub fn push(&mut self) { self.0 += 1; }

    /// Pop an new element off the environment.
    pub fn pop(&mut self) { self.0 -= 1; }

    /// Push many elements onto an environment.
    pub fn append(&mut self, other: Self) { self.0 += other.0; }

    /// Truncate the environment to `new_len`.
    pub fn truncate(&mut self, new_len: Self) { self.0 = new_len.0; }

    /// Reset the environment to the empty environment.
    pub fn clear(&mut self) { self.0 = 0; }
}

impl Add for EnvLen {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { Self(self.0 + rhs.0) }
}

/// An environment that is cheap to mutate, but expensive (*O(n)*) to clone.
#[derive(Debug, Clone)]
pub struct UniqueEnv<T> {
    elems: Vec<T>,
}

impl<T> UniqueEnv<T> {
    pub const fn new() -> Self { Self { elems: Vec::new() } }

    pub fn push(&mut self, elem: T) { self.elems.push(elem); }
    pub fn pop(&mut self) { self.elems.pop(); }

    pub fn truncate(&mut self, len: EnvLen) { self.elems.truncate(len.0); }
    pub fn clear(&mut self) { self.elems.clear(); }

    pub fn resize(&mut self, len: EnvLen, value: T)
    where
        T: Clone,
    {
        self.elems.resize(len.0, value);
    }
}

impl<T> Default for UniqueEnv<T> {
    fn default() -> Self { Self::new() }
}

impl<T> Deref for UniqueEnv<T> {
    type Target = SliceEnv<T>;
    fn deref(&self) -> &Self::Target { self.elems[..].into() }
}

impl<T> DerefMut for UniqueEnv<T> {
    fn deref_mut(&mut self) -> &mut Self::Target { (&mut self.elems[..]).into() }
}

#[derive(Debug, Clone)]
pub struct SharedEnv<T> {
    elems: EcoVec<T>,
}

impl<T: Clone> SharedEnv<T> {
    pub const fn new() -> Self {
        Self {
            elems: EcoVec::new(),
        }
    }

    pub fn push(&mut self, elem: T) { self.elems.push(elem); }
    pub fn pop(&mut self) { self.elems.pop(); }

    pub fn truncate(&mut self, len: EnvLen) { self.elems.truncate(len.0); }
    pub fn clear(&mut self) { self.elems.clear(); }
}

impl<T: Clone> Default for SharedEnv<T> {
    fn default() -> Self { Self::new() }
}

impl<T> Deref for SharedEnv<T> {
    type Target = SliceEnv<T>;
    fn deref(&self) -> &Self::Target { self.elems[..].into() }
}

#[derive(Debug, PartialEq, Eq)]
pub struct SliceEnv<T> {
    elems: [T],
}

impl<T> SliceEnv<T> {
    pub const fn len(&self) -> EnvLen { EnvLen(self.elems.len()) }

    pub const fn is_empty(&self) -> bool { self.elems.is_empty() }

    pub fn iter(&self) -> std::slice::Iter<T> { self.elems.iter() }

    pub fn iter_mut(&mut self) -> std::slice::IterMut<T> { self.elems.iter_mut() }

    pub fn get_absolute(&self, var: AbsoluteVar) -> Option<&T> { self.elems.get(var.0) }

    pub fn get_relative(&self, var: RelativeVar) -> Option<&T> {
        self.get_absolute(self.len().relative_to_absolute(var)?)
    }

    pub fn set_absolute(&mut self, var: AbsoluteVar, value: T) { self.elems[var.0] = value; }

    pub fn set_relative(&mut self, var: RelativeVar, value: T) {
        let absolute = self
            .len()
            .relative_to_absolute(var)
            .expect("index out of range");
        self.set_absolute(absolute, value);
    }
}

impl<'a, T> IntoIterator for &'a SliceEnv<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.elems.iter() }
}

impl<'a, T> IntoIterator for &'a mut SliceEnv<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter { self.elems.iter_mut() }
}

impl<'a, T> From<&'a [T]> for &'a SliceEnv<T> {
    fn from(slice: &'a [T]) -> &'a SliceEnv<T> {
        // SAFETY:
        // - `SliceEnv<T>` is equivalent to an `[T]` internally
        unsafe { &*(std::ptr::from_ref::<[T]>(slice) as *const SliceEnv<T>) }
    }
}

impl<'a, T> From<&'a mut [T]> for &'a mut SliceEnv<T> {
    fn from(slice: &'a mut [T]) -> &'a mut SliceEnv<T> {
        // SAFETY:
        // - `SliceEnv<T>` is equivalent to an `[T]` internally
        unsafe { &mut *(std::ptr::from_mut::<[T]>(slice) as *mut SliceEnv<T>) }
    }
}
