use std::ops::ControlFlow;

use internal_iterator::InternalIterator;
use pion_core::{Lit, Pat};
use pion_symbol::Symbol;
use smallvec::{smallvec, SmallVec};

use super::matrix::PatMatrix;

/// The head constructor of a pattern
#[derive(Debug, Copy, Clone)]
pub enum Constructor<'core> {
    Lit(Lit),
    Record(&'core [(Symbol, Pat<'core>)]),
}

impl<'core> PartialEq for Constructor<'core> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Lit(left_lit), Self::Lit(right_lit)) => left_lit == right_lit,
            (Self::Record(left_fields), Self::Record(right_fields)) => {
                pion_util::slice_eq_by_key(left_fields, right_fields, |(name, _)| *name)
            }
            _ => false,
        }
    }
}

impl<'core> Eq for Constructor<'core> {}

impl<'core> Constructor<'core> {
    /// Return number of fields `self` carries
    pub const fn arity(&self) -> usize {
        match self {
            Constructor::Lit(_) => 0,
            Constructor::Record(labels) => labels.len(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Constructors<'core> {
    Record(&'core [(Symbol, Pat<'core>)]),
    Bools(Bools),
    Ints(SmallVec<[u32; 4]>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Bools {
    False = 0,
    True = 1,
    Both = 2,
}

impl Bools {
    pub const fn contains(self, b: bool) -> bool {
        match self {
            Self::False => !b,
            Self::True => b,
            Self::Both => true,
        }
    }
}

impl From<bool> for Bools {
    fn from(value: bool) -> Self {
        match value {
            true => Self::True,
            false => Self::False,
        }
    }
}

impl<'core> Constructors<'core> {
    pub fn is_exhaustive(&self) -> bool {
        match self {
            Constructors::Record(_) => true,
            Constructors::Bools(bools) => *bools == Bools::Both,
            Constructors::Ints(ints) => (ints.len() as u64) >= (u32::MAX as u64),
        }
    }
}

pub struct PatConstructors<'core> {
    pat: Pat<'core>,
}

impl<'core> PatConstructors<'core> {
    pub const fn new(pat: Pat<'core>) -> Self { Self { pat } }
}

impl<'core> InternalIterator for PatConstructors<'core> {
    type Item = Constructor<'core>;

    fn try_for_each<R, F>(self, mut f: F) -> ControlFlow<R>
    where
        F: FnMut(Self::Item) -> ControlFlow<R>,
    {
        fn recur<'core, R>(
            pat: Pat<'core>,
            on_ctor: &mut impl FnMut(Constructor<'core>) -> ControlFlow<R>,
        ) -> ControlFlow<R> {
            match pat {
                Pat::Error | Pat::Underscore | Pat::Ident(..) => ControlFlow::Continue(()),
                Pat::Lit(.., lit) => on_ctor(Constructor::Lit(lit)),
                Pat::RecordLit(.., fields) => on_ctor(Constructor::Record(fields)),
            }
        }

        recur(self.pat, &mut f)
    }
}

pub fn has_constructors(pat: &Pat) -> bool { PatConstructors::new(*pat).next().is_some() }

impl<'core> PatMatrix<'core> {
    /// Collect all the `Constructor`s in the `index`th column
    #[allow(clippy::items_after_statements)]
    pub fn column_constructors(&self, index: usize) -> Option<Constructors<'core>> {
        let mut column = self.column(index).map(|(pat, _)| *pat);
        return empty(&mut column);

        fn empty<'core>(
            column: &mut dyn Iterator<Item = Pat<'core>>,
        ) -> Option<Constructors<'core>> {
            match column.next() {
                None => None,
                Some(pat) => match pat {
                    Pat::Error | Pat::Underscore | Pat::Ident(..) => empty(column),
                    Pat::RecordLit(.., fields) => Some(Constructors::Record(fields)),
                    Pat::Lit(.., Lit::Bool(value)) => Some(bools(column, value)),
                    Pat::Lit(.., Lit::Int(value)) => Some(ints(column, smallvec![value])),
                },
            }
        }

        fn bools<'core>(
            column: &mut dyn Iterator<Item = Pat<'core>>,
            value: bool,
        ) -> Constructors<'core> {
            match column.next() {
                None => Constructors::Bools(Bools::from(value)),
                Some(pat) => match pat {
                    Pat::Error | Pat::Underscore | Pat::Ident(..) => bools(column, value),
                    Pat::Lit(.., Lit::Bool(other_value)) if other_value == value => {
                        bools(column, value)
                    }
                    Pat::Lit(.., Lit::Bool(_)) => Constructors::Bools(Bools::Both),
                    Pat::Lit(..) | Pat::RecordLit(..) => unreachable!(),
                },
            }
        }

        fn ints<'core>(
            column: &mut dyn Iterator<Item = Pat<'core>>,
            mut values: SmallVec<[u32; 4]>,
        ) -> Constructors<'core> {
            match column.next() {
                None => Constructors::Ints(values),
                Some(pat) => match pat {
                    Pat::Error | Pat::Underscore | Pat::Ident(..) => ints(column, values),
                    Pat::Lit(.., Lit::Int(value)) => {
                        if let Err(index) = values.binary_search(&value) {
                            values.insert(index, value);
                        }
                        ints(column, values)
                    }
                    Pat::Lit(..) | Pat::RecordLit(..) => unreachable!(),
                },
            }
        }
    }
}
