#![feature(if_let_guard, iter_intersperse)]

pub mod core;
pub mod elab;
pub mod surface;

pub mod env;
pub mod symbol;

mod plicity;
mod slice_vec;

pub fn slice_eq_by_key<T, V: PartialEq>(
    xs: &[T],
    ys: &[T],
    key_fn: impl Copy + Fn(&T) -> V,
) -> bool {
    if xs.len() != ys.len() {
        return false;
    }

    Iterator::eq(xs.iter().map(key_fn), ys.iter().map(key_fn))
}
