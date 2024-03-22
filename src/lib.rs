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

pub fn slice_eq_by_key2<T1, T2, V: PartialEq>(
    xs: &[T1],
    ys: &[T2],
    key_fn1: impl Copy + Fn(&T1) -> V,
    key_fn2: impl Copy + Fn(&T2) -> V,
) -> bool {
    if xs.len() != ys.len() {
        return false;
    }

    Iterator::eq(xs.iter().map(key_fn1), ys.iter().map(key_fn2))
}
