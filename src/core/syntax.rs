use super::prim::Prim;
use crate::env::{AbsoluteVar, EnvLen, RelativeVar};
use crate::plicity::Plicity;
use crate::symbol::Symbol;

#[derive(Debug, Copy, Clone)]
pub enum Expr<'core> {
    Error,
    Const(Const),
    Prim(Prim),
    LocalVar(RelativeVar),
    MetaVar(AbsoluteVar),

    Let {
        name: Option<Symbol>,
        r#type: &'core Self,
        init: &'core Self,
        body: &'core Self,
    },
    If {
        cond: &'core Self,
        then: &'core Self,
        r#else: &'core Self,
    },

    FunType {
        param: FunParam<&'core Self>,
        body: &'core Self,
    },
    FunLit {
        param: FunParam<&'core Self>,
        body: &'core Self,
    },
    FunApp {
        fun: &'core Self,
        arg: FunArg<&'core Self>,
    },

    RecordType(&'core [(Symbol, Self)]),
    RecordLit(&'core [(Symbol, Self)]),
    RecordProj(&'core Self, Symbol),
}

impl<'core> Expr<'core> {
    pub const TYPE: Self = Self::Prim(Prim::Type);
    pub const BOOL: Self = Self::Prim(Prim::Bool);
    pub const INT: Self = Self::Prim(Prim::Int);

    pub fn references_local(&self, var: RelativeVar) -> bool {
        match self {
            Expr::LocalVar(v) => var == *v,
            Expr::Error | Expr::Const(..) | Expr::Prim(..) | Expr::MetaVar(..) => false,
            Expr::Let {
                r#type, init, body, ..
            } => {
                r#type.references_local(var)
                    || init.references_local(var)
                    || body.references_local(var.succ())
            }
            Expr::If { cond, then, r#else } => {
                cond.references_local(var)
                    || then.references_local(var)
                    || r#else.references_local(var)
            }
            Expr::FunType { param, body } | Expr::FunLit { param, body } => {
                param.r#type.references_local(var) || body.references_local(var.succ())
            }
            Expr::FunApp { fun, arg } => {
                fun.references_local(var) || arg.expr.references_local(var)
            }
            Expr::RecordType(fields) => RelativeVar::iter_from(var)
                .zip(fields.iter())
                .any(|(var, (_, r#type))| r#type.references_local(var)),
            Expr::RecordLit(fields) => fields.iter().any(|(_, expr)| expr.references_local(var)),
            Expr::RecordProj(scrut, _) => scrut.references_local(var),
        }
    }

    pub fn shift(&self, bump: &'core bumpalo::Bump, amount: EnvLen) -> Self {
        self.shift_inner(bump, RelativeVar::default(), amount)
    }

    fn shift_inner(
        &self,
        bump: &'core bumpalo::Bump,
        mut min: RelativeVar,
        amount: EnvLen,
    ) -> Self {
        // Skip traversing and rebuilding the term if it would make no change. Increases
        // sharing.
        if amount == EnvLen::new() {
            return *self;
        }

        match self {
            Expr::LocalVar(var) if *var >= min => Expr::LocalVar(*var + amount),

            Expr::Error
            | Expr::Const(..)
            | Expr::Prim(..)
            | Expr::LocalVar(..)
            | Expr::MetaVar(..) => *self,

            Expr::Let {
                name,
                r#type,
                init,
                body,
            } => {
                let r#type = r#type.shift_inner(bump, min, amount);
                let init = init.shift_inner(bump, min, amount);
                let body = body.shift_inner(bump, min.succ(), amount);
                let (r#type, init, body) = bump.alloc((r#type, init, body));
                Expr::Let {
                    name: *name,
                    r#type,
                    init,
                    body,
                }
            }

            Expr::FunLit { param, body } => {
                let r#type = param.r#type.shift_inner(bump, min, amount);
                let body = body.shift_inner(bump, min.succ(), amount);
                let (r#type, body) = bump.alloc((r#type, body));
                let param = FunParam::new(param.plicity, param.name, r#type as &_);
                Expr::FunLit { param, body }
            }
            Expr::FunType { param, body } => {
                let r#type = param.r#type.shift_inner(bump, min, amount);
                let body = body.shift_inner(bump, min.succ(), amount);
                let (r#type, body) = bump.alloc((r#type, body));
                let param = FunParam::new(param.plicity, param.name, r#type as &_);
                Expr::FunType { param, body }
            }
            Expr::FunApp { fun, arg } => {
                let fun = fun.shift_inner(bump, min, amount);
                let arg_expr = arg.expr.shift_inner(bump, min, amount);
                let (fun, arg_expr) = bump.alloc((fun, arg_expr));
                Expr::FunApp {
                    fun,
                    arg: FunArg::new(arg.plicity, arg_expr),
                }
            }

            Expr::RecordType(fields) => Expr::RecordType(bump.alloc_slice_fill_iter(
                fields.iter().map(|(name, r#type)| {
                    let r#type = r#type.shift_inner(bump, min, amount);
                    min = min.succ();
                    (*name, r#type)
                }),
            )),

            Expr::RecordLit(fields) => Expr::RecordLit(
                bump.alloc_slice_fill_iter(
                    fields
                        .iter()
                        .map(|(name, r#type)| (*name, r#type.shift_inner(bump, min, amount))),
                ),
            ),

            Expr::RecordProj(scrut, label) => {
                Expr::RecordProj(bump.alloc(scrut.shift_inner(bump, min, amount)), *label)
            }

            Expr::If { cond, then, r#else } => {
                let cond = cond.shift_inner(bump, min, amount);
                let then = then.shift_inner(bump, min, amount);
                let r#else = r#else.shift_inner(bump, min, amount);
                let (cond, then, r#else) = bump.alloc((cond, then, r#else));
                Expr::If { cond, then, r#else }
            }
        }
    }
}

impl<'core> Expr<'core> {
    pub fn lets(
        bump: &'core bumpalo::Bump,
        bindings: &[(Option<Symbol>, Self, Self)],
        body: Self,
    ) -> Self {
        bindings
            .iter()
            .copied()
            .rev()
            .fold(body, |body, (name, r#type, init)| {
                let (r#type, init, body) = bump.alloc((r#type, init, body));
                Expr::Let {
                    name,
                    r#type,
                    init,
                    body,
                }
            })
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<T> {
    pub plicity: Plicity,
    pub name: Option<Symbol>,
    pub r#type: T,
}

impl<T> FunParam<T> {
    pub const fn new(plicity: Plicity, name: Option<Symbol>, r#type: T) -> Self {
        Self {
            plicity,
            name,
            r#type,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct FunArg<T> {
    pub plicity: Plicity,
    pub expr: T,
}

impl<T> FunArg<T> {
    pub const fn new(plicity: Plicity, expr: T) -> Self { Self { plicity, expr } }
}

#[derive(Debug, Copy, Clone)]
pub enum Pat<'core> {
    Error,
    Underscore,
    Ident(Symbol),
    RecordLit(&'core [(Symbol, Self)]),
}

impl<'core> Pat<'core> {
    pub const fn name(&self) -> Option<Symbol> {
        match self {
            Pat::Ident(symbol) => Some(*symbol),
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    Bool(bool),
    Int(u32),
}
