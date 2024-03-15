use super::prim::Prim;
use crate::env::{AbsoluteVar, RelativeVar};
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Const {
    Bool(bool),
    Int(u32),
}
