use ecow::EcoVec;
use either::Either::{self, Left, Right};

use super::prim::Prim;
use super::syntax::{Const, Expr, FunArg, FunParam};
use crate::env::{AbsoluteVar, EnvLen, SharedEnv, SliceEnv};
use crate::plicity::Plicity;
use crate::slice_vec::SliceVec;
use crate::symbol::Symbol;

pub type Type<'core> = Value<'core>;

#[derive(Debug, Clone)]
pub enum Value<'core> {
    Error,
    Const(Const),
    Neutral {
        head: Head,
        spine: EcoVec<Elim<'core>>,
    },
    FunLit {
        param: FunParam<&'core Self>,
        body: Closure<'core>,
    },
    FunType {
        param: FunParam<&'core Self>,
        body: Closure<'core>,
    },
    RecordType(Telescope<'core>),
    RecordLit(&'core [(Symbol, Self)]),
}

impl<'core> Value<'core> {
    pub const TYPE: Self = Self::prim(Prim::Type);
    pub const INT: Self = Self::prim(Prim::Int);
    pub const BOOL: Self = Self::prim(Prim::Bool);

    pub const fn prim(prim: Prim) -> Self {
        Self::Neutral {
            head: Head::Prim(prim),
            spine: EcoVec::new(),
        }
    }

    pub const fn local_var(var: AbsoluteVar) -> Self {
        Self::Neutral {
            head: Head::LocalVar(var),
            spine: EcoVec::new(),
        }
    }

    pub const fn meta_var(var: AbsoluteVar) -> Self {
        Self::Neutral {
            head: Head::MetaVar(var),
            spine: EcoVec::new(),
        }
    }

    pub const fn is_type(&self) -> bool {
        matches!(self, Self::Neutral { head:Head::Prim(Prim::Type), spine } if spine.is_empty())
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Head {
    Prim(Prim),
    LocalVar(AbsoluteVar),
    MetaVar(AbsoluteVar),
}

#[derive(Debug, Clone)]
pub enum Elim<'core> {
    FunApp(FunArg<Value<'core>>),
    RecordProj(Symbol),
    BoolCases(BoolCases<'core>),
}

#[derive(Debug, Clone)]
pub struct BoolCases<'core> {
    pub local_values: LocalValues<'core>,
    pub then: &'core Expr<'core>,
    pub r#else: &'core Expr<'core>,
}

impl<'core> BoolCases<'core> {
    pub const fn new(
        local_values: LocalValues<'core>,
        then: &'core Expr<'core>,
        r#else: &'core Expr<'core>,
    ) -> Self {
        Self {
            local_values,
            then,
            r#else,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Closure<'core> {
    pub local_values: LocalValues<'core>,
    pub body: &'core Expr<'core>,
}

impl<'core> Closure<'core> {
    pub const fn new(local_values: LocalValues<'core>, body: &'core Expr<'core>) -> Self {
        Self { local_values, body }
    }

    pub const fn empty(body: &'core Expr<'core>) -> Self { Self::new(LocalValues::new(), body) }
}

#[derive(Debug, Clone)]
pub struct Telescope<'core> {
    pub local_values: LocalValues<'core>,
    pub fields: &'core [(Symbol, Expr<'core>)],
}

impl<'core> Telescope<'core> {
    pub const fn new(
        local_values: LocalValues<'core>,
        fields: &'core [(Symbol, Expr<'core>)],
    ) -> Self {
        Self {
            local_values,
            fields,
        }
    }

    pub const fn len(&self) -> usize { self.fields.len() }

    pub const fn is_empty(&self) -> bool { self.len() == 0 }
}

pub type LocalValues<'core> = SharedEnv<Value<'core>>;
pub type MetaValues<'core> = SliceEnv<Option<Value<'core>>>;

#[derive(Debug, Copy, Clone)]
pub struct EvalOpts {
    pub unfold_fix: bool,
}

impl Default for EvalOpts {
    fn default() -> Self { Self { unfold_fix: true } }
}

pub fn eval<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    local_values: &mut LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    expr: &Expr<'core>,
) -> Value<'core> {
    match expr {
        Expr::Error => Value::Error,
        Expr::Const(r#const) => Value::Const(*r#const),
        Expr::Prim(prim) => Value::prim(*prim),
        Expr::LocalVar(var) => match local_values.get_relative(*var) {
            None => panic!("Unbound local var: {var:?}"),
            Some(value) => value.clone(),
        },
        Expr::MetaVar(var) => match meta_values.get_absolute(*var) {
            None => panic!("Unbound meta var: {var:?}"),
            Some(None) => Value::meta_var(*var),
            Some(Some(value)) => value.clone(),
        },

        Expr::Let { init, body, .. } => {
            let init = eval(bump, opts, local_values, meta_values, init);
            local_values.push(init);
            let body = eval(bump, opts, local_values, meta_values, body);
            local_values.pop();
            body
        }
        Expr::If { cond, then, r#else } => {
            let cond = eval(bump, opts, local_values, meta_values, cond);
            if_then_else(bump, opts, local_values, meta_values, cond, then, r#else)
        }

        Expr::FunType { param, body } => {
            let r#type = eval(bump, opts, local_values, meta_values, param.r#type);
            let body = Closure::new(local_values.clone(), body);
            Value::FunType {
                param: FunParam::new(param.plicity, param.name, bump.alloc(r#type)),
                body,
            }
        }
        Expr::FunLit { param, body } => {
            let r#type = eval(bump, opts, local_values, meta_values, param.r#type);
            let body = Closure::new(local_values.clone(), body);
            Value::FunLit {
                param: FunParam::new(param.plicity, param.name, bump.alloc(r#type)),
                body,
            }
        }
        Expr::FunApp { fun, arg } => {
            let fun = eval(bump, opts, local_values, meta_values, fun);
            let arg = FunArg::new(
                arg.plicity,
                eval(bump, opts, local_values, meta_values, arg.expr),
            );
            fun_app(bump, opts, meta_values, fun, arg)
        }
        Expr::RecordType(type_fields) => {
            Value::RecordType(Telescope::new(local_values.clone(), type_fields))
        }
        Expr::RecordLit(expr_fields) => {
            Value::RecordLit(bump.alloc_slice_fill_iter(expr_fields.iter().map(
                |(symbol, expr)| (*symbol, eval(bump, opts, local_values, meta_values, expr)),
            )))
        }
        Expr::RecordProj(scrut, name) => {
            let scrut = eval(bump, opts, local_values, meta_values, scrut);
            record_proj(scrut, *name)
        }
    }
}

pub fn fun_app<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    fun: Value<'core>,
    arg: FunArg<Value<'core>>,
) -> Value<'core> {
    match fun {
        Value::Error => Value::Error,
        Value::Neutral { head, mut spine } => {
            spine.push(Elim::FunApp(arg));
            if let Some(value) = prim_app(bump, opts, meta_values, head, spine.as_slice()) {
                return value;
            }
            Value::Neutral { head, spine }
        }
        Value::FunLit { param, body, .. } => {
            debug_assert_eq!(arg.plicity, param.plicity);
            apply_closure(bump, opts, meta_values, body, arg.expr)
        }
        _ => panic!("Invalid function application"),
    }
}

fn prim_app<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    head: Head,
    spine: &[Elim<'core>],
) -> Option<Value<'core>> {
    let Head::Prim(prim) = head else { return None };

    macro_rules! prim_rules {
        ($($prim:ident($($args:pat)*)$(if $guard:expr)? => $rhs:expr),*,) => {
            #[allow(non_snake_case)]
            match (prim, spine) {
                $((Prim::$prim, [$(Elim::FunApp(FunArg{ plicity: _, expr:$args } ),)*]) $(if $guard)? => Some($rhs),)*
                _ => None,
            }
        };
    }

    prim_rules! {
        add(Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Int(x.wrapping_add(*y))),
        sub(Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Int(x.wrapping_sub(*y))),
        mul(Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Int(x.wrapping_mul(*y))),

        eq (Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x == y)),
        ne (Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x != y)),
        lt (Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x < y)),
        gt (Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x > y)),
        lte(Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x <= y)),
        gte(Value::Const(Const::Int(x)) Value::Const(Const::Int(y))) => Value::Const(Const::Bool(x >= y)),

        // fix @A @B f x  = f (fix @A @B f) x
        fix(A B f x) if opts.unfold_fix => {
            let fix = Value::prim(Prim::fix);
            let fixA = fun_app(bump, opts, meta_values, fix, FunArg::new(Plicity::Implicit, A.clone()));
            let fixAB = fun_app(bump, opts, meta_values, fixA, FunArg::new(Plicity::Implicit, B.clone()));
            let fixABf = fun_app(bump, opts, meta_values, fixAB, FunArg::new(Plicity::Explicit, f.clone()));
            let ffixABf = fun_app(bump, opts, meta_values, f.clone(), FunArg::new(Plicity::Explicit, fixABf));
            let ffixABfx = fun_app(bump, opts, meta_values, ffixABf, FunArg::new(Plicity::Explicit, x.clone()));
            ffixABfx
        },
    }
}

pub fn apply_closure<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    closure: Closure<'core>,
    arg: Value<'core>,
) -> Value<'core> {
    let Closure {
        mut local_values,
        body,
    } = closure;
    local_values.push(arg);
    eval(bump, opts, &mut local_values, meta_values, body)
}

pub fn if_then_else<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    local_values: &LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    cond: Value<'core>,
    then: &'core Expr<'core>,
    r#else: &'core Expr<'core>,
) -> Value<'core> {
    let cases = BoolCases::new(local_values.clone(), then, r#else);
    apply_bool_elim(bump, opts, meta_values, cases, cond)
}

pub fn apply_bool_elim<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    mut cases: BoolCases<'core>,
    cond: Value<'core>,
) -> Value<'core> {
    match cond {
        Value::Error => Value::Error,
        Value::Neutral { head, mut spine } => {
            spine.push(Elim::BoolCases(cases));
            Value::Neutral { head, spine }
        }
        Value::Const(Const::Bool(true)) => {
            eval(bump, opts, &mut cases.local_values, meta_values, cases.then)
        }
        Value::Const(Const::Bool(false)) => eval(
            bump,
            opts,
            &mut cases.local_values,
            meta_values,
            cases.r#else,
        ),
        _ => panic!("Invalid if-then-else"),
    }
}

pub fn record_proj(scrut: Value, name: Symbol) -> Value {
    match scrut {
        Value::Error => Value::Error,
        Value::Neutral { head, mut spine } => {
            spine.push(Elim::RecordProj(name));
            Value::Neutral { head, spine }
        }
        Value::RecordLit(fields) => match (fields.iter()).find(|(n, _)| *n == name) {
            Some((_, value)) => value.clone(),
            None => panic!("Invalid record projection"),
        },
        _ => panic!("Invalid record projection"),
    }
}

pub fn split_telescope<'core, 'tele>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    telescope: &'tele mut Telescope<'core>,
) -> Option<(Symbol, Value<'core>, impl FnOnce(Value<'core>) + 'tele)> {
    let ((name, expr), fields) = telescope.fields.split_first()?;
    let value = eval(bump, opts, &mut telescope.local_values, meta_values, expr);
    Some((*name, value, move |prev| {
        telescope.local_values.push(prev);
        telescope.fields = fields;
    }))
}

pub fn quote<'core>(
    bump: &'core bumpalo::Bump,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
    value: &Value<'core>,
) -> Expr<'core> {
    let opts = EvalOpts { unfold_fix: false };
    let value = update_metas(bump, opts, meta_values, value);
    match value {
        Value::Error => Expr::Error,
        Value::Neutral { head, spine } => {
            let head = quote_head(bump, head, local_len, meta_values);
            spine.iter().fold(head, |head, elim| match elim {
                Elim::FunApp(arg) => {
                    let arg_expr = quote(bump, local_len, meta_values, &arg.expr);
                    let (fun, arg_expr) = bump.alloc((head, arg_expr));
                    let (fun, arg_expr) = (fun as &_, arg_expr as &_);
                    let arg = FunArg::new(arg.plicity, arg_expr);
                    Expr::FunApp { fun, arg }
                }
                Elim::BoolCases(elim) => {
                    let mut elim = elim.clone();
                    let then = eval(bump, opts, &mut elim.local_values, meta_values, elim.then);
                    let r#else = eval(bump, opts, &mut elim.local_values, meta_values, elim.r#else);

                    let then = quote(bump, local_len, meta_values, &then);
                    let r#else = quote(bump, local_len, meta_values, &r#else);

                    let (cond, then, r#else) = bump.alloc((head, then, r#else));
                    Expr::If { cond, then, r#else }
                }
                Elim::RecordProj(name) => Expr::RecordProj(bump.alloc(head), *name),
            })
        }
        Value::FunLit { param, body } => {
            let (param, body) = quote_fun(bump, opts, local_len, meta_values, param, body);
            Expr::FunLit { param, body }
        }
        Value::FunType { param, body } => {
            let (param, body) = quote_fun(bump, opts, local_len, meta_values, param, body);
            Expr::FunType { param, body }
        }
        Value::Const(r#const) => Expr::Const(r#const),
        Value::RecordType(mut telescope) => {
            let mut local_len = local_len;
            let mut expr_fields = SliceVec::new(bump, telescope.fields.len());
            while let Some((name, value, update_telescope)) =
                split_telescope(bump, opts, meta_values, &mut telescope)
            {
                let var = Value::local_var(local_len.to_absolute());
                update_telescope(var);
                let expr = quote(bump, local_len, meta_values, &value);
                expr_fields.push((name, expr));
                local_len.push();
            }
            Expr::RecordType(expr_fields.into())
        }
        Value::RecordLit(expr_fields) => Expr::RecordLit(
            bump.alloc_slice_fill_iter(
                expr_fields
                    .iter()
                    .map(|(name, value)| (*name, quote(bump, local_len, meta_values, value))),
            ),
        ),
    }
}

fn quote_head<'core>(
    bump: &'core bumpalo::Bump,
    head: Head,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
) -> Expr<'core> {
    match head {
        Head::Prim(prim) => Expr::Prim(prim),
        Head::LocalVar(var) => match local_len.absolute_to_relative(var) {
            None => panic!("Unbound local variable: {var:?}"),
            Some(var) => Expr::LocalVar(var),
        },
        Head::MetaVar(var) => match meta_values.get_absolute(var) {
            Some(Some(value)) => quote(bump, local_len, meta_values, value),
            Some(None) => Expr::MetaVar(var),
            None => panic!("Unbound meta var: {var:?}"),
        },
    }
}

pub fn quote_fun<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    local_len: EnvLen,
    meta_values: &MetaValues<'core>,
    param: FunParam<&'core Value<'core>>,
    closure: Closure<'core>,
) -> (FunParam<&'core Expr<'core>>, &'core Expr<'core>) {
    let r#type = quote(bump, local_len, meta_values, param.r#type);

    let arg = Value::local_var(local_len.to_absolute());
    let body = apply_closure(bump, opts, meta_values, closure, arg);
    let body = quote(bump, local_len.succ(), meta_values, &body);

    let (r#type, body) = bump.alloc((r#type, body));

    (FunParam::new(param.plicity, param.name, r#type), body)
}

pub fn update_metas<'core>(
    bump: &'core bumpalo::Bump,
    opts: EvalOpts,
    meta_values: &MetaValues<'core>,
    value: &Value<'core>,
) -> Value<'core> {
    let mut value = value.clone();
    while let Value::Neutral {
        head: Head::MetaVar(var),
        spine,
    } = value
    {
        match meta_values.get_absolute(var) {
            Some(Some(head)) => {
                value = (spine.into_iter()).fold(head.clone(), |head, elim| match elim {
                    Elim::FunApp(arg) => fun_app(bump, opts, meta_values, head, arg),
                    Elim::BoolCases(cases) => apply_bool_elim(bump, opts, meta_values, cases, head),
                    Elim::RecordProj(name) => record_proj(head, name),
                });
            }
            Some(None) => {
                return Value::Neutral {
                    head: Head::MetaVar(var),
                    spine,
                }
            }
            None => panic!("Unbound meta var: {var:?}"),
        }
    }
    value
}

pub fn normalize<'core>(
    bump: &'core bumpalo::Bump,
    local_values: &mut LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    expr: &Expr<'core>,
) -> Expr<'core> {
    let value = eval(bump, EvalOpts::default(), local_values, meta_values, expr);
    quote(bump, local_values.len(), meta_values, &value)
}

pub fn zonk<'core>(
    bump: &'core bumpalo::Bump,
    local_values: &mut LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    expr: &Expr<'core>,
) -> Expr<'core> {
    match expr {
        Expr::Error => Expr::Error,
        Expr::Const(r#const) => Expr::Const(*r#const),
        Expr::Prim(prim) => Expr::Prim(*prim),
        Expr::LocalVar(var) => Expr::LocalVar(*var),

        Expr::Let {
            name,
            r#type,
            init,
            body,
        } => {
            let r#type = zonk(bump, local_values, meta_values, r#type);
            let init = zonk(bump, local_values, meta_values, init);
            let body = zonk_with_local(bump, local_values, meta_values, body);
            let (r#type, init, body) = bump.alloc((r#type, init, body));
            Expr::Let {
                name: *name,
                r#type,
                init,
                body,
            }
        }
        Expr::FunType { param, body } => {
            let r#type = zonk(bump, local_values, meta_values, param.r#type);
            let body = zonk_with_local(bump, local_values, meta_values, body);
            let (r#type, body) = bump.alloc((r#type, body));
            Expr::FunType {
                param: FunParam::new(param.plicity, param.name, r#type),
                body,
            }
        }
        Expr::FunLit { param, body } => {
            let r#type = zonk(bump, local_values, meta_values, param.r#type);
            let body = zonk_with_local(bump, local_values, meta_values, body);
            let (r#type, body) = bump.alloc((r#type, body));
            Expr::FunLit {
                param: FunParam::new(param.plicity, param.name, r#type),
                body,
            }
        }

        Expr::MetaVar(..) | Expr::FunApp { .. } | Expr::If { .. } | Expr::RecordProj(..) => {
            match zonk_meta_var_spines(bump, local_values, meta_values, expr) {
                Left(expr) => expr,
                Right(value) => {
                    let expr = quote(bump, local_values.len(), meta_values, &value);
                    zonk(bump, local_values, meta_values, &expr)
                }
            }
        }
        Expr::RecordType(type_fields) => {
            let local_len = local_values.len();
            let expr_fields = bump.alloc_slice_fill_iter(type_fields.iter().map(|(name, expr)| {
                let r#type = zonk(bump, local_values, meta_values, expr);
                let var = Value::local_var(local_values.len().to_absolute());
                local_values.push(var);
                (*name, r#type)
            }));
            local_values.truncate(local_len);
            Expr::RecordType(expr_fields)
        }
        Expr::RecordLit(expr_fields) => Expr::RecordLit(
            bump.alloc_slice_fill_iter(
                expr_fields
                    .iter()
                    .map(|(name, expr)| (*name, zonk(bump, local_values, meta_values, expr))),
            ),
        ),
    }
}

fn zonk_with_local<'core>(
    bump: &'core bumpalo::Bump,
    local_values: &mut LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    body: &Expr<'core>,
) -> Expr<'core> {
    let var = Value::local_var(local_values.len().to_absolute());
    local_values.push(var);
    let ret = zonk(bump, local_values, meta_values, body);
    local_values.pop();
    ret
}

fn zonk_meta_var_spines<'core>(
    bump: &'core bumpalo::Bump,
    local_values: &mut LocalValues<'core>,
    meta_values: &MetaValues<'core>,
    expr: &Expr<'core>,
) -> Either<Expr<'core>, Value<'core>> {
    let opts = EvalOpts::default();
    match expr {
        Expr::MetaVar(var) => match meta_values.get_absolute(*var) {
            Some(Some(value)) => Right(value.clone()),
            Some(None) => Left(Expr::MetaVar(*var)),
            None => panic!("Unbound meta var: {var:?}"),
        },
        Expr::FunApp { fun, arg } => {
            let fun = zonk_meta_var_spines(bump, local_values, meta_values, fun);
            match fun {
                Left(fun_expr) => {
                    let arg_expr = zonk(bump, local_values, meta_values, arg.expr);
                    let (fun_expr, arg_expr) = bump.alloc((fun_expr, arg_expr));
                    let arg = FunArg::new(arg.plicity, arg_expr as &_);
                    Left(Expr::FunApp { fun: fun_expr, arg })
                }
                Right(fun_value) => {
                    let arg_value = eval(bump, opts, local_values, meta_values, arg.expr);
                    let arg = FunArg::new(arg.plicity, arg_value);
                    Right(fun_app(bump, opts, meta_values, fun_value, arg))
                }
            }
        }
        Expr::RecordProj(scrut, name) => {
            let scrut = zonk_meta_var_spines(bump, local_values, meta_values, scrut);
            match scrut {
                Left(scrut_expr) => Left(Expr::RecordProj(bump.alloc(scrut_expr), *name)),
                Right(scrut_value) => Right(record_proj(scrut_value, *name)),
            }
        }
        Expr::If { cond, then, r#else } => {
            match zonk_meta_var_spines(bump, local_values, meta_values, cond) {
                Left(cond) => {
                    let then = zonk(bump, local_values, meta_values, then);
                    let r#else = zonk(bump, local_values, meta_values, r#else);
                    let (cond, then, r#else) = bump.alloc((cond, then, r#else));
                    Left(Expr::If { cond, then, r#else })
                }
                Right(cond) => {
                    let cases = BoolCases::new(local_values.clone(), then, r#else);
                    Right(apply_bool_elim(bump, opts, meta_values, cases, cond))
                }
            }
        }
        expr => Left(zonk(bump, local_values, meta_values, expr)),
    }
}
