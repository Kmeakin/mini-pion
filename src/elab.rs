use std::str::FromStr;

use codespan_reporting::diagnostic::{Diagnostic, Label};
use text_size::TextRange;

use self::unify::{PartialRenaming, UnifyCtx, UnifyError};
use crate::core::semantics::{self, Closure, Type, Value};
use crate::core::syntax::{Const, Expr, FunArg, FunParam, Prim};
use crate::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, UniqueEnv};
use crate::plicity::Plicity;
use crate::surface::{self, Located};
use crate::symbol::Symbol;

mod unify;

pub struct Elaborator<'core, 'text, H, E>
where
    H: FnMut(Diagnostic<usize>) -> Result<(), E>,
{
    bump: &'core bumpalo::Bump,
    text: &'text str,
    file_id: usize,
    handler: H,

    local_env: LocalEnv<'core>,
    meta_env: MetaEnv<'core>,
    renaming: PartialRenaming,
}

#[derive(Default)]
struct LocalEnv<'core> {
    names: UniqueEnv<Option<Symbol>>,
    infos: UniqueEnv<LocalInfo>,
    types: UniqueEnv<Type<'core>>,
    values: SharedEnv<Value<'core>>,
}

#[derive(Debug, Copy, Clone)]
pub enum LocalInfo {
    Let,
    Param,
}

impl<'core> LocalEnv<'core> {
    pub fn len(&self) -> EnvLen { self.names.len() }

    pub fn push(
        &mut self,
        name: Option<Symbol>,
        info: LocalInfo,
        r#type: Type<'core>,
        value: Value<'core>,
    ) {
        self.names.push(name);
        self.infos.push(info);
        self.types.push(r#type);
        self.values.push(value);
    }

    pub fn push_let(&mut self, name: Option<Symbol>, r#type: Type<'core>, value: Value<'core>) {
        self.push(name, LocalInfo::Let, r#type, value);
    }

    pub fn push_param(&mut self, name: Option<Symbol>, r#type: Type<'core>) {
        let var = Value::local_var(self.values.len().to_absolute());
        self.push(name, LocalInfo::Param, r#type, var);
    }

    pub fn pop(&mut self) {
        self.names.pop();
        self.infos.pop();
        self.types.pop();
        self.values.pop();
    }

    pub fn lookup(&self, sym: Symbol) -> Option<RelativeVar> {
        self.names
            .iter()
            .rev()
            .enumerate()
            .find(|(_, name)| **name == Some(sym))
            .map(|(idx, _)| RelativeVar::from(idx))
    }

    fn next_var(&self) -> Value<'core> { Value::local_var(self.len().to_absolute()) }
}

#[derive(Default)]
struct MetaEnv<'core> {
    sources: UniqueEnv<MetaSource>,
    types: UniqueEnv<Type<'core>>,
    values: UniqueEnv<Option<Value<'core>>>,
}

impl<'core> MetaEnv<'core> {
    fn len(&self) -> EnvLen { self.sources.len() }

    fn push(&mut self, source: MetaSource, r#type: Type<'core>) {
        self.sources.push(source);
        self.types.push(r#type);
        self.values.push(None);
    }

    fn iter(&self) -> impl Iterator<Item = (MetaSource, &Type<'core>, &Option<Value<'core>>)> + '_ {
        self.sources
            .iter()
            .zip(self.types.iter())
            .zip(self.values.iter())
            .map(|((source, r#type), value)| (*source, r#type, value))
    }
}

#[derive(Debug, Copy, Clone)]
pub enum MetaSource {
    PatType {
        range: TextRange,
        name: Option<Symbol>,
    },
    HoleType {
        range: TextRange,
    },
    HoleExpr {
        range: TextRange,
    },
    ImplicitArg {
        range: TextRange,
        name: Option<Symbol>,
    },
}

impl MetaSource {
    pub const fn range(&self) -> TextRange {
        match self {
            Self::PatType { range, .. }
            | Self::HoleType { range, .. }
            | Self::HoleExpr { range, .. }
            | Self::ImplicitArg { range, .. } => *range,
        }
    }
}

impl<'core, 'text, 'surface, H, E> Elaborator<'core, 'text, H, E>
where
    H: FnMut(Diagnostic<usize>) -> Result<(), E>,
{
    pub fn new(bump: &'core bumpalo::Bump, text: &'text str, file_id: usize, handler: H) -> Self {
        Self {
            bump,
            text,
            file_id,
            handler,

            local_env: LocalEnv::default(),
            meta_env: MetaEnv::default(),
            renaming: PartialRenaming::default(),
        }
    }

    fn report_diagnostic(&mut self, diagnostic: Diagnostic<usize>) -> Result<(), E> {
        (self.handler)(diagnostic)
    }

    pub fn report_unsolved_metas(&mut self) -> Result<(), E> {
        let meta_env = std::mem::take(&mut self.meta_env);
        for (id, (source, _, value)) in meta_env.iter().enumerate() {
            if value.is_none() {
                let message = match source {
                    MetaSource::PatType {
                        name: Some(name), ..
                    } => format!("type of variable `{name}`"),
                    MetaSource::PatType { name: None, .. } => {
                        "type of placeholder pattern".to_string()
                    }
                    MetaSource::HoleType { .. } => "type of hole".to_string(),
                    MetaSource::HoleExpr { .. } => "expression to solve hole".to_string(),
                    MetaSource::ImplicitArg {
                        name: Some(name), ..
                    } => format!("implicit argument `{name}`"),
                    MetaSource::ImplicitArg { name: None, .. } => "implicit argument".to_string(),
                };

                self.report_diagnostic(
                    Diagnostic::error()
                        .with_message(format!("Unsolved metavariable: ?{id}"))
                        .with_labels(vec![Label::primary(self.file_id, source.range())
                            .with_message(format!("could not infer {message}"))]),
                )?;
            }
        }
        self.meta_env = meta_env;
        Ok(())
    }

    fn push_unsolved_expr(&mut self, source: MetaSource, r#type: Type<'core>) -> Expr<'core> {
        let var = self.meta_env.len().to_absolute();
        self.meta_env.push(source, r#type);

        let mut expr = Expr::MetaVar { var };
        for (var, info) in AbsoluteVar::iter().zip(self.local_env.infos.iter()) {
            match info {
                LocalInfo::Let => {}
                LocalInfo::Param => {
                    let var = self.local_env.len().absolute_to_relative(var).unwrap();
                    let arg = Expr::LocalVar { var };
                    let (fun, arg) = self.bump.alloc((expr, arg));
                    let arg = FunArg::new(Plicity::Explicit, arg as &_);
                    expr = Expr::FunApp { fun, arg };
                }
            }
        }
        expr
    }

    fn push_unsolved_type(&mut self, source: MetaSource) -> Value<'core> {
        let expr = self.push_unsolved_expr(source, Value::TYPE);
        self.eval(&expr)
    }

    pub fn eval(&mut self, expr: &Expr<'core>) -> Value<'core> {
        semantics::eval(
            self.bump,
            &mut self.local_env.values,
            &self.meta_env.values,
            expr,
        )
    }

    pub fn quote(&mut self, value: &Value<'core>) -> Expr<'core> {
        semantics::quote(
            self.bump,
            self.local_env.values.len(),
            &self.meta_env.values,
            value,
        )
    }

    pub fn normalize(&mut self, expr: &Expr<'core>) -> Expr<'core> {
        semantics::normalize(
            self.bump,
            &mut self.local_env.values,
            &self.meta_env.values,
            expr,
        )
    }

    pub fn zonk(&mut self, expr: &Expr<'core>) -> Expr<'core> {
        semantics::zonk(
            self.bump,
            &mut self.local_env.values,
            &self.meta_env.values,
            expr,
        )
    }

    pub fn unify(&mut self, left: &Value<'core>, right: &Value<'core>) -> Result<(), UnifyError> {
        let mut ctx = UnifyCtx::new(
            self.bump,
            &mut self.renaming,
            self.local_env.len(),
            &mut self.meta_env.values,
        );
        ctx.unify(left, right)
    }

    pub fn pretty(&mut self, expr: &Expr<'core>) -> String {
        let expr = self.zonk(expr);
        let printer =
            crate::core::print::Printer::new(self.bump, crate::core::print::Config::default());
        let doc = printer.expr(&mut self.local_env.names, &expr).into_doc();
        doc.pretty(usize::MAX).to_string()
    }

    pub fn synth_expr(
        &mut self,
        surface_expr: &'surface Located<surface::Expr<'surface>>,
    ) -> Result<(Expr<'core>, Type<'core>), E> {
        match surface_expr.data {
            surface::Expr::Error => Ok((Expr::Error, Type::Error)),
            surface::Expr::Const(r#const) => {
                let mut parse_int = |base| {
                    let text = &self.text[surface_expr.range];
                    match u32::from_str_radix(text, base) {
                        Ok(int) => Ok(Expr::Const(Const::Int(int))),
                        Err(error) => {
                            self.report_diagnostic(
                                Diagnostic::error()
                                    .with_message(format!("Invalid integer literal: {error}"))
                                    .with_labels(vec![Label::primary(
                                        self.file_id,
                                        surface_expr.range,
                                    )]),
                            )?;
                            Ok(Expr::Error)
                        }
                    }
                };
                let (expr, r#type) = match r#const {
                    surface::Const::Bool(b) => (Expr::Const(Const::Bool(b)), Type::BOOL),
                    surface::Const::DecInt => (parse_int(10)?, Type::INT),
                    surface::Const::BinInt => (parse_int(2)?, Type::INT),
                    surface::Const::HexInt => (parse_int(16)?, Type::INT),
                };
                Ok((expr, r#type))
            }
            surface::Expr::LocalVar => {
                let text = &self.text[surface_expr.range];
                let name = Symbol::from(text);

                if let Some(var) = self.local_env.lookup(name) {
                    let r#type = self.local_env.types.get_relative(var).unwrap().clone();
                    return Ok((Expr::LocalVar { var }, r#type));
                }

                if let Ok(prim) = Prim::from_str(text) {
                    let r#type = prim.r#type();
                    return Ok((Expr::Prim(prim), r#type));
                }

                self.report_diagnostic(
                    Diagnostic::error()
                        .with_message(format!("Unbound variable: {text}"))
                        .with_labels(vec![Label::primary(self.file_id, surface_expr.range)]),
                )?;
                Ok((Expr::Error, Type::Error))
            }
            surface::Expr::Hole => {
                let range = surface_expr.range;
                let r#type = self.push_unsolved_type(MetaSource::HoleType { range });
                let expr = self.push_unsolved_expr(MetaSource::HoleExpr { range }, r#type.clone());
                Ok((expr, r#type))
            }
            surface::Expr::Paren { expr } => self.synth_expr(expr),
            surface::Expr::Ann { expr, r#type } => {
                let r#type = self.check_expr_is_type(r#type)?;
                let r#type = self.eval(&r#type);
                let expr = self.check_expr(expr, &r#type)?;
                Ok((expr, r#type))
            }
            surface::Expr::Let {
                pat,
                r#type,
                init,
                body,
            } => {
                let (name, r#type) = self.synth_ann_pat(pat, r#type)?;
                let r#type_expr = self.quote(&r#type);
                let init_expr = self.check_expr(init, &r#type)?;
                let init_value = self.eval(&init_expr);
                let (body_expr, body_type) = {
                    self.local_env.push_let(name, r#type, init_value);
                    let (body_expr, body_type) = self.synth_expr(body)?;
                    self.local_env.pop();
                    (body_expr, body_type)
                };
                let (r#type, init, body) = self.bump.alloc((r#type_expr, init_expr, body_expr));
                let core_expr = Expr::Let {
                    name,
                    r#type,
                    init,
                    body,
                };
                Ok((core_expr, body_type))
            }
            surface::Expr::If { cond, then, r#else } => {
                let cond = self.check_expr(cond, &Type::BOOL)?;
                let (then, then_type) = self.synth_expr(then)?;
                let r#else = self.check_expr(r#else, &then_type)?;
                let (cond, then, r#else) = self.bump.alloc((cond, then, r#else));
                Ok((Expr::If { cond, then, r#else }, then_type))
            }
            surface::Expr::FunArrow { plicity, lhs, rhs } => {
                let param_type = self.check_expr_is_type(lhs)?;
                let body = {
                    let param_type_value = self.eval(&param_type);
                    self.local_env.push_param(None, param_type_value);
                    let body = self.check_expr_is_type(rhs)?;
                    self.local_env.pop();
                    body
                };
                let (param_type, body) = self.bump.alloc((param_type, body));
                let core_expr = Expr::FunType {
                    param: FunParam::new(plicity, None, param_type),
                    body,
                };
                Ok((core_expr, Type::TYPE))
            }
            surface::Expr::FunType { params, body } => self.synth_fun_type(params, body),
            surface::Expr::FunLit { params, body } => self.synth_fun_lit(params, body),
            surface::Expr::FunApp { fun, arg } => {
                let (mut fun_expr, mut fun_type) = self.synth_expr(fun)?;
                if arg.data.plicity == Plicity::Explicit {
                    (fun_expr, fun_type) = self.insert_implicit_apps(arg.range, fun_expr, fun_type);
                }

                match fun_type {
                    Value::Error => Ok((Expr::Error, Type::Error)),
                    Value::FunType { param, .. } if arg.data.plicity != param.plicity => {
                        let fun_type = self.quote(&fun_type);
                        let fun_type = self.pretty(&fun_type);
                        self.report_diagnostic(
                            Diagnostic::error()
                                .with_message(format!(
                                    "Applied {} argument when {} argument was expected",
                                    arg.data.plicity.description(),
                                    param.plicity.description()
                                ))
                                .with_labels(vec![
                                    Label::primary(self.file_id, arg.range).with_message(format!(
                                        "{} argument",
                                        arg.data.plicity.description()
                                    )),
                                    Label::secondary(self.file_id, fun.range)
                                        .with_message(format!("function has type {fun_type}")),
                                ]),
                        )?;
                        Ok((Expr::Error, Type::Error))
                    }
                    Value::FunType { param, body } => {
                        let arg_expr = self.check_expr(arg.data.expr, param.r#type)?;
                        let arg = self.eval(&arg_expr);
                        let output_type =
                            semantics::apply_closure(self.bump, &self.meta_env.values, body, arg);

                        let (fun, arg_expr) = self.bump.alloc((fun_expr, arg_expr));
                        let arg = FunArg::new(param.plicity, arg_expr as &_);
                        let core_expr = Expr::FunApp { fun, arg };
                        Ok((core_expr, output_type))
                    }
                    _ => {
                        let fun_type = self.quote(&fun_type);
                        let fun_type = self.pretty(&fun_type);
                        self.report_diagnostic(
                            Diagnostic::error()
                                .with_message(format!("Expected function, found `{fun_type}`"))
                                .with_labels(vec![Label::primary(self.file_id, fun.range)]),
                        )?;
                        Ok((Expr::Error, Type::Error))
                    }
                }
            }
        }
    }

    /// Wrap an expr in fresh implicit applications that correspond to implicit
    /// parameters in the type provided.
    fn insert_implicit_apps(
        &mut self,
        fun_range: TextRange,
        mut expr: Expr<'core>,
        mut r#type: Type<'core>,
    ) -> (Expr<'core>, Type<'core>) {
        loop {
            r#type = semantics::update_metas(self.bump, &self.meta_env.values, &r#type);
            match r#type {
                Value::FunType { param, body } if param.plicity.is_implicit() => {
                    let source = MetaSource::ImplicitArg {
                        range: fun_range,
                        name: param.name,
                    };
                    let arg_expr = self.push_unsolved_expr(source, param.r#type.clone());
                    let arg_value = self.eval(&arg_expr);

                    let (fun, arg_expr) = self.bump.alloc((expr, arg_expr));

                    let arg = FunArg::new(param.plicity, arg_expr as &_);
                    expr = Expr::FunApp { fun, arg };
                    r#type =
                        semantics::apply_closure(self.bump, &self.meta_env.values, body, arg_value);
                }
                _ => break,
            }
        }
        (expr, r#type)
    }

    fn synth_fun_type(
        &mut self,
        surface_params: &'surface [Located<surface::FunParam<'surface>>],
        surface_body: &'surface Located<surface::Expr<'surface>>,
    ) -> Result<(Expr<'core>, Type<'core>), E> {
        match surface_params.split_first() {
            None => {
                let body = self.check_expr_is_type(surface_body)?;
                Ok((body, Type::TYPE))
            }
            Some((surface_param, surface_params)) => {
                let (param, param_type) = self.synth_param(surface_param)?;
                let body_expr = {
                    self.local_env.push_param(param.name, param_type);
                    let (body_expr, _) = self.synth_fun_type(surface_params, surface_body)?;
                    self.local_env.pop();
                    body_expr
                };
                let core_expr = Expr::FunType {
                    param,
                    body: self.bump.alloc(body_expr),
                };
                Ok((core_expr, Type::TYPE))
            }
        }
    }

    fn synth_fun_lit(
        &mut self,
        surface_params: &'surface [Located<surface::FunParam<'surface>>],
        surface_body: &'surface Located<surface::Expr<'surface>>,
    ) -> Result<(Expr<'core>, Type<'core>), E> {
        match surface_params.split_first() {
            None => self.synth_expr(surface_body),
            Some((surface_param, surface_params)) => {
                let (param, param_type) = self.synth_param(surface_param)?;
                let (body_expr, body_type) = {
                    self.local_env.push_param(param.name, param_type.clone());
                    let (body_expr, body_type) =
                        self.synth_fun_lit(surface_params, surface_body)?;
                    let body_type = self.quote(&body_type);
                    self.local_env.pop();
                    (body_expr, body_type)
                };
                let core_expr = Expr::FunLit {
                    param,
                    body: self.bump.alloc(body_expr),
                };
                let core_type = Value::FunType {
                    param: FunParam::new(param.plicity, param.name, self.bump.alloc(param_type)),
                    body: Closure::new(self.local_env.values.clone(), self.bump.alloc(body_type)),
                };
                Ok((core_expr, core_type))
            }
        }
    }

    pub fn check_expr_is_type(
        &mut self,
        surface_expr: &'surface Located<surface::Expr<'surface>>,
    ) -> Result<Expr<'core>, E> {
        self.check_expr(surface_expr, &Type::TYPE)
    }

    pub fn check_expr(
        &mut self,
        surface_expr: &'surface Located<surface::Expr<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Expr<'core>, E> {
        match surface_expr.data {
            surface::Expr::Error => Ok(Expr::Error),
            surface::Expr::Paren { expr } => self.check_expr(expr, expected),
            surface::Expr::Let {
                pat,
                r#type,
                init,
                body,
            } => {
                let (name, r#type) = self.synth_ann_pat(pat, r#type)?;
                let r#type_expr = self.quote(&r#type);
                let init_expr = self.check_expr(init, &r#type)?;
                let init_value = self.eval(&init_expr);
                let body_expr = {
                    self.local_env.push_let(name, r#type, init_value);
                    let body_expr = self.check_expr(body, expected)?;
                    self.local_env.pop();
                    body_expr
                };
                let (r#type, init, body) = self.bump.alloc((r#type_expr, init_expr, body_expr));
                let core_expr = Expr::Let {
                    name,
                    r#type,
                    init,
                    body,
                };
                Ok(core_expr)
            }
            surface::Expr::If { cond, then, r#else } => {
                let cond = self.check_expr(cond, &Type::BOOL)?;
                let then = self.check_expr(then, expected)?;
                let r#else = self.check_expr(r#else, expected)?;
                let (cond, then, r#else) = self.bump.alloc((cond, then, r#else));
                Ok(Expr::If { cond, then, r#else })
            }
            surface::Expr::FunLit { params, body } => self.check_fun_lit(params, body, expected),

            // list cases explicitly instead of using `_` so that new cases are not forgotten when
            // new expression variants are added
            surface::Expr::Const(..)
            | surface::Expr::LocalVar { .. }
            | surface::Expr::Hole
            | surface::Expr::Ann { .. }
            | surface::Expr::FunArrow { .. }
            | surface::Expr::FunType { .. }
            | surface::Expr::FunApp { .. } => self.synth_and_convert_expr(surface_expr, expected),
        }
    }

    fn check_fun_lit(
        &mut self,
        surface_params: &'surface [Located<surface::FunParam<'surface>>],
        surface_body: &'surface Located<surface::Expr<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Expr<'core>, E> {
        let [surface_param, rest_params @ ..] = surface_params else {
            return self.check_expr(surface_body, expected);
        };

        match expected {
            // If an implicit function is expected, try to generalize the
            // function literal by wrapping it in an implicit function
            Value::FunType {
                param: expected_param,
                body: expected_body,
            } if surface_param.data.plicity.is_explicit()
                && expected_param.plicity.is_implicit() =>
            {
                let r#type = self.quote(expected_param.r#type);

                let var = self.local_env.next_var();
                self.local_env
                    .push_param(expected_param.name, expected_param.r#type.clone());
                let expected = semantics::apply_closure(
                    self.bump,
                    &self.meta_env.values,
                    expected_body.clone(),
                    var,
                );
                let body = self.check_fun_lit(surface_params, surface_body, &expected)?;
                self.local_env.pop();

                let (r#type, body) = self.bump.alloc((r#type, body));
                let param =
                    FunParam::new(expected_param.plicity, expected_param.name, r#type as &_);
                Ok(Expr::FunLit { param, body })
            }
            Value::FunType {
                param: expected_param,
                body: expected_body,
            } if surface_param.data.plicity == expected_param.plicity => {
                let param = self.check_param(surface_param, expected_param.r#type)?;
                let body_expr = {
                    let arg_value = self.local_env.next_var();
                    self.local_env
                        .push_param(param.name, expected_param.r#type.clone());
                    let expected = semantics::apply_closure(
                        self.bump,
                        &self.meta_env.values,
                        expected_body.clone(),
                        arg_value,
                    );
                    let body_expr = self.check_fun_lit(rest_params, surface_body, &expected)?;
                    self.local_env.pop();
                    body_expr
                };
                let core_expr = Expr::FunLit {
                    param,
                    body: self.bump.alloc(body_expr),
                };
                Ok(core_expr)
            }
            _ => {
                let (expr, r#type) = self.synth_fun_lit(surface_params, surface_body)?;
                let range = surface_param.range.cover(surface_body.range);
                self.convert_expr(range, expr, r#type, expected)?;
                Ok(expr)
            }
        }
    }

    fn synth_and_convert_expr(
        &mut self,
        surface_expr: &'surface Located<surface::Expr<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Expr<'core>, E> {
        let range = surface_expr.range;
        let (expr, r#type) = self.synth_expr(surface_expr)?;
        self.convert_expr(range, expr, r#type, expected)
    }

    fn convert_expr(
        &mut self,
        range: TextRange,
        expr: Expr<'core>,
        from: Type<'core>,
        to: &Type<'core>,
    ) -> Result<Expr<'core>, E> {
        // Attempt to specialize exprs with freshly inserted implicit
        // arguments if an explicit function was expected.
        let (expr, from) = match (expr, to) {
            (Expr::FunLit { .. }, _) => (expr, from),
            (_, Type::FunType { param, .. }) if param.plicity.is_explicit() => {
                self.insert_implicit_apps(range, expr, from)
            }
            _ => (expr, from),
        };

        match self.unify(&from, to) {
            Ok(()) => Ok(expr),
            Err(error) => {
                let from = self.quote(&from);
                let to = self.quote(to);

                let found = self.pretty(&from);
                let expected = self.pretty(&to);

                let message = match error {
                    UnifyError::Mismatch => {
                        format!("type mismatch: expected `{expected}`, found `{found}`")
                    }
                    UnifyError::Spine(_) => {
                        "variable appeared more than once in problem spine".into()
                    }
                    UnifyError::Rename(_) => {
                        "application in problem spine was not a local variable".into()
                    }
                };
                let diagnostic = Diagnostic::error()
                    .with_message(message)
                    .with_labels(vec![Label::primary(self.file_id, range)]);
                self.report_diagnostic(diagnostic)?;
                Ok(Expr::Error)
            }
        }
    }

    fn synth_param(
        &mut self,
        surface_param: &'surface Located<surface::FunParam<'surface>>,
    ) -> Result<(FunParam<&'core Expr<'core>>, Type<'core>), E> {
        let surface_param = surface_param.data;
        let (name, r#type_value) =
            self.synth_ann_pat(&surface_param.pat, surface_param.r#type.as_ref())?;
        let r#type = self.quote(&r#type_value);
        Ok((
            FunParam::new(surface_param.plicity, name, self.bump.alloc(r#type)),
            type_value,
        ))
    }

    fn check_param(
        &mut self,
        surface_param: &'surface Located<surface::FunParam<'surface>>,
        expected: &Type<'core>,
    ) -> Result<FunParam<&'core Expr<'core>>, E> {
        let surface_param = surface_param.data;
        let name =
            self.check_ann_pat(&surface_param.pat, surface_param.r#type.as_ref(), expected)?;
        let r#type = self.quote(expected);
        Ok(FunParam::new(
            surface_param.plicity,
            name,
            self.bump.alloc(r#type),
        ))
    }

    fn synth_ann_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_ann: Option<&'surface Located<surface::Expr<'surface>>>,
    ) -> Result<(Option<Symbol>, Type<'core>), E> {
        match surface_ann {
            None => self.synth_pat(surface_pat),
            Some(surface_ann) => {
                let ann_expr = self.check_expr_is_type(surface_ann)?;
                let ann_value = self.eval(&ann_expr);
                let name = self.check_pat(surface_pat, &ann_value)?;
                Ok((name, ann_value))
            }
        }
    }

    fn check_ann_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_ann: Option<&'surface Located<surface::Expr<'surface>>>,
        expected: &Type<'core>,
    ) -> Result<Option<Symbol>, E> {
        match surface_ann {
            None => self.check_pat(surface_pat, expected),
            Some(surface_ann) => {
                let ann_expr = self.check_expr_is_type(surface_ann)?;
                let ann_value = self.eval(&ann_expr);
                let name = self.check_pat(surface_pat, &ann_value)?;
                Ok(name)
            }
        }
    }

    fn synth_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
    ) -> Result<(Option<Symbol>, Type<'core>), E> {
        match surface_pat.data {
            surface::Pat::Error => Ok((None, Type::Error)),
            surface::Pat::Underscore => {
                let range = surface_pat.range;
                let name = None;
                let source = MetaSource::PatType { range, name };
                let r#type = self.push_unsolved_type(source);
                Ok((name, r#type))
            }
            surface::Pat::Ident => {
                let range = surface_pat.range;
                let text = &self.text[range];
                let name = Some(Symbol::from(text));
                let source = MetaSource::PatType { range, name };
                let r#type = self.push_unsolved_type(source);
                Ok((name, r#type))
            }
            surface::Pat::Paren { pat } => self.synth_pat(pat),
        }
    }

    #[allow(clippy::only_used_in_recursion)]
    fn check_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Option<Symbol>, E> {
        match surface_pat.data {
            surface::Pat::Error | surface::Pat::Underscore => Ok(None),
            surface::Pat::Ident => {
                let text = &self.text[surface_pat.range];
                let symbol = Symbol::from(text);
                Ok(Some(symbol))
            }
            surface::Pat::Paren { pat } => self.check_pat(pat, expected),
        }
    }
}

impl Prim {
    pub const fn r#type(self) -> Type<'static> {
        use Plicity::Explicit;

        const INT: &Type<'static> = &Type::INT;

        match self {
            // `Type : Type`
            // `Int : Type`
            // `Bool : Type`
            Self::Type | Self::Int | Self::Bool => Type::TYPE,

            // `add : Int -> Int -> Int`
            // `sub : Int -> Int -> Int`
            // `mul : Int -> Int -> Int`
            Self::add | Self::sub | Self::mul => Type::FunType {
                param: FunParam {
                    plicity: Explicit,
                    name: None,
                    r#type: INT,
                },
                body: Closure::new(
                    SharedEnv::new(),
                    &Expr::FunType {
                        param: FunParam {
                            plicity: Explicit,
                            name: None,
                            r#type: &Expr::INT,
                        },
                        body: &Expr::INT,
                    },
                ),
            },

            // `eq : Int -> Int -> Bool`
            // `ne : Int -> Int -> Bool`
            // `lt : Int -> Int -> Bool`
            // `gt : Int -> Int -> Bool`
            // `lte : Int -> Int -> Bool`
            // `gte : Int -> Int -> Bool`
            Self::eq | Self::ne | Self::lt | Self::gt | Self::lte | Self::gte => Type::FunType {
                param: FunParam {
                    plicity: Explicit,
                    name: None,
                    r#type: INT,
                },
                body: Closure::new(
                    SharedEnv::new(),
                    &Expr::FunType {
                        param: FunParam {
                            plicity: Explicit,
                            name: None,
                            r#type: &Expr::INT,
                        },
                        body: &Expr::BOOL,
                    },
                ),
            },
        }
    }
}
