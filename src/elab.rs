use codespan_reporting::diagnostic::{Diagnostic, Label};
use text_size::TextRange;

use self::unify::{PartialRenaming, UnifyCtx, UnifyError};
use crate::core::prim::Prim;
use crate::core::semantics::{self, Closure, EvalOpts, Telescope, Type, Value};
use crate::core::syntax::{Const, Expr, FunArg, FunParam};
use crate::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, UniqueEnv};
use crate::plicity::Plicity;
use crate::slice_vec::SliceVec;
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

    pub fn truncate(&mut self, len: EnvLen) {
        self.names.truncate(len);
        self.infos.truncate(len);
        self.types.truncate(len);
        self.values.truncate(len);
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

        let mut expr = Expr::MetaVar(var);
        for (var, info) in AbsoluteVar::iter().zip(self.local_env.infos.iter()) {
            match info {
                LocalInfo::Let => {}
                LocalInfo::Param => {
                    let var = self.local_env.len().absolute_to_relative(var).unwrap();
                    let arg = Expr::LocalVar(var);
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
            EvalOpts::default(),
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

    pub fn quote_offset(&mut self, value: &Value<'core>, offset: usize) -> Expr<'core> {
        semantics::quote(
            self.bump,
            self.local_env.values.len() + EnvLen::from(offset),
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
                let symbol = Symbol::intern(text);

                if let Some(var) = self.local_env.lookup(symbol) {
                    let r#type = self.local_env.types.get_relative(var).unwrap().clone();
                    return Ok((Expr::LocalVar(var), r#type));
                }

                if let Some(prim) = Prim::from_symbol(symbol) {
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
            #[allow(clippy::redundant_closure_for_method_calls)]
            surface::Expr::Let {
                rec: surface::Rec::Nonrec,
                pat,
                r#type,
                init,
                body,
            } => self.elab_let(pat, r#type, init, body, |this, body| this.synth_expr(body)),
            #[allow(clippy::redundant_closure_for_method_calls)]
            surface::Expr::Let {
                rec: surface::Rec::Rec,
                pat,
                r#type,
                init,
                body,
            } => self.elab_letrec(pat, r#type, init, body, |this, body| this.synth_expr(body)),
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
                let fun_type = semantics::update_metas(
                    self.bump,
                    EvalOpts::default(),
                    &self.meta_env.values,
                    &fun_type,
                );

                let (param, body) = match fun_type {
                    Value::FunType { param, body } if arg.data.plicity == param.plicity => {
                        (param, body)
                    }
                    Value::FunType { param, .. } => {
                        let fun_type = self.quote(&fun_type);
                        let fun_type = self.pretty(&fun_type);
                        let diagnostic = Diagnostic::error()
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
                            ]);
                        self.report_diagnostic(diagnostic)?;
                        return Ok((Expr::Error, Type::Error));
                    }
                    Value::Error => return Ok((Expr::Error, Type::Error)),
                    _ => {
                        let fun_type = self.quote(&fun_type);
                        let fun_type = self.pretty(&fun_type);
                        self.report_diagnostic(
                            Diagnostic::error()
                                .with_message(format!("Expected function, found `{fun_type}`"))
                                .with_labels(vec![Label::primary(self.file_id, fun.range)]),
                        )?;
                        return Ok((Expr::Error, Type::Error));
                    }
                };

                let arg_expr = self.check_expr(arg.data.expr, param.r#type)?;
                let arg = self.eval(&arg_expr);
                let output_type = semantics::apply_closure(
                    self.bump,
                    EvalOpts::default(),
                    &self.meta_env.values,
                    body,
                    arg,
                );

                let (fun, arg_expr) = self.bump.alloc((fun_expr, arg_expr));
                let arg = FunArg::new(param.plicity, arg_expr as &_);
                let core_expr = Expr::FunApp { fun, arg };
                Ok((core_expr, output_type))
            }
            surface::Expr::TupleLit(surface_exprs) => {
                let mut expr_fields = SliceVec::new(self.bump, surface_exprs.len());
                let mut type_fields = SliceVec::new(self.bump, surface_exprs.len());

                for (index, surface_expr) in surface_exprs.iter().enumerate() {
                    let (expr, r#type) = self.synth_expr(surface_expr)?;
                    let name = Symbol::tuple_index(index as u32);
                    expr_fields.push((name, expr));
                    type_fields.push((name, self.quote_offset(&r#type, index)));
                }

                let telescope = Telescope::new(self.local_env.values.clone(), type_fields.into());
                Ok((
                    Expr::RecordLit(expr_fields.into()),
                    Type::RecordType(telescope),
                ))
            }
            surface::Expr::RecordType(surface_fields) => {
                let mut type_fields = SliceVec::new(self.bump, surface_fields.len());

                for surface_field in surface_fields {
                    let r#type = self.check_expr_is_type(&surface_field.data.r#type)?;
                    type_fields.push((surface_field.data.name.data, r#type));
                }

                Ok((Expr::RecordType(type_fields.into()), Type::TYPE))
            }
            surface::Expr::RecordLit(surface_fields) => {
                let mut expr_fields = SliceVec::new(self.bump, surface_fields.len());
                let mut type_fields = SliceVec::new(self.bump, surface_fields.len());

                for (index, surface_field) in surface_fields.iter().enumerate() {
                    let (expr, r#type) = self.synth_expr(&surface_field.data.expr)?;
                    let name = surface_field.data.name.data;
                    expr_fields.push((name, expr));
                    type_fields.push((name, self.quote_offset(&r#type, index)));
                }

                let telescope = Telescope::new(self.local_env.values.clone(), type_fields.into());
                Ok((
                    Expr::RecordLit(expr_fields.into()),
                    Type::RecordType(telescope),
                ))
            }
            surface::Expr::RecordProj { scrut, name } => {
                let (scrut_expr, scrut_type) = self.synth_expr(scrut)?;

                let scrut_type = semantics::update_metas(
                    self.bump,
                    EvalOpts::default(),
                    &self.meta_env.values,
                    &scrut_type,
                );

                match scrut_type {
                    Value::RecordType(mut telescope) => {
                        let Some(_) = telescope.fields.iter().find(|(n, _)| *n == name.data) else {
                            self.report_diagnostic(
                                Diagnostic::error()
                                    .with_message(format!("Field `{}` not found", name.data))
                                    .with_labels(vec![Label::primary(self.file_id, name.range)]),
                            )?;
                            return Ok((Expr::Error, Type::Error));
                        };

                        let scrut_value = self.eval(&scrut_expr);
                        while let Some((n, r#type, update_telescope)) = semantics::split_telescope(
                            self.bump,
                            EvalOpts::default(),
                            &self.meta_env.values,
                            &mut telescope,
                        ) {
                            if n == name.data {
                                let expr = Expr::RecordProj(self.bump.alloc(scrut_expr), name.data);
                                return Ok((expr, r#type));
                            }

                            let projected = semantics::record_proj(scrut_value.clone(), name.data);
                            update_telescope(projected);
                        }

                        unreachable!()
                    }
                    Value::Error => Ok((Expr::Error, Type::Error)),
                    _ => {
                        let scrut_type = self.quote(&scrut_type);
                        let scrut_type = self.pretty(&scrut_type);
                        self.report_diagnostic(
                            Diagnostic::error()
                                .with_message(format!("Expected record, found `{scrut_type}`"))
                                .with_labels(vec![Label::primary(self.file_id, name.range)]),
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
            r#type = semantics::update_metas(
                self.bump,
                EvalOpts::default(),
                &self.meta_env.values,
                &r#type,
            );
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
                    r#type = semantics::apply_closure(
                        self.bump,
                        EvalOpts::default(),
                        &self.meta_env.values,
                        body,
                        arg_value,
                    );
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
        let expected = semantics::update_metas(
            self.bump,
            EvalOpts::default(),
            &self.meta_env.values,
            expected,
        );
        match surface_expr.data {
            surface::Expr::Error => Ok(Expr::Error),
            surface::Expr::Hole => {
                let range = surface_expr.range;
                let expr = self.push_unsolved_expr(MetaSource::HoleExpr { range }, expected);
                Ok(expr)
            }
            surface::Expr::Paren { expr } => self.check_expr(expr, &expected),
            surface::Expr::Let {
                rec: surface::Rec::Nonrec,
                pat,
                r#type,
                init,
                body,
            } => {
                let (expr, ()) = self.elab_let(pat, r#type, init, body, |this, body| {
                    let body = this.check_expr(body, &expected)?;
                    Ok((body, ()))
                })?;
                Ok(expr)
            }
            surface::Expr::Let {
                rec: surface::Rec::Rec,
                pat,
                r#type,
                init,
                body,
            } => {
                let (expr, ()) = self.elab_letrec(pat, r#type, init, body, |this, body| {
                    let body = this.check_expr(body, &expected)?;
                    Ok((body, ()))
                })?;
                Ok(expr)
            }
            surface::Expr::If { cond, then, r#else } => {
                let cond = self.check_expr(cond, &Type::BOOL)?;
                let then = self.check_expr(then, &expected)?;
                let r#else = self.check_expr(r#else, &expected)?;
                let (cond, then, r#else) = self.bump.alloc((cond, then, r#else));
                Ok(Expr::If { cond, then, r#else })
            }
            surface::Expr::FunLit { params, body } => self.check_fun_lit(params, body, &expected),

            surface::Expr::TupleLit(surface_exprs) if expected.is_type() => {
                let len = self.local_env.len();
                let mut type_fields = SliceVec::new(self.bump, surface_exprs.len());
                for (index, expr) in surface_exprs.iter().enumerate() {
                    let name = Symbol::tuple_index(index as u32);
                    let r#type = self.check_expr_is_type(expr)?;
                    let r#type_value = self.eval(&r#type);
                    self.local_env.push_param(None, type_value);
                    type_fields.push((name, r#type));
                }
                let expr = Expr::RecordType(r#type_fields.into());
                self.local_env.truncate(len);
                Ok(expr)
            }
            surface::Expr::RecordLit(surface_fields) => match expected {
                Value::RecordType(mut telescope)
                    if telescope.fields.len() == surface_fields.len()
                        && surface_fields
                            .iter()
                            .map(|field| field.data.name.data)
                            .eq(telescope.fields.iter().map(|(n, _)| *n)) =>
                {
                    let mut expr_fields = SliceVec::new(self.bump, surface_fields.len());
                    for surface_field in surface_fields {
                        let (name, r#type, update_telescope) = semantics::split_telescope(
                            self.bump,
                            EvalOpts::default(),
                            &self.meta_env.values,
                            &mut telescope,
                        )
                        .unwrap();
                        let expr = self.check_expr(&surface_field.data.expr, &r#type)?;
                        let value = self.eval(&expr);
                        update_telescope(value);
                        expr_fields.push((name, expr));
                    }
                    Ok(Expr::RecordLit(expr_fields.into()))
                }
                _ => self.synth_and_convert_expr(surface_expr, &expected),
            },

            // list cases explicitly instead of using `_` so that new cases are not forgotten when
            // new expression variants are added
            surface::Expr::Const(..)
            | surface::Expr::LocalVar { .. }
            | surface::Expr::Ann { .. }
            | surface::Expr::FunArrow { .. }
            | surface::Expr::FunType { .. }
            | surface::Expr::FunApp { .. }
            | surface::Expr::TupleLit(..)
            | surface::Expr::RecordType(..)
            | surface::Expr::RecordProj { .. } => {
                self.synth_and_convert_expr(surface_expr, &expected)
            }
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
                    EvalOpts::default(),
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
                        EvalOpts::default(),
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

    fn elab_let<T>(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_type: Option<&'surface Located<surface::Expr<'surface>>>,
        surface_init: &'surface Located<surface::Expr<'surface>>,
        surface_body: &'surface Located<surface::Expr<'surface>>,
        mut elab_body: impl FnMut(
            &mut Self,
            &'surface Located<surface::Expr<'surface>>,
        ) -> Result<(Expr<'core>, T), E>,
    ) -> Result<(Expr<'core>, T), E> {
        let (name, r#type) = self.synth_ann_pat(surface_pat, surface_type)?;
        let init_expr = self.check_expr(surface_init, &r#type)?;
        let init_value = self.eval(&init_expr);

        let r#type_expr = self.quote(&r#type);
        let (body_expr, body_type) = {
            self.local_env.push_let(name, r#type.clone(), init_value);
            let (body_expr, body_type) = elab_body(self, surface_body)?;
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

    fn elab_letrec<T>(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_type: Option<&'surface Located<surface::Expr<'surface>>>,
        surface_init: &'surface Located<surface::Expr<'surface>>,
        surface_body: &'surface Located<surface::Expr<'surface>>,
        mut elab_body: impl FnMut(
            &mut Self,
            &'surface Located<surface::Expr<'surface>>,
        ) -> Result<(Expr<'core>, T), E>,
    ) -> Result<(Expr<'core>, T), E> {
        let (name, mut r#type) = self.synth_ann_pat(surface_pat, surface_type)?;

        let init_expr = {
            let var = self.local_env.next_var();
            self.local_env.push_let(name, r#type.clone(), var);
            let init_expr = self.check_expr(surface_init, &r#type)?;
            self.local_env.pop();
            init_expr
        };

        let r#type_expr = self.quote(&r#type);
        let init_expr = match init_expr {
            Expr::FunLit { .. } => {
                let opts = EvalOpts::default();
                r#type = semantics::update_metas(
                    self.bump,
                    EvalOpts::default(),
                    &self.meta_env.values,
                    &r#type,
                );
                let Value::FunType { param, body } = &r#type else {
                    unreachable!()
                };

                let (param, output_type) = semantics::quote_fun(
                    self.bump,
                    opts,
                    self.local_env.len(),
                    &self.meta_env.values,
                    *param,
                    body.clone(),
                );

                let fix = &Expr::Prim(Prim::fix);
                Expr::FunApp {
                    fun: self.bump.alloc(Expr::FunApp {
                        fun: self.bump.alloc(Expr::FunApp {
                            fun: fix,
                            arg: FunArg::new(Plicity::Implicit, param.r#type),
                        }),
                        arg: FunArg::new(Plicity::Implicit, output_type),
                    }),
                    arg: FunArg::new(
                        Plicity::Explicit,
                        self.bump.alloc(Expr::FunLit {
                            param: FunParam::new(
                                Plicity::Explicit,
                                name,
                                self.bump.alloc(r#type_expr),
                            ),
                            body: self.bump.alloc(init_expr),
                        }),
                    ),
                }
            }
            Expr::Error => Expr::Error,
            _ => {
                let diagnostic = Diagnostic::error()
                    .with_message("recursive bindings must be function literals")
                    .with_labels(vec![Label::primary(self.file_id, surface_pat.range)]);
                self.report_diagnostic(diagnostic)?;
                Expr::Error
            }
        };

        let (body_expr, body_type) = {
            let init_value = self.eval(&init_expr);
            self.local_env.push_let(name, r#type.clone(), init_value);
            let (body_expr, body_type) = elab_body(self, surface_body)?;
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
                let type_expr = self.check_expr_is_type(surface_ann)?;
                let type_value = self.eval(&type_expr);
                let name = self.check_pat(surface_pat, &type_value)?;
                self.convert_pat(surface_pat.range, &type_value, expected)?;
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
                let name = Some(Symbol::intern(text));
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
                let symbol = Symbol::intern(text);
                Ok(Some(symbol))
            }
            surface::Pat::Paren { pat } => self.check_pat(pat, expected),
        }
    }

    fn convert_pat(
        &mut self,
        range: TextRange,
        from: &Type<'core>,
        to: &Type<'core>,
    ) -> Result<(), E> {
        match self.unify(from, to) {
            Ok(()) => Ok(()),
            Err(error) => {
                let from = self.quote(from);
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
                Ok(())
            }
        }
    }
}
