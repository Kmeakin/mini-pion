use codespan_reporting::diagnostic::{Diagnostic, Label};
use text_size::TextRange;

use self::unify::{PartialRenaming, UnifyCtx};
use crate::core::semantics::{self, EvalOpts, Type, Value};
use crate::core::syntax::{Expr, FunArg};
use crate::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, UniqueEnv};
use crate::plicity::Plicity;
use crate::symbol::Symbol;

mod expr;
mod pat;

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

impl<'core, 'text, H, E> Elaborator<'core, 'text, H, E>
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
        self.eval_env().eval(&expr)
    }

    pub fn elim_env(&mut self) -> semantics::ElimEnv<'core, '_> {
        semantics::ElimEnv::new(self.bump, EvalOpts::default(), &self.meta_env.values)
    }

    pub fn eval_env(&mut self) -> semantics::EvalEnv<'core, '_> {
        semantics::EvalEnv::new(
            self.bump,
            EvalOpts::default(),
            &mut self.local_env.values,
            &self.meta_env.values,
        )
    }

    pub fn quote_env(&self) -> semantics::QuoteEnv<'core, '_> {
        semantics::QuoteEnv::new(self.bump, self.local_env.len(), &self.meta_env.values)
    }

    pub fn zonk_env(&mut self) -> semantics::ZonkEnv<'core, '_> {
        semantics::ZonkEnv::new(self.bump, &mut self.local_env.values, &self.meta_env.values)
    }

    pub fn unify_env(&mut self) -> UnifyCtx<'core, '_> {
        UnifyCtx::new(
            self.bump,
            &mut self.renaming,
            self.local_env.len(),
            &mut self.meta_env.values,
        )
    }

    pub fn pretty(&mut self, expr: &Expr<'core>) -> String {
        let expr = self.zonk_env().zonk(expr);
        let printer =
            crate::core::print::Printer::new(self.bump, crate::core::print::Config::default());
        let doc = printer.expr(&mut self.local_env.names, &expr).into_doc();
        doc.pretty(usize::MAX).to_string()
    }

    fn push_let_bindings(&mut self, bindings: &[(Option<Symbol>, Expr<'core>, Expr<'core>)]) {
        for (name, r#type, init) in bindings {
            let value = self.eval_env().eval(init);
            let r#type = self.eval_env().eval(r#type);
            self.local_env.push_let(*name, r#type, value);
        }
    }
}
