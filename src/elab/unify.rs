use codespan_reporting::diagnostic::{Diagnostic, Label};
use text_size::TextRange;

use crate::core::semantics::{self, Closure, Elim, EvalOpts, Head, MetaValues, Value};
use crate::core::syntax::{Const, Expr, FunArg, FunParam};
use crate::env::{AbsoluteVar, EnvLen, RelativeVar, SharedEnv, SliceEnv, UniqueEnv};
use crate::plicity::Plicity;
use crate::slice_vec::SliceVec;

/// Unification context.
pub struct UnifyCtx<'core, 'env> {
    bump: &'core bumpalo::Bump,
    renaming: &'env mut PartialRenaming,
    local_env: EnvLen,
    meta_values: &'env mut MetaValues<'core>,
}

/// A partial renaming from a source environment to a target environment.
#[derive(Default)]
pub struct PartialRenaming {
    /// Mapping from local variables in the source environment to local
    /// variables in the target environment.
    source: UniqueEnv<Option<AbsoluteVar>>,
    /// The length of the target binding environment
    target: EnvLen,
}

impl PartialRenaming {
    /// Re-initialize the renaming to the requested `source_len`, reusing the
    /// previous allocation.
    fn init(&mut self, source_len: EnvLen) {
        self.source.clear();
        self.source.resize(source_len, None);
        self.target.clear();
    }

    fn next_local_var<'core>(&self) -> Value<'core> {
        Value::local_var(self.source.len().to_absolute())
    }

    /// Set a local source variable to local target variable mapping, ensuring
    /// that the variable appears uniquely.
    ///
    /// # Returns
    ///
    /// - `true` if the local binding was set successfully.
    /// - `false` if the local binding was already set.
    fn set_local(&mut self, source_var: AbsoluteVar) -> bool {
        let is_unique = self.get_as_absolute(source_var).is_none();

        if is_unique {
            let target_var = Some(self.target.to_absolute());
            self.source.set_absolute(source_var, target_var);
            self.target.push();
        }

        is_unique
    }

    /// Push an extra local binding onto the renaming.
    fn push_local(&mut self) {
        let target_var = self.target.to_absolute();
        self.source.push(Some(target_var));
        self.target.push();
    }

    /// Pop a local binding off the renaming.
    fn pop_local(&mut self) {
        self.source.pop();
        self.target.pop();
    }

    /// Get the local variable in the target environment that will be used in
    /// place of the `source_var`.
    fn get_as_absolute(&self, source_var: AbsoluteVar) -> Option<AbsoluteVar> {
        self.source.get_absolute(source_var).copied().flatten()
    }

    /// Rename a local variable in the source environment to a local variable in
    /// the target environment.
    fn get_as_relative(&self, source_var: AbsoluteVar) -> Option<RelativeVar> {
        let target_var = self.get_as_absolute(source_var)?;
        Some(self.target.absolute_to_relative(target_var).unwrap())
    }

    fn len(&self) -> (EnvLen, EnvLen) { (self.source.len(), self.target) }

    fn truncate(&mut self, (source_len, target_len): (EnvLen, EnvLen)) {
        self.source.truncate(source_len);
        self.target.truncate(target_len);
    }
}

impl<'core, 'env> UnifyCtx<'core, 'env> {
    pub fn new(
        arena: &'core bumpalo::Bump,
        renaming: &'env mut PartialRenaming,
        local_env: EnvLen,
        meta_values: &'env mut SliceEnv<Option<Value<'core>>>,
    ) -> Self {
        Self {
            bump: arena,
            renaming,
            local_env,
            meta_values,
        }
    }

    pub fn quote_env(&mut self) -> semantics::QuoteEnv<'core, '_> {
        semantics::QuoteEnv::new(self.bump, self.local_env, self.meta_values)
    }

    pub fn elim_env(&mut self) -> semantics::ElimEnv<'core, '_> {
        semantics::ElimEnv::new(self.bump, EvalOpts::default(), self.meta_values)
    }

    /// Unify two values, updating the solution environment if necessary.
    pub fn unify(&mut self, left: &Value<'core>, right: &Value<'core>) -> Result<(), UnifyError> {
        if std::ptr::eq(left, right) {
            return Ok(());
        }

        let left = self.elim_env().update_metas(left);
        let right = self.elim_env().update_metas(right);

        match (left, right) {
            (Value::Const(left), Value::Const(right)) if left == right => Ok(()),

            (Value::Neutral(left_head, left_spine), Value::Neutral(right_head, right_spine))
                if left_head == right_head =>
            {
                self.unify_spines(&left_spine, &right_spine)
            }

            (
                Value::FunType {
                    param: left_param,
                    body: left_body,
                },
                Value::FunType {
                    param: right_param,
                    body: right_body,
                },
            )
            | (
                Value::FunLit {
                    param: left_param,
                    body: left_body,
                },
                Value::FunLit {
                    param: right_param,
                    body: right_body,
                },
            ) => self.unify_funs(left_param, left_body, right_param, right_body),
            // Unify a function literal with a value, using eta-conversion:
            // `(fun x => f x) ?= f`
            (Value::FunLit { param, body, .. }, value)
            | (value, Value::FunLit { param, body, .. }) => {
                let left_var = Value::local_var(self.local_env.to_absolute());
                let right_var = Value::local_var(self.local_env.to_absolute());

                let left_value = self.elim_env().apply_closure(body, left_var);
                let right_value = self
                    .elim_env()
                    .fun_app(value, FunArg::new(param.plicity, right_var));

                self.local_env.push();
                let result = self.unify(&left_value, &right_value);
                self.local_env.pop();

                result
            }

            (Value::RecordType(mut left_telescope), Value::RecordType(mut right_telescope)) => {
                if !crate::slice_eq_by_key(
                    left_telescope.fields,
                    right_telescope.fields,
                    |(field, _)| *field,
                ) {
                    return Err(UnifyError::Mismatch);
                }

                let local_len = self.local_env;

                while let Some((
                    (_, left_value, left_update_telescope),
                    (_, right_value, right_update_telescope),
                )) = Option::zip(
                    self.elim_env().split_telescope(&mut left_telescope),
                    self.elim_env().split_telescope(&mut right_telescope),
                ) {
                    if let Err(error) = self.unify(&left_value, &right_value) {
                        self.local_env.truncate(local_len);
                        return Err(error);
                    }

                    let left_var = Value::local_var(self.local_env.to_absolute());
                    let right_var = Value::local_var(self.local_env.to_absolute());
                    left_update_telescope(left_var);
                    right_update_telescope(right_var);
                    self.local_env.push();
                }

                self.local_env.truncate(local_len);

                Ok(())
            }

            (Value::RecordLit(left_fields), Value::RecordLit(right_fields)) => {
                if !crate::slice_eq_by_key(left_fields, right_fields, |(field, _)| *field) {
                    return Err(UnifyError::Mismatch);
                }

                for ((_, left), (_, right)) in left_fields.iter().zip(right_fields.iter()) {
                    self.unify(left, right)?;
                }

                Ok(())
            }

            // Unify a record literal with a value, using eta-conversion:
            // `{ x = r.x, y = r.y, .. } ?= r`
            (Value::RecordLit(fields), value) | (value, Value::RecordLit(fields)) => {
                for (name, scrut) in fields {
                    let field_value = self.elim_env().record_proj(scrut.clone(), *name);
                    self.unify(&value, &field_value)?;
                }

                Ok(())
            }

            // One of the values has a metavariable at its head, so we
            // attempt to solve it using pattern unification.
            (Value::Neutral(Head::MetaVar(var), spine), value)
            | (value, Value::Neutral(Head::MetaVar(var), spine)) => self.solve(var, &spine, &value),

            (Value::Error, _) | (_, Value::Error) => Ok(()),

            _ => Err(UnifyError::Mismatch),
        }
    }

    /// Unify two elimination spines.
    fn unify_spines(
        &mut self,
        left_spine: &[Elim<'core>],
        right_spine: &[Elim<'core>],
    ) -> Result<(), UnifyError> {
        if left_spine.len() != right_spine.len() {
            return Err(UnifyError::Mismatch);
        }

        for (left_elim, right_elim) in Iterator::zip(left_spine.iter(), right_spine.iter()) {
            match (left_elim, right_elim) {
                (Elim::FunApp(left_arg), Elim::FunApp(right_arg))
                    if left_arg.plicity == right_arg.plicity =>
                {
                    self.unify(&left_arg.expr, &right_arg.expr)?;
                }
                (Elim::BoolCases(left_cases), Elim::BoolCases(right_cases)) => {
                    let left_then = self
                        .elim_env()
                        .apply_bool_elim(left_cases.clone(), Value::Const(Const::Bool(true)));
                    let right_then = self
                        .elim_env()
                        .apply_bool_elim(right_cases.clone(), Value::Const(Const::Bool(true)));
                    self.unify(&left_then, &right_then)?;

                    let left_else = self
                        .elim_env()
                        .apply_bool_elim(left_cases.clone(), Value::Const(Const::Bool(false)));
                    let right_else = self
                        .elim_env()
                        .apply_bool_elim(right_cases.clone(), Value::Const(Const::Bool(false)));
                    self.unify(&left_else, &right_else)?;
                }
                (Elim::RecordProj(left_field), Elim::RecordProj(right_field))
                    if left_field == right_field => {}
                _ => return Err(UnifyError::Mismatch),
            }
        }
        Ok(())
    }

    /// Unify two [closures][Closure].
    fn unify_funs(
        &mut self,
        left_param: FunParam<&Value<'core>>,
        left_body: Closure<'core>,
        right_param: FunParam<&Value<'core>>,
        right_body: Closure<'core>,
    ) -> Result<(), UnifyError> {
        if left_param.plicity != right_param.plicity {
            return Err(UnifyError::Mismatch);
        }

        self.unify(left_param.r#type, right_param.r#type)?;

        let left_var = Value::local_var(self.local_env.to_absolute());
        let right_var = Value::local_var(self.local_env.to_absolute());

        let left_value = self.elim_env().apply_closure(left_body, left_var);
        let right_value = self.elim_env().apply_closure(right_body, right_var);

        self.local_env.push();
        let result = self.unify(&left_value, &right_value);
        self.local_env.pop();

        result
    }

    /// Solve a pattern unification problem that looks like:
    ///
    /// ```text
    /// ?α spine =? value`
    /// ```
    ///
    /// If successful, the metavariable environment will be updated with a
    /// solution that looks something like:
    ///
    /// ```text
    /// ?α := fun spine => value
    /// ```
    fn solve(
        &mut self,
        meta_var: AbsoluteVar,
        spine: &[Elim<'core>],
        value: &Value<'core>,
    ) -> Result<(), UnifyError> {
        self.init_renaming(spine)?;
        let expr = self.rename(meta_var, value)?;
        let fun_expr = self.fun_intros(spine, expr);
        let mut local_values = SharedEnv::new();
        let solution = semantics::EvalEnv::new(
            self.bump,
            EvalOpts::default(),
            &mut local_values,
            self.meta_values,
        )
        .eval(&fun_expr);
        self.meta_values.set_absolute(meta_var, Some(solution));
        Ok(())
    }

    /// Re-initialize the [`UnificationCtx::renaming`] by mapping the local
    /// variables in the spine to the local variables in the solution. This
    /// can fail if the spine does not contain distinct local variables.
    fn init_renaming(&mut self, spine: &[Elim<'core>]) -> Result<(), SpineError> {
        self.renaming.init(self.local_env);

        for elim in spine {
            match elim {
                Elim::FunApp(arg) => match self.elim_env().update_metas(&arg.expr) {
                    Value::Neutral(Head::LocalVar(var), spine)
                        if spine.is_empty() && self.renaming.set_local(var) => {}
                    Value::Neutral(Head::LocalVar(var), _) => {
                        return Err(SpineError::NonLinearSpine(var))
                    }
                    _ => return Err(SpineError::NonLocalFunApp),
                },
                Elim::BoolCases(..) => return Err(SpineError::BoolCases),
                Elim::RecordProj(_) => return Err(SpineError::RecordProj),
            }
        }
        Ok(())
    }

    /// Wrap `expr` in [function literals][Expr::FunLit] that correspond to the
    /// given `spine`.
    fn fun_intros(&self, spine: &[Elim<'core>], expr: Expr<'core>) -> Expr<'core> {
        spine.iter().fold(expr, |expr, elim| match elim {
            Elim::FunApp(..) => Expr::FunLit {
                param: FunParam::new(Plicity::Explicit, None, &Expr::Error),
                body: self.bump.alloc(expr),
            },
            Elim::BoolCases(..) | Elim::RecordProj(_) => {
                unreachable!("should have been caught by `init_renaming`")
            }
        })
    }

    /// Rename `value` to an [`Expr`], while at the same time using the current
    /// renaming to update variable indices, failing if the partial renaming is
    /// not defined (resulting in an [scope error][Error::ScopeError]), and also
    /// checking for occurrences of the `meta_var` (resulting in an [occurs
    /// check error][Error::InfiniteSolution]).
    ///
    /// This allows us to subsequently wrap the returned expr in function
    /// literals, using [`UnificationContext::function_intros`].
    fn rename(
        &mut self,
        meta_var: AbsoluteVar,
        value: &Value<'core>,
    ) -> Result<Expr<'core>, RenameError> {
        let value = self.elim_env().update_metas(value);
        match value {
            Value::Error => Ok(Expr::Error),
            Value::Const(r#const) => Ok(Expr::Const(r#const)),
            Value::Neutral(head, spine) => {
                let head = match head {
                    Head::Prim(prim) => Expr::Prim(prim),
                    Head::LocalVar(var) => match self.renaming.get_as_relative(var) {
                        None => return Err(RenameError::EscapingLocalVar(var)),
                        Some(var) => Expr::LocalVar(var),
                    },
                    Head::MetaVar(var) => match meta_var == var {
                        true => return Err(RenameError::InfiniteSolution),
                        false => Expr::MetaVar(var),
                    },
                };
                spine.iter().try_fold(head, |head, elim| match elim {
                    Elim::FunApp(arg) => {
                        let arg_expr = self.rename(meta_var, &arg.expr)?;
                        let (fun, arg_expr) = self.bump.alloc((head, arg_expr));
                        let arg = FunArg::new(arg.plicity, arg_expr as &_);
                        Ok(Expr::FunApp { fun, arg })
                    }
                    Elim::RecordProj(name) => Ok(Expr::RecordProj(self.bump.alloc(head), *name)),
                    Elim::BoolCases(cases) => {
                        let then = self
                            .elim_env()
                            .apply_bool_elim(cases.clone(), Value::Const(Const::Bool(false)));
                        let then = self.rename(meta_var, &then)?;

                        let r#else = self
                            .elim_env()
                            .apply_bool_elim(cases.clone(), Value::Const(Const::Bool(false)));
                        let r#else = self.rename(meta_var, &r#else)?;

                        let (cond, then, r#else) = self.bump.alloc((head, then, r#else));
                        Ok(Expr::If { cond, then, r#else })
                    }
                })
            }
            Value::FunType { param, body } => {
                let (param, body) = self.rename_fun(meta_var, param, body)?;
                Ok(Expr::FunType { param, body })
            }
            Value::FunLit { param, body } => {
                let (param, body) = self.rename_fun(meta_var, param, body)?;
                Ok(Expr::FunLit { param, body })
            }
            Value::RecordType(telescope) => {
                let initial_renaming_len = self.renaming.len();
                let mut telescope = telescope;
                let mut expr_fields = SliceVec::new(self.bump, telescope.len());

                while let Some((name, value, update_telescope)) =
                    self.elim_env().split_telescope(&mut telescope)
                {
                    match self.rename(meta_var, &value) {
                        Ok(expr) => {
                            expr_fields.push((name, expr));
                            let source_var = self.renaming.next_local_var();
                            update_telescope(source_var);
                            self.renaming.push_local();
                        }
                        Err(error) => {
                            self.renaming.truncate(initial_renaming_len);
                            return Err(error);
                        }
                    }
                }

                self.renaming.truncate(initial_renaming_len);
                Ok(Expr::RecordType(expr_fields.into()))
            }
            Value::RecordLit(value_fields) => {
                let mut expr_fields = SliceVec::new(self.bump, value_fields.len());
                for (name, value) in value_fields {
                    let expr = self.rename(meta_var, value)?;
                    expr_fields.push((*name, expr));
                }
                Ok(Expr::RecordLit(expr_fields.into()))
            }
        }
    }

    /// Rename a closure back into an [`Expr`].
    fn rename_fun(
        &mut self,
        meta_var: AbsoluteVar,
        param: FunParam<&'core Value<'core>>,
        body: Closure<'core>,
    ) -> Result<(FunParam<&'core Expr<'core>>, &'core Expr<'core>), RenameError> {
        let r#type = self.rename(meta_var, param.r#type)?;

        let var = self.renaming.next_local_var();
        let body = self.elim_env().apply_closure(body, var);

        self.renaming.push_local();
        let body = self.rename(meta_var, &body);
        self.renaming.pop_local();

        let (r#type, body) = self.bump.alloc((r#type, body?));
        let param = FunParam::new(param.plicity, param.name, r#type as &_);

        Ok((param, body))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnifyError {
    /// A known part of one value failed to match with a known part of the other
    /// value that we are comparing against.
    //
    // TODO: Return some sort of type-diff
    Mismatch,
    /// An error that was found in the problem spine.
    Spine(SpineError),
    /// An error that occurred when renaming the solution.
    Rename(RenameError),
}

impl UnifyError {
    pub fn to_diagnostic(
        self,
        file_id: usize,
        range: TextRange,
        expected: &str,
        found: &str,
    ) -> Diagnostic<usize> {
        let message = match self {
            Self::Mismatch => format!("type mismatch: expected `{expected}`, found `{found}`"),
            Self::Spine(_) => String::from("variable appeared more than once in problem spine"),
            Self::Rename(_) => {
                String::from("application in problem spine was not a local variable")
            }
        };
        Diagnostic::error()
            .with_message(message)
            .with_labels(vec![Label::primary(file_id, range)])
    }
}

impl From<SpineError> for UnifyError {
    fn from(error: SpineError) -> Self { Self::Spine(error) }
}

impl From<RenameError> for UnifyError {
    fn from(error: RenameError) -> Self { Self::Rename(error) }
}

/// An error that was found in the spine of a unification problem.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SpineError {
    /// A local variable appeared multiple times in the spine of a unification
    /// problem.
    ///
    /// For example:
    ///
    /// ```text
    /// ?α x x =? x`
    /// ```
    ///
    /// This results in two distinct solutions:
    ///
    /// - `?α := fun x _ => x`
    /// - `?α := fun _ x => x`
    ///
    /// We only want unification to result in a unique solution, so we fail
    /// to unify in this case.
    ///
    /// Another example, assuming `true : Bool`, is:
    ///
    /// ```text
    /// ?α true =? true
    /// ```
    ///
    /// This also has multiple solutions, for example:
    ///
    /// - `?α := fun _ => true`
    /// - `?α := fun x => x`
    /// - `?α := fun x => if x then true else false`
    ///
    /// It's also possible that the return type of `?α` is not always `Bool`,
    /// for example:
    ///
    /// ```text
    /// ?α : fun (b : Bool) -> if b then Bool else (Bool -> Bool)
    /// ```
    ///
    /// In this case the example solution `?α := fun _ => true` is not even
    /// well-typed! In contrast, if the problem spine only has distinct local
    /// variables, even if the return type is dependent, local variables block
    /// all computation in the return type, and the pattern solution is
    /// guaranteed to be well-typed.
    /// TODO: add test
    NonLinearSpine(AbsoluteVar),
    /// A function application was in the problem spine, but it wasn't a local
    /// variable.
    NonLocalFunApp,
    BoolCases,
    RecordProj,
}

/// An error that occurred when renaming the solution.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RenameError {
    /// A free local variable in the compared value does not occur in the
    /// problem spine.
    ///
    /// For example, where `z : Type` is a local variable:
    ///
    /// ```text
    /// ?α x y =? z -> z
    /// ```
    ///
    /// There is no solution for this metavariable because `?α` is the
    /// topmost-level scope, so it can only abstract over `x` and `y`, but
    /// these don't occur in `z -> z`.
    EscapingLocalVar(AbsoluteVar),
    /// The metavariable occurs in the value being compared against.
    /// This is sometimes referred to as an 'occurs check' failure.
    ///
    /// For example:
    ///
    /// ```text
    /// ?α =? ?α -> ?α
    /// ```
    ///
    /// Here `?α` occurs in the right hand side, so in order to solve this
    /// metavariable we would end up going into an infinite loop,
    /// attempting to construct larger and larger solutions:
    ///
    /// - `?α =? ?α -> ?α`
    /// - `?α =? (?α -> ?α) -> (?α -> ?α)`
    /// - `?α =? ((?α -> ?α) -> (?α -> ?α)) -> ((?α -> ?α) -> (?α -> ?α))`
    InfiniteSolution,
}
