use codespan_reporting::diagnostic::Diagnostic;
use text_size::TextRange;

use super::{Elaborator, MetaSource};
use crate::core::semantics::{Telescope, Type};
use crate::core::syntax::{Expr, FunParam, Pat};
use crate::env::EnvLen;
use crate::slice_vec::SliceVec;
use crate::surface::{self, Located};
use crate::symbol::{self, Symbol};

impl<'core, 'text, 'surface, H, E> Elaborator<'core, 'text, H, E>
where
    H: FnMut(Diagnostic<usize>) -> Result<(), E>,
{
    pub(super) fn synth_param(
        &mut self,
        surface_param: &'surface Located<surface::FunParam<'surface>>,
    ) -> Result<(Pat<'core>, FunParam<&'core Expr<'core>>, Type<'core>), E> {
        let surface_param = surface_param.data;
        let (pat, r#type_value) =
            self.synth_ann_pat(&surface_param.pat, surface_param.r#type.as_ref())?;
        let name = pat.name();
        let r#type = self.quote_env().quote(&r#type_value);
        Ok((
            pat,
            FunParam::new(surface_param.plicity, name, self.bump.alloc(r#type)),
            type_value,
        ))
    }

    pub(super) fn check_param(
        &mut self,
        surface_param: &'surface Located<surface::FunParam<'surface>>,
        expected: &Type<'core>,
    ) -> Result<(Pat<'core>, FunParam<&'core Expr<'core>>), E> {
        let surface_param = surface_param.data;
        let pat =
            self.check_ann_pat(&surface_param.pat, surface_param.r#type.as_ref(), expected)?;
        let name = pat.name();
        let r#type = self.quote_env().quote(expected);
        let param = FunParam::new(surface_param.plicity, name, self.bump.alloc(r#type) as &_);
        Ok((pat, param))
    }

    pub(super) fn synth_ann_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_ann: Option<&'surface Located<surface::Expr<'surface>>>,
    ) -> Result<(Pat<'core>, Type<'core>), E> {
        match surface_ann {
            None => self.synth_pat(surface_pat),
            Some(surface_ann) => {
                let ann_expr = self.check_expr_is_type(surface_ann)?;
                let ann_value = self.eval_env().eval(&ann_expr);
                let name = self.check_pat(surface_pat, &ann_value)?;
                Ok((name, ann_value))
            }
        }
    }

    pub(super) fn check_ann_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        surface_ann: Option<&'surface Located<surface::Expr<'surface>>>,
        expected: &Type<'core>,
    ) -> Result<Pat<'core>, E> {
        match surface_ann {
            None => self.check_pat(surface_pat, expected),
            Some(surface_ann) => {
                let type_expr = self.check_expr_is_type(surface_ann)?;
                let type_value = self.eval_env().eval(&type_expr);
                let pat = self.check_pat(surface_pat, &type_value)?;
                self.convert_pat(surface_pat.range, pat, &type_value, expected)?;
                Ok(pat)
            }
        }
    }

    fn synth_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
    ) -> Result<(Pat<'core>, Type<'core>), E> {
        match surface_pat.data {
            surface::Pat::Error => Ok((Pat::Error, Type::Error)),
            surface::Pat::Underscore => {
                let range = surface_pat.range;
                let name = None;
                let source = MetaSource::PatType { range, name };
                let r#type = self.push_unsolved_type(source);
                Ok((Pat::Underscore, r#type))
            }
            surface::Pat::Ident => {
                let range = surface_pat.range;
                let text = &self.text[range];
                let name = Symbol::intern(text);
                let source = MetaSource::PatType {
                    range,
                    name: Some(name),
                };
                let r#type = self.push_unsolved_type(source);
                Ok((Pat::Ident(name), r#type))
            }
            surface::Pat::Paren(pat) => self.synth_pat(pat),
            surface::Pat::TupleLit(pats) => {
                let mut pat_fields = SliceVec::new(self.bump, pats.len());
                let mut type_fields = SliceVec::new(self.bump, pats.len());
                for (index, pat) in pats.iter().enumerate() {
                    let name = Symbol::tuple_index(index);
                    let (pat, r#type) = self.synth_pat(pat)?;
                    pat_fields.push((name, pat));
                    type_fields.push((name, self.quote_env().quote_at(&r#type, index)));
                }

                let telescope = Telescope::new(self.local_env.values.clone(), type_fields.into());
                let r#type = Type::RecordType(telescope);
                Ok((Pat::RecordLit(pat_fields.into()), r#type))
            }
            surface::Pat::RecordLit(fields) => {
                let mut pat_fields = SliceVec::new(self.bump, fields.len());
                let mut type_fields = SliceVec::new(self.bump, fields.len());

                for (index, field) in fields.iter().enumerate() {
                    let surface::PatField { name, pat } = field.data;
                    let (pat, r#type) = self.synth_pat(&pat)?;
                    pat_fields.push((name.data, pat));
                    type_fields.push((name.data, self.quote_env().quote_at(&r#type, index)));
                }

                let telescope = Telescope::new(self.local_env.values.clone(), type_fields.into());
                let r#type = Type::RecordType(telescope);
                Ok((Pat::RecordLit(pat_fields.into()), r#type))
            }
        }
    }

    fn check_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Pat<'core>, E> {
        match surface_pat.data {
            surface::Pat::Error => Ok(Pat::Error),
            surface::Pat::Underscore => Ok(Pat::Underscore),
            surface::Pat::Ident => {
                let text = &self.text[surface_pat.range];
                let symbol = Symbol::intern(text);
                Ok(Pat::Ident(symbol))
            }
            surface::Pat::Paren(pat) => self.check_pat(pat, expected),
            surface::Pat::TupleLit(surface_fields) => {
                let Type::RecordType(telescope) = &expected else {
                    return self.synth_and_convert_pat(surface_pat, expected);
                };

                if !symbol::are_tuple_field_names(telescope.fields.iter().map(|(n, _)| *n)) {
                    return self.synth_and_convert_pat(surface_pat, expected);
                }

                let mut telescope = telescope.clone();
                let mut pat_fields = SliceVec::new(self.bump, surface_fields.len());
                for surface_field in surface_fields {
                    let (name, r#type, update_telescope) =
                        self.elim_env().split_telescope(&mut telescope).unwrap();
                    let pat = self.check_pat(surface_field, &r#type)?;
                    pat_fields.push((name, pat));
                    update_telescope(self.local_env.next_var());
                }

                Ok(Pat::RecordLit(pat_fields.into()))
            }
            surface::Pat::RecordLit(surface_fields) => {
                let Type::RecordType(telescope) = &expected else {
                    return self.synth_and_convert_pat(surface_pat, expected);
                };

                if !crate::slice_eq_by_key2(
                    surface_fields,
                    telescope.fields,
                    |field| field.data.name.data,
                    |field| field.0,
                ) {
                    return self.synth_and_convert_pat(surface_pat, expected);
                }

                let mut telescope = telescope.clone();
                let mut pat_fields = SliceVec::new(self.bump, surface_fields.len());
                for surface_field in surface_fields {
                    let (name, r#type, update_telescope) =
                        self.elim_env().split_telescope(&mut telescope).unwrap();
                    let pat = self.check_pat(&surface_field.data.pat, &r#type)?;
                    pat_fields.push((name, pat));
                    update_telescope(self.local_env.next_var());
                }

                Ok(Pat::RecordLit(pat_fields.into()))
            }
        }
    }

    fn synth_and_convert_pat(
        &mut self,
        surface_pat: &'surface Located<surface::Pat<'surface>>,
        expected: &Type<'core>,
    ) -> Result<Pat<'core>, E> {
        let range = surface_pat.range;
        let (pat, r#type) = self.synth_pat(surface_pat)?;
        self.convert_pat(range, pat, &r#type, expected)
    }

    fn convert_pat(
        &mut self,
        range: TextRange,
        pat: Pat<'core>,
        from: &Type<'core>,
        to: &Type<'core>,
    ) -> Result<Pat<'core>, E> {
        match self.unify_env().unify(from, to) {
            Ok(()) => Ok(pat),
            Err(error) => {
                let from = self.quote_env().quote(from);
                let to = self.quote_env().quote(to);

                let found = self.pretty(&from);
                let expected = self.pretty(&to);

                let diagnostic = error.to_diagnostic(self.file_id, range, &expected, &found);
                self.report_diagnostic(diagnostic)?;
                Ok(Pat::Error)
            }
        }
    }

    pub(super) fn destruct_pat(
        &mut self,
        pat: &Pat<'core>,
        expr: &Expr<'core>,
        r#type: &Type<'core>,
        toplevel_param: bool,
    ) -> Vec<(Option<Symbol>, Expr<'core>, Expr<'core>)> {
        fn recur<'core, H, E>(
            ctx: &mut Elaborator<'core, '_, H, E>,
            pat: &Pat<'core>,
            expr: &Expr<'core>,
            r#type: &Type<'core>,
            bindings: &mut Vec<(Option<Symbol>, Expr<'core>, Expr<'core>)>,
            toplevel_param: bool,
        ) where
            H: FnMut(Diagnostic<usize>) -> Result<(), E>,
        {
            match pat {
                Pat::Error | Pat::Underscore => {}
                Pat::Ident(..) if toplevel_param => {}
                Pat::Ident(..) => {
                    let name = pat.name();
                    let r#type = ctx.quote_env().quote_at(r#type, bindings.len());
                    let expr = expr.shift(ctx.bump, EnvLen::from(bindings.len()));
                    bindings.push((name, r#type, expr));
                }
                Pat::RecordLit(pat_fields) => {
                    let r#type = ctx.elim_env().update_metas(r#type);
                    let Type::RecordType(mut telescope) = r#type else {
                        unreachable!("expected record type, got {type:?}")
                    };
                    for (pat_name, pat) in *pat_fields {
                        let (telescope_name, r#type, update_telescope) =
                            ctx.elim_env().split_telescope(&mut telescope).unwrap();
                        debug_assert_eq!(*pat_name, telescope_name);

                        let expr = Expr::RecordProj(ctx.bump.alloc(*expr), *pat_name);

                        recur(ctx, pat, &expr, &r#type, bindings, false);
                        update_telescope(ctx.local_env.next_var());
                    }
                }
            }
        }

        let mut bindings = Vec::new();
        recur(self, pat, expr, r#type, &mut bindings, toplevel_param);
        bindings
    }
}
