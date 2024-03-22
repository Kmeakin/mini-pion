use codespan_reporting::diagnostic::{Diagnostic, Label};
use lalrpop_util::lalrpop_mod;

mod lexer;

pub use lexer::{lex, Token, TokenKind};
use text_size::{TextRange, TextSize};

use crate::plicity::Plicity;
use crate::symbol::Symbol;

lalrpop_mod!(
    #[allow(
        clippy::all,
        clippy::pedantic,
        clippy::nursery,
        unused_imports,
        unused_qualifications
    )]
    grammar,
    "/surface/grammar.rs"
);

#[derive(Debug, Copy, Clone)]
pub struct Located<T> {
    pub range: TextRange,
    pub data: T,
}

impl<T> Located<T> {
    pub const fn new(range: TextRange, data: T) -> Self { Self { range, data } }
}

#[derive(Debug, Copy, Clone)]
pub enum Expr<'surface> {
    Error,
    Const(Const),
    LocalVar,
    Hole,

    Paren(&'surface Located<Self>),
    Ann {
        expr: &'surface Located<Self>,
        r#type: &'surface Located<Self>,
    },

    Let {
        rec: Rec,
        pat: &'surface Located<Pat<'surface>>,
        r#type: Option<&'surface Located<Self>>,
        init: &'surface Located<Self>,
        body: &'surface Located<Self>,
    },
    If {
        cond: &'surface Located<Self>,
        then: &'surface Located<Self>,
        r#else: &'surface Located<Self>,
    },

    FunArrow {
        plicity: Plicity,
        lhs: &'surface Located<Self>,
        rhs: &'surface Located<Self>,
    },
    FunType {
        params: &'surface [Located<FunParam<'surface>>],
        body: &'surface Located<Self>,
    },
    FunLit {
        params: &'surface [Located<FunParam<'surface>>],
        body: &'surface Located<Self>,
    },
    FunApp {
        fun: &'surface Located<Self>,
        arg: Located<FunArg<'surface>>,
    },

    TupleLit(&'surface [Located<Self>]),
    RecordType(&'surface [Located<TypeField<'surface>>]),
    RecordLit(&'surface [Located<ExprField<'surface>>]),
    RecordProj {
        scrut: &'surface Located<Self>,
        name: Located<Symbol>,
    },
}

#[derive(Debug, Copy, Clone)]
pub struct TypeField<'surface> {
    pub name: Located<Symbol>,
    pub r#type: Located<Expr<'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub struct ExprField<'surface> {
    pub name: Located<Symbol>,
    pub expr: Located<Expr<'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Rec {
    Rec,
    Nonrec,
}

#[derive(Debug, Copy, Clone)]
pub struct FunParam<'surface> {
    pub plicity: Plicity,
    pub pat: Located<Pat<'surface>>,
    pub r#type: Option<Located<Expr<'surface>>>,
}

#[derive(Debug, Copy, Clone)]
pub struct FunArg<'surface> {
    pub plicity: Plicity,
    pub expr: &'surface Located<Expr<'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Pat<'surface> {
    Error,
    Underscore,
    Ident,
    Paren(&'surface Located<Self>),
    TupleLit(&'surface [Located<Self>]),
    RecordLit(&'surface [Located<PatField<'surface>>]),
}

#[derive(Debug, Copy, Clone)]
pub struct PatField<'surface> {
    pub name: Located<Symbol>,
    pub pat: Located<Pat<'surface>>,
}

#[derive(Debug, Copy, Clone)]
pub enum Const {
    Bool(bool),
    DecInt,
    BinInt,
    HexInt,
}

pub type LalrpopError = lalrpop_util::ParseError<TextSize, TokenKind, std::convert::Infallible>;

const fn error_range(error: &LalrpopError) -> TextRange {
    match error {
        lalrpop_util::ParseError::InvalidToken { location } => TextRange::new(*location, *location),
        lalrpop_util::ParseError::UnrecognizedEof { location, .. } => {
            TextRange::new(*location, *location)
        }
        lalrpop_util::ParseError::UnrecognizedToken { token, .. } => {
            TextRange::new(token.0, token.2)
        }
        lalrpop_util::ParseError::ExtraToken { token } => TextRange::new(token.0, token.2),
        #[allow(clippy::uninhabited_references)]
        lalrpop_util::ParseError::User { error } => match *error {},
    }
}

fn error_to_diagnostic(file_id: usize, range: TextRange, error: LalrpopError) -> Diagnostic<usize> {
    let format_expected = |expected: Vec<String>| match expected.as_slice() {
        [] => unreachable!(),
        [expected] => format!("expected {expected}"),
        [butlast @ .., last] => format!(
            "expected one of {} or {last}",
            butlast
                .iter()
                .map(String::as_str)
                .intersperse(", ")
                .collect::<String>()
        ),
    };

    match error {
        lalrpop_util::ParseError::InvalidToken { .. } => Diagnostic::error()
            .with_message("Syntax error: invalid token")
            .with_labels(vec![Label::primary(file_id, range)]),
        lalrpop_util::ParseError::UnrecognizedEof { expected, .. } => Diagnostic::error()
            .with_message("Syntax error: unexpected end of file")
            .with_labels(vec![
                Label::primary(file_id, range).with_message(format_expected(expected))
            ]),
        lalrpop_util::ParseError::UnrecognizedToken {
            token: (_, token, _),
            expected,
            ..
        } => Diagnostic::error()
            .with_message(format!("Syntax error: unexpected {token}"))
            .with_labels(vec![Label::primary(file_id, range)])
            .with_message(format_expected(expected)),
        lalrpop_util::ParseError::ExtraToken {
            token: (_, token, _),
        } => Diagnostic::error()
            .with_message(format!("Syntax error: unexpected {token}"))
            .with_labels(vec![Label::primary(file_id, range)]),
        lalrpop_util::ParseError::User { error } => match error {},
    }
}

pub fn parse_expr<'surface, E>(
    bump: &'surface bumpalo::Bump,
    handler: &mut impl FnMut(Diagnostic<usize>) -> Result<(), E>,
    file_id: usize,
    text: &str,
) -> Result<Located<Expr<'surface>>, E> {
    let tokens = lex(text)
        .filter(|token| !token.kind.is_trivia())
        .map(|token| (token.range.start(), token.kind, token.range.end()));
    let mut errors = Vec::new();
    let expr = match grammar::ExprParser::new().parse(bump, text, &mut errors, tokens) {
        Ok(expr) => expr,
        Err(error) => {
            let range = error_range(&error);
            errors.push(error);
            Located::new(range, Expr::Error)
        }
    };
    for error in errors {
        let range = error_range(&error);
        handler(error_to_diagnostic(file_id, range, error))?;
    }
    Ok(expr)
}
