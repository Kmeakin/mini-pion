use core::fmt;
use std::ops::Range;

use logos::Logos;
use text_size::{TextRange, TextSize};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Logos)]
#[rustfmt::skip]
pub enum TokenKind {
    Unknown,
    #[regex(r"\s+")]    Whitespace,
    #[regex(r"//.*")]   LineComment,

    #[token("false")]   KwFalse,
    #[token("forall")]  KwForall,
    #[token("fun")]     KwFun,
    #[token("let")]     KwLet,
    #[token("true")]    KwTrue,

    #[token("(")] LParen,
    #[token(")")] RParen,
    #[token("{")] LCurly,
    #[token("}")] RCurly,

    #[token("_", priority = 10)] Underscore,
    #[token(",")] Comma,
    #[token(";")] Semicolon,
    #[token(":")] Colon,
    #[token("@")] At,
    #[token("=")] Eq,
    #[token("=>")] DoubleArrow,
    #[token("->")] SingleArrow,

    #[regex("[0-9][0-9_]*")] DecInt,
    #[regex("0(b|B)[0-1][0-1_]*")] BinInt,
    #[regex("0(x|X)[0-9a-fA-F][0-9a-fA-F_]*")] HexInt,
    #[regex(r"[\p{XID_START}_]\p{XID_CONTINUE}*")] Ident,
}
impl TokenKind {
    pub const fn is_trivia(self) -> bool {
        matches!(self, Self::Unknown | Self::Whitespace | Self::LineComment)
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Unknown => "unknown character",
            Self::Whitespace => "whitespace",
            Self::LineComment => "line comment",
            Self::KwFalse => "keyword `false`",
            Self::KwForall => "keyword `forall`",
            Self::KwFun => "keyword `fun`",
            Self::KwLet => "keyword `let`",
            Self::KwTrue => "keyword `true`",
            Self::LParen => "`(`",
            Self::RParen => "`)`",
            Self::LCurly => "`{`",
            Self::RCurly => "`}`",
            Self::Underscore => "`_`",
            Self::Comma => "`,`",
            Self::Semicolon => "`;`",
            Self::Colon => "`:`",
            Self::At => "`@`",
            Self::Eq => "`=`",
            Self::DoubleArrow => "`=>`",
            Self::SingleArrow => "`->`",
            Self::DecInt | Self::BinInt | Self::HexInt => "integer",
            Self::Ident => "identifier",
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token {
    pub(super) kind: TokenKind,
    pub(super) range: TextRange,
}

impl Token {
    pub const fn new(kind: TokenKind, range: TextRange) -> Self { Self { kind, range } }
}

#[allow(clippy::cast_possible_truncation)]
pub fn lex(text: &str) -> impl Iterator<Item = Token> + '_ {
    TokenKind::lexer(text).spanned().map(|(result, range)| {
        let Range { start, end } = range;
        let (start, end) = (TextSize::new(start as u32), TextSize::new(end as u32));
        let range = TextRange::new(start, end);
        match result {
            Err(()) => Token::new(TokenKind::Unknown, range),
            Ok(kind) => Token::new(kind, range),
        }
    })
}

#[cfg(test)]
mod tests {
    use TokenKind::*;

    use super::*;

    fn range(range: Range<u32>) -> TextRange {
        TextRange::new(TextSize::from(range.start), TextSize::from(range.end))
    }

    fn check(text: &str, expected: &[Token]) {
        let actual: Vec<_> = lex(text).collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn empty() { check("", &[]); }

    #[test]
    fn unknown() {
        #[rustfmt::skip]
        check(
            "🦀🦞",
            &[
                Token { kind: Unknown, range: range(0..4) },
                Token { kind: Unknown, range: range(4..8) },
            ],
        );
    }

    #[test]
    fn line_comments() {
        #[rustfmt::skip]
        check(
            "// line 1\n // line 2",
            &[
                Token { kind: LineComment,  range: range(0..9) },
                Token { kind: Whitespace,   range: range(9..11) },
                Token { kind: LineComment,  range: range(11..20) },
            ]
        );
    }

    #[test]
    fn keywords() {
        #[rustfmt::skip]
        check(
            "false forall fun let true",
            &[
                Token { kind: KwFalse,      range: range(0..5) },
                Token { kind: Whitespace,   range: range(5..6) },
                Token { kind: KwForall,     range: range(6..12) },
                Token { kind: Whitespace,   range: range(12..13) },
                Token { kind: KwFun,        range: range(13..16) },
                Token { kind: Whitespace,   range: range(16..17) },
                Token { kind: KwLet,        range: range(17..20) },
                Token { kind: Whitespace,   range: range(20..21) },
                Token { kind: KwTrue,       range: range(21..25) },
            ],
        );
    }

    #[test]
    fn delimiters() {
        #[rustfmt::skip]
        check(
            "(){}",
            &[
                Token { kind: LParen, range: range(0..1) },
                Token { kind: RParen, range: range(1..2) },
                Token { kind: LCurly, range: range(2..3) },
                Token { kind: RCurly, range: range(3..4) },
            ],
        );
    }

    #[test]
    fn punctuation() {
        #[rustfmt::skip]
        check(
            "_,;:==>->",
            &[
                Token { kind: Underscore,   range: range(0..1) },
                Token { kind: Comma,        range: range(1..2) },
                Token { kind: Semicolon,    range: range(2..3) },
                Token { kind: Colon,        range: range(3..4) },
                Token { kind: Eq,           range: range(4..5) },
                Token { kind: DoubleArrow,  range: range(5..7) },
                Token { kind: SingleArrow,  range: range(7..9) },
            ],
        );
    }

    #[test]
    fn integers() {
        #[rustfmt::skip]
        check(
            "0123456789_ 0b01_ 0x0123456789abcdef_",
            &[
                Token { kind: DecInt,       range: range(0..11) },
                Token { kind: Whitespace,   range: range(11..12) },
                Token { kind: BinInt,       range: range(12..17) },
                Token { kind: Whitespace,   range: range(17..18) },
                Token { kind: HexInt,       range: range(18..37) },
            ],
        );
    }

    #[test]
    fn identifiers() {
        #[rustfmt::skip]
        check(
            "abcDEF_ _hello λ",
            &[
                Token { kind: Ident,        range: range(0..7) },
                Token { kind: Whitespace,   range: range(7..8) },
                Token { kind: Ident,        range: range(8..14) },
                Token { kind: Whitespace,   range: range(14..15) },
                Token { kind: Ident,        range: range(15..17) },
            ],
        );
    }
}