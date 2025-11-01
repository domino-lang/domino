// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt::Display;

use super::s_expr::SpecConstant;

pub const WHITE_SPACE: [char; 4] = ['\t', '\r', '\n', ' '];
pub const SIMPLE_SYM_SPECIAL: [char; 17] = [
    '~', '!', '@', '$', '%', '^', '&', '*', '_', '-', '+', '=', '<', '>', '.', '?', '/',
];

pub const RESERVED_WORDS: [&str; 13] = [
    "BINARY",
    "DECIMAL",
    "HEXADECIMAL",
    "NUMERAL",
    "STRING",
    "_",
    "!",
    "as",
    "let",
    "exists",
    "forall",
    "match",
    "par",
];

#[derive(Debug, Clone)]
pub enum ReservedWord {
    Binary,
    Decimal,
    Hexadecimal,
    Numeral,
    String,
    Underscore,
    Bang,
    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,
}

impl Display for ReservedWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            ReservedWord::Binary => "BINARY",
            ReservedWord::Decimal => "DECIMAL",
            ReservedWord::Hexadecimal => "HEXADECIMAL",
            ReservedWord::Numeral => "NUMERAL",
            ReservedWord::String => "STRING",
            ReservedWord::Underscore => "_",
            ReservedWord::Bang => "!",
            ReservedWord::As => "as",
            ReservedWord::Let => "let",
            ReservedWord::Exists => "exists",
            ReservedWord::Forall => "forall",
            ReservedWord::Match => "match",
            ReservedWord::Par => "par",
        };

        write!(f, "{text}")
    }
}

#[derive(Debug, Clone)]
pub struct Numeral(pub u64);

impl Numeral {
    pub fn into_const(self) -> SpecConstant {
        SpecConstant::Numeral(self)
    }
}

impl Display for Numeral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<u64> for Numeral {
    fn from(value: u64) -> Self {
        Self(value)
    }
}

/// {left}.{0 ^ zeroes}{right}
#[derive(Debug, Clone)]
pub struct Decimal {
    pub left: u64,
    pub right: u64,
    pub zeroes: usize,
}

impl Decimal {
    pub fn into_const(self) -> SpecConstant {
        SpecConstant::Decimal(self)
    }
}
impl Display for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { left, right, .. } = self;
        let zeroes = "0".repeat(self.zeroes);

        write!(f, "{left}.{zeroes}{right}")
    }
}

#[derive(Debug, Clone)]
pub struct Hexadecimal {
    pub nibbles: Vec<u8>,
}

impl Hexadecimal {
    pub fn into_const(self) -> SpecConstant {
        SpecConstant::Hexadecimal(self)
    }
}
impl Display for Hexadecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        assert!(!self.nibbles.is_empty());

        write!(f, "#x")?;
        for nibble in &self.nibbles {
            assert!(*nibble < 0x10);

            write!(f, "{:x}", nibble)?;
        }

        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct Binary {
    pub bits: Vec<bool>,
}

impl Binary {
    pub fn into_const(self) -> SpecConstant {
        SpecConstant::Binary(self)
    }
}
impl Display for Binary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        assert!(!self.bits.is_empty());

        write!(f, "#x")?;
        for bit in &self.bits {
            let bit = if *bit { 1 } else { 0 };
            write!(f, "{:x}", bit)?;
        }

        Ok(())
    }
}

// TODO: add proper parsing/validation for these
#[derive(Debug, Clone)]
pub struct StringLiteral(String);

impl StringLiteral {
    pub fn into_const(self) -> SpecConstant {
        SpecConstant::String(self)
    }
}
impl Display for StringLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"{}\"", self.0)
    }
}

impl From<String> for StringLiteral {
    fn from(value: String) -> Self {
        StringLiteral(value)
    }
}

#[derive(Debug, Clone)]
pub struct Symbol(String);

impl Symbol {
    pub fn parse(sym: impl AsRef<str> + ToString) -> Option<Self> {
        parse_symbol(sym).map(|s| Self(s.to_string()))
    }
}

impl<T: AsRef<str>> From<T> for Symbol {
    fn from(value: T) -> Self {
        Self::parse(value.as_ref()).unwrap()
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub struct Keyword(String);

impl Keyword {
    /// parses the keyword incl. ":"
    pub fn parse(mut kw: String) -> Option<Self> {
        if kw.is_empty() || kw.remove(0) != ':' {
            return None;
        }

        Self::parse_without_colon(kw)
    }

    pub fn parse_without_colon(kw: String) -> Option<Self> {
        parse_simple_symbol(kw).map(Self)
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl AsRef<str> for Keyword {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ":{}", self.0)
    }
}

pub fn parse_symbol<T: AsRef<str>>(sym: T) -> Option<T> {
    if sym.as_ref().chars().next()? == '|' {
        parse_quoted_symbol(sym)
    } else {
        parse_simple_symbol(sym)
    }
}

fn parse_simple_symbol<T: AsRef<str>>(sym: T) -> Option<T> {
    let sym_str = sym.as_ref();
    if !RESERVED_WORDS.contains(&sym_str)
        && sym_str
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || SIMPLE_SYM_SPECIAL.contains(&c))
    {
        Some(sym)
    } else {
        None
    }
}

fn parse_quoted_symbol<T: AsRef<str>>(sym: T) -> Option<T> {
    if sym
        .as_ref()
        .chars()
        .all(|c| !matches!(c, '|' | '\\' | '\x7f'))
    {
        Some(sym)
    } else {
        None
    }
}
