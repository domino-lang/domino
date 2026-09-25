// SPDX-License-Identifier: MIT OR Apache-2.0

//! The Rust mirror of `easycrypt cli -json` (format `domino-json/1`, specified in
//! `easycrypt/doc/json-output.md`).
//!
//! The mirror is lenient on purpose: every field a consumer does not read is left out, every
//! optional field defaults, and node kinds are kept as strings, because the format may gain
//! fields and kinds without a version change ("readers must ignore what they do not know").
//! [`Form`] therefore is one struct carrying the union of the fields of the kinds this crate
//! reads, not an enum.

use serde::Deserialize as _;
use serde_derive::Deserialize;

/// The only format version this module understands.
pub const FORMAT_VERSION: &str = "domino-json/1";

/// The answer to one sentence.
#[derive(Debug, Clone, Deserialize)]
pub struct Response {
    pub version: String,
    /// The undo depth after the sentence: `undo <state>.` returns to this state.
    pub state: u64,
    pub status: Status,
    #[serde(default)]
    pub error: Option<EcError>,
    #[serde(default)]
    pub messages: Vec<Message>,
    /// `None` when there is no active proof.
    #[serde(default)]
    pub proof: Option<Proof>,
}

impl Response {
    /// Whether the answer lost its goals: an interrupt that lands while EasyCrypt prints them
    /// leaves the answer without them, with a `critical` message saying so (story 34). The
    /// sentence's effect on the state stands.
    pub fn goals_lost(&self) -> bool {
        self.proof.is_none()
            && self
                .messages
                .iter()
                .any(|m| m.text.starts_with("cannot serialize the goals"))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Status {
    Ok,
    Error,
    Interrupted,
}

#[derive(Debug, Clone, Deserialize)]
pub struct EcError {
    /// Character offsets inside the sentence; `None` if the error has no location.
    #[serde(default)]
    pub loc: Option<Loc>,
    pub msg: String,
}

#[derive(Debug, Clone, Copy, Deserialize)]
pub struct Loc {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Message {
    pub level: String,
    pub text: String,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Proof {
    pub goals: Vec<Goal>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Goal {
    /// The ordinal of the goal among the open goals, from 1. Not stable across commands.
    pub id: u64,
    #[serde(default)]
    pub tvars: Vec<String>,
    #[serde(default)]
    pub hyps: Vec<Hyp>,
    pub concl: Form,
    /// The goal as `cli` prints it.
    #[serde(default)]
    pub text: String,
}

/// A hypothesis. `kind` is `var`, `mem`, `modty`, `hyp` or `abs_st`.
#[derive(Debug, Clone, Deserialize)]
pub struct Hyp {
    pub name: String,
    pub kind: String,
    #[serde(default)]
    pub ident: Option<Ident>,
    #[serde(default, rename = "type")]
    pub ty: Option<Node>,
    #[serde(default)]
    pub form: Option<Form>,
}

/// A binder identity: two binders called `x` have different tags.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Ident {
    pub name: String,
    pub tag: u64,
}

/// A node about which only `kind` and `pp` are read (types, expressions).
#[derive(Debug, Clone, Deserialize)]
pub struct Node {
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub pp: String,
}

/// A formula. Which fields are present depends on `kind` (`equivS`, `equivF`, `app`, `quant`, …);
/// see `json-output.md`.
#[derive(Debug, Clone, Deserialize)]
pub struct Form {
    pub kind: String,
    #[serde(default)]
    pub pp: String,
    /// `app`: the operator path if the head is an operator.
    #[serde(default)]
    pub op: Option<String>,
    #[serde(default)]
    pub head: Option<Box<Form>>,
    /// `app`: the arguments. A `pr` has a single formula (its argument tuple), read as one.
    #[serde(default, deserialize_with = "one_or_many")]
    pub args: Vec<Form>,
    /// `quant`: `forall`, `exists` or `lambda`.
    #[serde(default)]
    pub quantifier: Option<String>,
    #[serde(default)]
    pub binders: Vec<Binder>,
    #[serde(default)]
    pub body: Option<Box<Form>>,
    /// `equivS`: the two programs.
    #[serde(default)]
    pub left: Option<Side>,
    #[serde(default)]
    pub right: Option<Side>,
    #[serde(default)]
    pub pre: Option<Box<Form>>,
    #[serde(default)]
    pub post: Option<Box<Form>>,
}

impl Form {
    /// The two procedures of an `equivF`, `(left, right)`.
    pub fn equiv_procs(&self) -> Option<(&Proc, &Proc)> {
        if self.kind != "equivF" {
            return None;
        }
        Some((self.left.as_ref()?.proc.as_ref()?, self.right.as_ref()?.proc.as_ref()?))
    }
}

#[derive(Debug, Clone, Deserialize)]
pub struct Binder {
    pub name: String,
    #[serde(default)]
    pub kind: String,
    #[serde(default)]
    pub ident: Option<Ident>,
}

/// One side of an `equivS` (`stmt` is the program) or `equivF` (`proc`).
#[derive(Debug, Clone, Deserialize)]
pub struct Side {
    #[serde(default)]
    pub mem: String,
    #[serde(default)]
    pub stmt: Vec<Instr>,
    #[serde(default)]
    pub stmt_pp: String,
    #[serde(default)]
    pub proc: Option<Proc>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct Proc {
    pub path: String,
    /// The module, `Top.Comp_X.Game_X`.
    pub top: String,
    /// The procedure name.
    pub name: String,
    #[serde(default)]
    pub pp: String,
}

/// A program instruction. `kind` is `asgn`, `rnd`, `call`, `if`, `while`, `match`, `raise` or
/// `abstract`.
#[derive(Debug, Clone, Deserialize)]
pub struct Instr {
    pub kind: String,
    #[serde(default)]
    pub pp: String,
    /// `if`, `while`.
    #[serde(default)]
    pub cond: Option<Node>,
    #[serde(default, rename = "then")]
    pub then_block: Vec<Instr>,
    #[serde(default, rename = "else")]
    pub else_block: Vec<Instr>,
    /// `asgn`, `rnd`, `call`.
    #[serde(default)]
    pub lvalue: Option<LValue>,
}

#[derive(Debug, Clone, Deserialize)]
pub struct LValue {
    #[serde(default)]
    pub pp: String,
}

/// Parses one line of an EasyCrypt answer.
///
/// The recursion limit is off: after a few `sp`s the goals nest a formula deeper than serde's
/// default of 128, and the answer is still well-formed. The caller must have stack for it (the
/// session parses on a thread with a large one).
pub fn parse_response(line: &str) -> Result<Response, serde_json::Error> {
    let mut deserializer = serde_json::Deserializer::from_str(line);
    deserializer.disable_recursion_limit();
    let response = Response::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(response)
}

/// A list of formulas, or a single formula (`pr`'s `args`) as a list of one.
fn one_or_many<'de, D>(deserializer: D) -> Result<Vec<Form>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    #[derive(Deserialize)]
    #[serde(untagged)]
    enum OneOrMany {
        Many(Vec<Form>),
        One(Box<Form>),
    }
    Ok(match OneOrMany::deserialize(deserializer)? {
        OneOrMany::Many(v) => v,
        OneOrMany::One(f) => vec![*f],
    })
}
