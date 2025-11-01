// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::transforms::samplify::Position as SamplePosition;
use std::{fmt::Write, marker::PhantomData};

use super::exprs::SmtExpr;

pub(crate) fn var_globalstate_name() -> String {
    "<game-state>".to_string()
}

pub(crate) fn var_ret_name() -> String {
    "__ret".to_string()
}

pub(crate) fn fn_sample_rand_name<S: Into<SmtExpr>>(game_name: &str, rand_sort: S) -> String {
    format!("__sample-rand-{}-{}", game_name, rand_sort.into())
}

/// The kinds of delimiters we use when generating smtlib names
pub(crate) trait Delimiter {
    const DELIMITER: &'static str;
}

macro_rules! defn_delim {
    ($name:ident, $delim:literal) => {
        pub(crate) struct $name;

        impl Delimiter for $name {
            const DELIMITER: &'static str = $delim;
        }
    };
}
defn_delim!(Dash, "-");
defn_delim!(Underscore, "_");

/// The stages of the builder. Abstracted into a trait so we can blanket impl, not just the builder
/// itself but also sections.
pub(crate) trait NameBuilderStage {
    fn write_delimiter(name: &mut String, delimiter: &str);
}

/// The initial state. Don't write a delimiter before this one
pub(crate) struct Empty;

impl NameBuilderStage for Empty {
    #[inline(always)]
    fn write_delimiter(_name: &mut String, _delimiter: &str) {}
}

/// After writing the first element, we need to write the delimiter before any entry
pub(crate) struct NotEmpty;

impl NameBuilderStage for NotEmpty {
    #[inline(always)]
    fn write_delimiter(name: &mut String, delimiter: &str) {
        write!(name, "{delimiter}").unwrap();
    }
}

/// The core NameBuilder. Has a String that we append to when stuff is added.
pub(crate) struct NameBuilder<Delim, Stage: NameBuilderStage> {
    name: String,
    _delim: PhantomData<(Delim, Stage)>,
}

#[allow(private_bounds)]
impl<Delim: Delimiter> NameBuilder<Delim, Empty> {
    /// Create a new builder
    pub(crate) fn new() -> Self {
        // this is just a guess of a somewhat low value that should capture most use cases
        // hopefully
        Self::with_capacity(32)
    }

    /// Create a new builder with the specified capacity preallocated.
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        let mut sort_name = String::with_capacity(capacity);
        sort_name.push('<');

        Self {
            name: sort_name,
            _delim: PhantomData,
        }
    }
}

#[allow(private_bounds)]
impl<Delim: Delimiter, Stage: NameBuilderStage> NameBuilder<Delim, Stage> {
    /// Push a single displayable thing
    pub(crate) fn push(self, part: impl std::fmt::Display) -> NameBuilder<Delim, NotEmpty> {
        let Self {
            name: mut sort_name,
            ..
        } = self;
        Stage::write_delimiter(&mut sort_name, Delim::DELIMITER);
        write!(&mut sort_name, "{part}").unwrap();

        NameBuilder {
            name: sort_name,
            _delim: PhantomData,
        }
    }

    /// Extend the name with a section. Can add multiple items, the logic for that lives in the
    /// code of the respective section. At least one item is written.
    pub(crate) fn extend<Section: NameSection>(
        self,
        section: &Section,
    ) -> NameBuilder<Delim, NotEmpty> {
        section.push_into(self)
    }

    /// Returns the built string.
    pub(crate) fn build(mut self) -> String {
        self.name.push('>');
        self.name
    }
}

impl<Delim: Delimiter> NameBuilder<Delim, NotEmpty> {
    /// Extend the name with a section. Can add multiple items, the logic for that lives in the
    /// code of the respective section. May also not write at all.
    pub(crate) fn maybe_extend<Section: MaybeNameSection>(
        self,
        section: &Section,
    ) -> NameBuilder<Delim, NotEmpty> {
        section.maybe_push_into(self)
    }
}

/// Our convention for Sort names
pub(crate) type SortNameBuilder = NameBuilder<Underscore, Empty>;
/// Our convention for function and term names
pub(crate) type FunctionNameBuilder = NameBuilder<Dash, Empty>;

/// A section
pub(crate) trait NameSection {
    /// Updates the builder arbitrarily, but leaves it in NonEmpty state
    ///
    /// Note: a section may technically return a new empty builder, but that is not the inteded
    /// use!
    fn push_into<Delim: Delimiter, Stage: NameBuilderStage>(
        &self,
        builder: NameBuilder<Delim, Stage>,
    ) -> NameBuilder<Delim, NotEmpty>;
}

pub(crate) trait MaybeNameSection {
    /// Updates the builder arbitrarily. May also not do any writes
    ///
    /// Note: a section may technically return a new empty builder, but that is not the inteded
    /// use!
    fn maybe_push_into<Delim: Delimiter>(
        &self,
        builder: NameBuilder<Delim, NotEmpty>,
    ) -> NameBuilder<Delim, NotEmpty>;
}

// NameSection implies MaybeNameSection
impl<T: NameSection> MaybeNameSection for T {
    fn maybe_push_into<Delim: Delimiter>(
        &self,
        builder: NameBuilder<Delim, NotEmpty>,
    ) -> NameBuilder<Delim, NotEmpty> {
        self.push_into(builder)
    }
}

// NameSection implies MaybeNameSection of Option<T>
impl<T: NameSection> MaybeNameSection for Option<T> {
    fn maybe_push_into<Delim: Delimiter>(
        &self,
        builder: NameBuilder<Delim, NotEmpty>,
    ) -> NameBuilder<Delim, NotEmpty> {
        if let Some(thing) = self {
            thing.push_into(builder)
        } else {
            builder
        }
    }
}

impl<'a> NameSection for String {
    fn push_into<Delim: Delimiter, Stage: NameBuilderStage>(
        &self,
        builder: NameBuilder<Delim, Stage>,
    ) -> NameBuilder<Delim, NotEmpty> {
        builder.push(self)
    }
}

impl NameSection for &str {
    fn push_into<Delim: Delimiter, Stage: NameBuilderStage>(
        &self,
        builder: NameBuilder<Delim, Stage>,
    ) -> NameBuilder<Delim, NotEmpty> {
        builder.push(*self)
    }
}

impl<'a> NameSection for usize {
    fn push_into<Delim: Delimiter, Stage: NameBuilderStage>(
        &self,
        builder: NameBuilder<Delim, Stage>,
    ) -> NameBuilder<Delim, NotEmpty> {
        builder.push(*self)
    }
}

impl NameSection for SamplePosition {
    fn push_into<Delim: Delimiter, Stage: NameBuilderStage>(
        &self,
        builder: NameBuilder<Delim, Stage>,
    ) -> NameBuilder<Delim, NotEmpty> {
        builder
            .push(&self.inst_name)
            .push(&self.oracle_name)
            .push(&self.sample_name)
    }
}
