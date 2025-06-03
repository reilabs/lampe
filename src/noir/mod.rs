//! This module contains functionality for interacting with the Noir compiler
//! driver, and easing usage of some of its functionality.
//!
//! They are primarily wrappers to make interaction type-safe in ways that this
//! library cares about.

use std::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use derivative::Derivative;
use noirc_driver::Warnings;

pub mod error;
pub mod project;
pub use project::{parse_workspace, Project};

/// A container for attaching non-fatal compilation warnings to arbitrary data.
///
/// It implements [`Deref`] and [`DerefMut`] to allow the warning information to
/// be attached at any point without having to worry about manually extracting
/// the underlying data to access its properties or call it.
///
/// The warnings can be removed at any time to result in the underlying data.
#[derive(Derivative)]
#[derivative(
    Clone(bound = "T: Clone"),
    Debug(bound = "T: Debug"),
    Default(bound = "T: Default")
)]
pub struct WithWarnings<T> {
    /// The data itself.
    pub data: T,

    /// Any warnings attached to the data (possibly empty).
    pub warnings: Warnings,
}

impl<T> WithWarnings<T> {
    /// Creates a new container to wrap the provided `data` with the provided
    /// `warnings`.
    pub fn new(data: T, warnings: Warnings) -> Self {
        Self { data, warnings }
    }

    /// Wraps the provided data into the container without attaching any
    /// warnings.
    pub fn wrap(data: T) -> Self {
        let warnings = Warnings::new();
        Self::new(data, warnings)
    }

    /// Drops any warnings associated with the data to yield only the data.
    pub fn take(self) -> T {
        self.data
    }

    /// Returns `true` if `self` has warnings associated with it, and `false`
    /// otherwise.
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }
}

impl<T> From<T> for WithWarnings<T> {
    fn from(value: T) -> Self {
        Self::wrap(value)
    }
}

impl<T> Deref for WithWarnings<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<T> DerefMut for WithWarnings<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}
