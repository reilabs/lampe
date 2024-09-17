//! A container for Lean source-code expressions.

use itertools::Itertools;

use crate::error::emit::{Error, Result};

/// The default string used for each indentation level.
const DEFAULT_INDENT_STRING: &str = "    ";

/// The default line separator.
const DEFAULT_LINE_SEPARATOR: &str = "\n";

/// A stateful handler for the current level of indentation of strings being
/// built.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub struct Indenter {
    /// The string replicated for each indentation level.
    indent_string: String,

    /// The character(s) used to separate lines.
    line_separator: String,

    /// The current indentation level.
    current_level: usize,
}
impl Indenter {
    /// Creates a new indenter configured to use the `indent_string` and
    /// `line_separator` with a default indentation level of zero.
    pub fn new(indent_string: impl Into<String>, line_separator: impl Into<String>) -> Self {
        let current_level = 0;
        let indent_string = indent_string.into();
        let line_separator = line_separator.into();
        Self {
            indent_string,
            line_separator,
            current_level,
        }
    }

    /// Returns the line separator in use.
    #[must_use]
    pub fn sep(&self) -> &str {
        &self.line_separator
    }

    /// Gets the current indentation level.
    #[must_use]
    pub fn level(&self) -> usize {
        self.current_level
    }

    /// Increases the current indentation level by one.
    pub fn indent(&mut self) {
        self.current_level += 1;
    }

    /// Decreases the current indentation level by one.
    ///
    /// # Errors
    ///
    /// - [`Error::CannotDecreaseIndentLevel`] if the indentation level is
    ///   already zero and a decrease in that level is requested.
    pub fn dedent(&mut self) -> Result<()> {
        if self.current_level != 0 {
            self.current_level -= 1;
            Ok(())
        } else {
            Err(Error::CannotDecreaseIndentLevel)
        }
    }

    /// Performs indenting on the provided input.
    pub fn run(&self, input: impl Into<String>) -> String {
        let input: String = input.into();
        let indent = self.indent_string.repeat(self.current_level);

        input
            .split(self.line_separator.as_str())
            .map(|line| format!("{indent}{line}"))
            .join(self.line_separator.as_str())
    }
}

impl Default for Indenter {
    fn default() -> Self {
        Self::new(DEFAULT_INDENT_STRING, DEFAULT_LINE_SEPARATOR)
    }
}

#[cfg(test)]
mod test {
    use crate::{error::emit::Error, lean::indent::Indenter};

    #[test]
    fn can_modify_indent_level() -> anyhow::Result<()> {
        let mut indenter = Indenter::default();

        assert_eq!(indenter.level(), 0);
        indenter.indent();
        assert_eq!(indenter.level(), 1);
        indenter.dedent()?;
        assert_eq!(indenter.level(), 0);

        Ok(())
    }

    #[test]
    fn can_indent_source_text() -> anyhow::Result<()> {
        let mut indenter = Indenter::default();
        let text = "foo";

        assert_eq!(indenter.run(text), text);
        indenter.indent();
        assert_eq!(indenter.run(text), format!("    {text}"));
        indenter.indent();
        assert_eq!(indenter.run(text), format!("        {text}"));
        indenter.dedent()?;
        assert_eq!(indenter.run(text), format!("    {text}"));

        Ok(())
    }

    #[test]
    fn correctly_indents_multiline_text() {
        let mut indenter = Indenter::default();
        let text = "foo\n    bar\n  baz";

        indenter.indent();
        assert_eq!(indenter.run(text), "    foo\n        bar\n      baz");
    }

    #[test]
    fn can_use_specific_indent_strings() {
        let mut indenter = Indenter::new("--", "\n");
        let text = "foo";

        indenter.indent();
        assert_eq!(indenter.run(text), "--foo");
    }

    #[test]
    fn errors_on_decreasing_indent_level_too_far() {
        let mut indenter = Indenter::default();

        let result = indenter.dedent();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), Error::CannotDecreaseIndentLevel);
    }
}
