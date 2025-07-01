/// The default contents of a single indentation level.
pub const DEFAULT_INDENTATION_CONTENT: &str = "  ";

/// If this is seen at the end of a line, the indent level is increased.
pub const INCREASE_INDENT_TAIL: &str = "{";

/// If this is seen at the end of a line, the indent level is decreased.
pub const DECREASE_INDENT_TAIL: &str = "}";

/// The opening quote for use in the Lean source.
pub const LEAN_QUOTE_START: &str = "«";

/// The closing quote for use in the Lean source.
pub const LEAN_QUOTE_END: &str = "»";

/// Handles the emission of Lean DSL source code for a single module / file pair
/// in the Noir source.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EmitContext {
    /// The current contents of the module source.
    source_buffer: String,

    /// The current indentation level.
    indent_level: usize,

    /// The string repeated per indentation level and prepended to the line.
    indent_level_contents: String,
}

/// The basic functionality of the emitter that does not deal specifically with
/// the AST.
impl EmitContext {
    /// Constructs a new emitter which uses the specified
    /// `indent_level_contents` per indentation level.
    #[must_use]
    pub fn new(indent_level_contents: &str) -> Self {
        Self {
            source_buffer:         String::new(),
            indent_level:          0,
            indent_level_contents: indent_level_contents.to_owned(),
        }
    }

    /// Gets the current indentation level.
    #[must_use]
    pub fn get_indent_level(&self) -> usize {
        self.indent_level
    }

    /// Increases the indentation level by one.
    pub fn increase_indent(&mut self) {
        self.indent_level = self.indent_level.saturating_add(1);
    }

    /// Decreases the indentation level by one.
    pub fn decrease_indent(&mut self) {
        self.indent_level = self.indent_level.saturating_sub(1);
    }

    /// Generates the indent string that is prepended to the current line.
    #[must_use]
    pub fn generate_indent(&self) -> String {
        self.indent_level_contents.repeat(self.indent_level)
    }

    /// Appends a line to the source buffer, implicitly adding a newline at the
    /// end of the provided `content`.
    ///
    /// This will automatically increase the indentation level if the line ends
    /// with [`INCREASE_INDENT_TAIL`] and automatically decrease the indentation
    /// level if the line ends with [`DECREASE_INDENT_TAIL`].
    pub fn append_line(&mut self, content: &str) {
        // Handle any negative changes to indentation that may result from the line.
        if content.ends_with(DECREASE_INDENT_TAIL) {
            self.decrease_indent();
        }

        // Append the correct indent to the buffer.
        self.source_buffer.push_str(&self.generate_indent());

        // Start by appending the line to the buffer.
        self.source_buffer.push_str(content);
        self.source_buffer.push('\n');

        // Handle any positive changes to indentation that may result from the line.
        if content.ends_with(INCREASE_INDENT_TAIL) {
            self.increase_indent();
        }
    }

    /// Quotes the provided `text` between [`LEAN_QUOTE_START`] and
    /// [`LEAN_QUOTE_END`].
    #[must_use]
    pub fn quote(&self, text: &str) -> String {
        format!("{LEAN_QUOTE_START}{text}{LEAN_QUOTE_END}")
    }

    /// Consumes the emitter structure to result in the source buffer that it
    /// has generated.
    #[must_use]
    pub fn consume(self) -> String {
        self.source_buffer
    }
}

impl Default for EmitContext {
    fn default() -> Self {
        Self::new(DEFAULT_INDENTATION_CONTENT)
    }
}

#[cfg(test)]
mod test {
    use crate::lean::emit::context::{EmitContext, LEAN_QUOTE_END, LEAN_QUOTE_START};

    #[test]
    fn quotes_correctly() {
        let emitter = EmitContext::default();
        assert_eq!(
            emitter.quote("foobar42"),
            format!("{LEAN_QUOTE_START}foobar42{LEAN_QUOTE_END}")
        );
    }

    #[test]
    fn increases_indentation_correctly() {
        let mut emitter = EmitContext::default();
        emitter.increase_indent();
        assert_eq!(emitter.get_indent_level(), 1);

        emitter.append_line("foo");
        assert_eq!(emitter.get_indent_level(), 1);

        emitter.append_line("foobar {");
        assert_eq!(emitter.get_indent_level(), 2);
    }

    #[test]
    fn decreases_indentation_correctly() {
        let mut emitter = EmitContext::default();
        emitter.increase_indent();
        emitter.increase_indent();
        assert_eq!(emitter.get_indent_level(), 2);

        emitter.append_line("foo");
        assert_eq!(emitter.get_indent_level(), 2);

        emitter.append_line("}");
        assert_eq!(emitter.get_indent_level(), 1);

        emitter.decrease_indent();
        assert_eq!(emitter.get_indent_level(), 0);
    }

    #[test]
    fn builds_output_correctly() {
        let mut emitter = EmitContext::default();

        // Write a function.
        emitter.append_line("nr_def return_three<>() -> Field {");
        emitter.append_line("3 : Field");
        emitter.append_line("}");

        // Check if the output is correct.
        assert_eq!(
            emitter.consume(),
            "nr_def return_three<>() -> Field {\n  3 : Field\n}\n"
        );
    }
}
