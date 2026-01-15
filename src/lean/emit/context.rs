use crate::lean::{LEAN_QUOTE_END, LEAN_QUOTE_START};

/// The default contents of a single indentation level.
pub const DEFAULT_INDENTATION_CONTENT: &str = "  ";

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

    /// Set if the current line has had the correct amount of indentation
    /// prepended to it, and unset otherwise.
    current_line_has_indent: bool,
}

/// The basic functionality of the emitter that does not deal specifically with
/// the AST.
impl EmitContext {
    /// Constructs a new emitter which uses the specified
    /// `indent_level_contents` per indentation level.
    #[must_use]
    pub fn new(indent_level_contents: &str) -> Self {
        Self {
            source_buffer:           String::new(),
            indent_level:            0,
            indent_level_contents:   indent_level_contents.to_owned(),
            current_line_has_indent: false,
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

    /// Appends the provided text to the current line of the source buffer.
    ///
    /// If the provided `text` is the first text appended to a line, then this
    /// functional will first prepend the correct amount of indentation.
    pub fn append_to_line(&mut self, text: &str) {
        if !self.current_line_has_indent {
            self.source_buffer.push_str(&self.generate_indent());
            self.current_line_has_indent = true;
        }

        // Unfortunately `<<` is an operator in Lean's syntax, and so we need to put
        // spaces in between a pair of these to prevent a bad parse.
        if self.source_buffer.ends_with('<') && text.starts_with('<') {
            self.source_buffer.push(' ');
            self.source_buffer.push_str(text);
            return;
        }

        // Unfortunately `<i` is an operator in Lean's syntax, so we need to put space
        // in between these two to correct a bad parse.
        if self.source_buffer.ends_with('<') && text.starts_with('i') {
            self.source_buffer.push(' ');
            self.source_buffer.push_str(text);
            return;
        }

        // Unfortunately `>>` is an operator in Lean's syntax, and so we need to put
        // spaces in between a pair of these to prevent a bad parse.
        if self.source_buffer.ends_with('>') && text.starts_with('>') {
            self.source_buffer.push(' ');
            self.source_buffer.push_str(text);
            return;
        }

        self.source_buffer.push_str(text);
    }

    /// Ends the current line and creates a new line that begins with the
    /// current indentation level.
    ///
    /// This means that you need to call [`Self::increase_indent`] or
    /// [`Self::decrease_indent`] **before** calling this method.
    pub fn end_line(&mut self) {
        self.append_to_line("\n");
        self.current_line_has_indent = false;
    }

    /// Ends the current line and decreases the indentation level.
    pub fn end_line_and_dedent(&mut self) {
        self.end_line();
        self.decrease_indent();
    }

    /// Appends the provided `text` to the current line and then begins a new
    /// line with indentation increased one level.
    pub fn finish_line_with_and_then_indent(&mut self, text: &str) {
        self.append_to_line(text);
        self.end_line();
        self.increase_indent();
    }

    /// Quotes the provided `text` between [`LEAN_QUOTE_START`] and
    /// [`LEAN_QUOTE_END`] if it is necessary.
    #[must_use]
    pub fn quote_name_if_needed(text: &str) -> String {
        if text.contains("::") {
            let text = text.replace(LEAN_QUOTE_START, "").replace(LEAN_QUOTE_END, "");
            format!("{LEAN_QUOTE_START}{text}{LEAN_QUOTE_END}")
        } else {
            text.to_string()
        }
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
    use crate::lean::{emit::context::EmitContext, LEAN_QUOTE_END, LEAN_QUOTE_START};

    #[test]
    fn quotes_correctly() {
        assert_eq!(
            EmitContext::quote_name_if_needed("foo::bar42"),
            format!("{LEAN_QUOTE_START}foo::bar42{LEAN_QUOTE_END}")
        );
        assert_eq!(
            EmitContext::quote_name_if_needed("«std-1.0.0-beta.12»::slice::«all»"),
            format!("{LEAN_QUOTE_START}std-1.0.0-beta.12::slice::all{LEAN_QUOTE_END}")
        );
    }

    #[test]
    fn builds_output_correctly() {
        let mut emitter = EmitContext::default();

        // Write a function.
        emitter.append_to_line("noir_def return_three<>() -> Field {");
        emitter.end_line();
        emitter.increase_indent();
        emitter.append_to_line("3 : Field");
        emitter.end_line_and_dedent();
        emitter.append_to_line("}");

        // Check if the output is correct.
        assert_eq!(
            emitter.consume(),
            "noir_def return_three<>() -> Field {\n  3 : Field\n}"
        );
    }
}
