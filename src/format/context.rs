// SPDX-License-Identifier: MIT OR Apache-2.0

#[derive(Debug, Clone)]
pub struct FormatContext<'a> {
    pub file_name: &'a str,
    #[allow(dead_code)]
    pub file_content: &'a str,

    pub indent_level: usize,
    buffer: String,
}

impl<'a> FormatContext<'a> {
    pub fn new(file_name: &'a str, file_content: &'a str) -> Self {
        FormatContext {
            file_name,
            file_content,
            indent_level: 0,
            buffer: String::new(),
        }
    }

    pub fn to_str(&self) -> &str {
        &self.buffer
    }

    pub fn is_package(&self) -> bool {
        self.file_name.ends_with(".pkg.ssp")
    }

    pub fn is_game(&self) -> bool {
        self.file_name.ends_with(".comp.ssp")
    }

    pub fn push_line(&mut self, line: &str) {
        if line.is_empty() {
            self.buffer.push('\n');
        } else {
            let indent = "    ".repeat(self.indent_level);
            self.buffer.push_str(&format!("{indent}{line}\n"));
        }
    }

    pub fn push_lines(&mut self, lines: &[&str]) {
        for line in lines {
            self.push_line(line);
        }
    }

    pub fn add_indent(&mut self) {
        self.indent_level += 1
    }

    pub fn remove_indent(&mut self) {
        self.indent_level = if self.indent_level > 0 {
            self.indent_level - 1
        } else {
            0
        }
    }
}
