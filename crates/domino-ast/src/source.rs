use std::path::{Path, PathBuf};

use crate::arena::Arena;

/// Holds a source file contents and file path.
///
/// The contents are needed for parsing, and the path is needed for reporting diagnostics.
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub path: PathBuf,
    pub contents: String,
}

/// We use the arena handle of a source file as the file identifier.
pub type FileId = super::arena::Ref<SourceFile>;

/// A pointer to a specific section of the source file.
///
/// We restrict ourselves to files that are small enough for 32 bit offsets. That gives us 4GiB,
/// which should be enough for source code. This reduces the size of the SourceLocation by 16B (and
/// we have a lot of them).
#[derive(Debug, Clone, Copy)]
pub struct SourceLocation {
    pub file_id: FileId,
    pub start: u32,
    pub end: u32,
}

impl SourceFile {
    /// Reads a source file from a path
    pub fn read_from_path(path: PathBuf) -> std::io::Result<Self> {
        let contents = std::fs::read_to_string(&path)?;

        Ok(Self { path, contents })
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl SourceLocation {
    pub fn from_file_and_pair(file_id: FileId, pair: &crate::Pair) -> Self {
        crate::ast_nodes::trimmed_loc(file_id, pair)
    }
    /// Returns the SourceFile for the location
    pub fn source_file<'a>(&self, arena: &'a Arena<SourceFile>) -> &'a SourceFile {
        arena.get(self.file_id)
    }

    /// Returns the source text that the location refers to
    pub fn text<'a>(&self, arena: &'a Arena<SourceFile>) -> &'a str {
        &self.source_file(arena).contents()[self.start as usize..self.end as usize]
    }
}
