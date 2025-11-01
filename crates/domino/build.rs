// SPDX-License-Identifier: MIT OR Apache-2.0

use clap::{CommandFactory, ValueEnum};
use clap_complete::{generate_to, Shell};
use std::env;
use std::io::Error;

include!("src/cli.rs");

fn main() -> Result<(), Error> {
    let mut cmd = Cli::command();

    let outdir = match env::var_os("OUT_DIR") {
        None => return Ok(()),
        Some(outdir) => outdir,
    };

    for &shell in Shell::value_variants() {
        generate_to(shell, &mut cmd, "domino", &outdir)?;
    }

    Ok(())
}
