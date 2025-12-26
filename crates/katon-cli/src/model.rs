use clap::{Parser, Subcommand};
use serde::Serialize;

#[derive(Parser, Debug)]
#[command(
    name = "katon",
    version,
    about = "Official Katon verifier programming language command line interface",
    arg_required_else_help = false
)]
pub struct Cli {
    #[command(subcommand)]
    pub commands: Option<Commands>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    New {
        #[arg(required = true)]
        project_name: String,
    },

    Verify {
        #[arg(required = true)]
        file_name: String, // Right now it verify one single file, but the future implementation should consider to verify a whole directory by an argument '.' dot
    },

    Transpile {
        #[arg(required = true)]
        to: String, // Transpile Katon code to what language? Right now it only support for Rust programming language
    },
}

#[derive(Serialize)]
pub struct Config {
    pub package: Package,
}

#[derive(Serialize)]
pub struct Package {
    pub name: String,
    pub author: String,
    pub version: String,
}
