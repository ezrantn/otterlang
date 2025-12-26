pub mod model;
pub mod scaffold;

use clap::Parser;
use model::{Cli, Commands};

use crate::scaffold::scaffold_katon_project;

fn main() -> std::io::Result<()> {
    let cli = Cli::parse();

    match cli.commands {
        Some(Commands::New { project_name }) => {
            scaffold_katon_project(&project_name)?;
            println!("Successfully initialized project: {}", project_name);
        }
        _ => println!("Use --help for usage information"),
    }

    Ok(())
}
