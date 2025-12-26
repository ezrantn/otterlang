use crate::model::{Config, Package};
use std::{fs, path::Path};
use toml;

pub fn scaffold_katon_project(name: &str) -> std::io::Result<()> {
    let root = Path::new(name);
    if root.exists() {
        println!("Error: Directory '{}' already exists.", name);
        return Ok(());
    }

    let src_path = root.join("src");

    fs::create_dir_all(&src_path)?;

    let config = Config {
        package: Package {
            name: name.to_string(),
            author: "".to_string(),
            version: "0.1.0".to_string(),
        },
    };

    let toml_content = toml::to_string(&config).unwrap();
    fs::write(root.join("config.toml"), toml_content)?;

    fs::write(root.join(".gitignore"), "/target\n")?;

    fs::write(
        root.join("README.md"),
        format!("# {}\n\nInitial Katon project.", name),
    )?;

    let ktn_file_path = root.join("src").join(format!("{}.ktn", name));
    fs::write(ktn_file_path, "// Start coding in Katon!")?;

    Ok(())
}
