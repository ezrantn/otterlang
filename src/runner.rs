use std::io::Write;
use std::process::{Command, Stdio};

pub fn verify_with_z3(smt_code: &str) -> Result<(), String> {
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|_| "Could not find 'z3' binary")?;

    child
        .stdin
        .as_mut()
        .ok_or("Failed to open stdin")?
        .write_all(smt_code.as_bytes())
        .map_err(|e| e.to_string())?;

    let output = child.wait_with_output().map_err(|e| e.to_string())?;
    let stdout = String::from_utf8_lossy(&output.stdout);

    println!("Z3 Output:\n{}", stdout);

    // We want to ensure NO "sat" appears.
    // However, "unsat" appearing inside a variable name (rare) could trick us,
    // but standard Z3 output is clean.

    // Simple check: splitting by whitespace
    let last = stdout.lines().map(str::trim).rfind(|l| !l.is_empty());

    match last {
        Some("unsat") => Ok(()),
        Some("sat") => Err("Counter-example found".to_string()),
        Some(other) => Err(format!("Unexpected Z3 result: {}", other)),
        None => Err("Error".to_string()),
    }
}
