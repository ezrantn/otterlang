// Implement the borrow checker
use crate::ast::{Expr, FnDecl, Stmt};
use std::collections::HashMap;

pub struct BorrowChecker {
    scope: HashMap<String, bool>, // Name -> IsAlive?
}

impl Default for BorrowChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowChecker {
    pub fn new() -> Self {
        Self {
            scope: HashMap::new(),
        }
    }

    pub fn check_fn(&mut self, func: &FnDecl) -> Result<(), String> {
        // Initialize args as Alive
        for param in &func.params {
            self.scope.insert(param.clone(), true);
        }

        // Check Body
        for stmt in &func.body {
            self.check_stmt(stmt)?;
        }

        Ok(())
    }

    fn check_stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::Assign { target, value } => {
                self.check_expr(value)?; // Check RHS first (Use)
                self.scope.insert(target.clone(), true); // Revive LHS (Define)
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.check_expr(cond)?;
                // Cloning scope for simplistic branch checking
                let start_scope = self.scope.clone();

                for s in then_block {
                    self.check_stmt(s)?;
                }

                let then_scope = self.scope.clone(); // <--- Capture state after THEN

                // 3. Process ELSE
                self.scope = start_scope; // Reset
                for s in else_block {
                    self.check_stmt(s)?;
                }

                let else_scope = self.scope.clone(); // <--- Capture state after ELSE

                // Update the current scope to be the intersection of both branches
                self.scope = self.merge_scopes(then_scope, else_scope);

                Ok(())
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<(), String> {
        match expr {
            Expr::Var(name) => {
                if let Some(true) = self.scope.get(name) {
                    // Move semantics
                    // We 'kill' the variable after use
                    // (In a real compiler, check if the type is Copy first. For now, everything moves)
                    self.scope.insert(name.clone(), false);
                    Ok(())
                } else {
                    Err(format!(
                        "Borrow Error: Variable '{}' is used after move or undefined.",
                        name
                    ))
                }
            }
            Expr::Binary(l, _, r) => {
                // Order matters! Left is evaluated/moved first.
                self.check_expr(l)?;
                self.check_expr(r)
            }
            Expr::Old(name) => {
                // old(x) usually borrows, so we might check existence without killing?
                // For safety, let's treat it as a read
                if self.scope.get(name).is_some() {
                    Ok(())
                } else {
                    Err(format!("Undefined variable in old(): {}", name))
                }
            }
            _ => Ok(()),
        }
    }

    fn merge_scopes(
        &self,
        s1: HashMap<String, bool>,
        s2: HashMap<String, bool>,
    ) -> HashMap<String, bool> {
        let mut result = HashMap::new();

        // We iterate over the union of keys, but practically iterating s1 is often enough
        // if we assume new variables declared inside blocks die at end of block.
        // But to be safe, let's look at s1.
        for (key, alive1) in s1 {
            if let Some(&alive2) = s2.get(&key) {
                // It is alive ONLY if it survived BOTH branches.
                // If it was moved (false) in 'then', it's dead (false) here.
                result.insert(key, alive1 && alive2);
            } else {
                // Variable exists in s1 but not s2.
                // This implies it was defined inside the 'then' block.
                // It falls out of scope, so we don't add it to result.
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_borrow_checker_moves() {
        let mut bc = BorrowChecker::new();

        // fn test(x) {
        //    if true {
        //       let y = x; // x moved here
        //    } else {
        //       // x alive here
        //    }
        //    let z = x; // ERROR: x moved in previous branch
        // }

        let func = FnDecl {
            name: "test".to_string(),
            params: vec!["x".to_string()],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Stmt::If {
                    cond: Expr::BoolLit(true),
                    then_block: vec![Stmt::Assign {
                        target: "y".to_string(),
                        value: Expr::Var("x".to_string()),
                    }],
                    else_block: vec![],
                },
                Stmt::Assign {
                    target: "z".to_string(),
                    value: Expr::Var("x".to_string()),
                },
            ],
        };

        let result = bc.check_fn(&func);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            "Borrow Error: Variable 'x' is used after move or undefined."
        );
    }
}
