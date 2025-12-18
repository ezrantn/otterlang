// Implementation of affine types
use crate::{
    ast::{Expr, FnDecl, NodeId, Op, SExpr, SStmt, Stmt, Type},
    errors::{CheckError, Diagnostic},
    symbol::TyCtx,
};
use std::collections::HashMap;

pub struct BorrowChecker {
    scope: HashMap<NodeId, (bool, Type)>, // Name -> IsAlive?
    id_to_name: HashMap<NodeId, String>,
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
            id_to_name: HashMap::new(),
        }
    }

    pub fn check_fn(&mut self, func: &FnDecl, tcx: &TyCtx) -> Result<(), Diagnostic> {
        // Initialize args as Alive
        // Register variable as Alive with its Type
        for (id, ty) in &func.params {
            self.scope.insert(*id, (true, ty.clone()));
        }

        // Check Body
        for stmt in &func.body {
            self.check_stmt(stmt, tcx)?;
        }

        Ok(())
    }

    fn is_copy(&self, ty: &Type) -> bool {
        match ty {
            Type::Int | Type::Nat => true, // Primitives copy
            Type::Array(_) => false,       // Array moves
        }
    }

    fn check_stmt(&mut self, stmt: &SStmt, tcx: &TyCtx) -> Result<(), Diagnostic> {
        match &stmt.node {
            Stmt::Assign {
                target,
                target_id,
                value,
            } => {
                // Check RHS first (Use)
                self.check_expr(value)?;

                // Revive LHS (Define)
                // Get the unique ID for this target
                let id = target_id.expect("Resolver should have caught this");

                // Get the type from the global type table (populated by inference or decls)
                let ty = tcx.node_types.get(&id).cloned().unwrap_or(Type::Int);

                // Mark as alive in current dataflow scope
                self.scope.insert(id, (true, ty));

                // Store the name so we can print "Variable 'x' is moved" later
                self.id_to_name.insert(id, target.clone());
                Ok(())
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                self.check_expr(cond)?;

                let start_scope = self.scope.clone();

                // Then Branch
                for s in then_block {
                    self.check_stmt(s, tcx)?;
                }

                let then_scope = self.scope.clone();

                // Else Branch
                self.scope = start_scope.clone();
                for s in else_block {
                    self.check_stmt(s, tcx)?;
                }

                let else_scope = self.scope.clone();

                // Merge
                self.scope = self.merge_scopes(then_scope, else_scope);
                Ok(())
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                self.check_expr(cond)?;
                self.check_expr(invariant)?;

                // Snapshot scope before loop
                let start_scope = self.scope.clone();

                // Check body
                for s in body {
                    self.check_stmt(s, tcx)?;
                }

                // Verify Loop Safety (No moves of outer variables)
                // We check: Did any variable that was alive at start become dead?
                for (name_id, (was_alive, _)) in &start_scope {
                    if *was_alive {
                        let (is_alive_after, _) = self.scope.get(name_id).unwrap();
                        if !is_alive_after {
                            let var_name = tcx
                                .resolutions
                                .get(name_id)
                                .map(|def| def.name.clone())
                                .unwrap_or_else(|| format!("var_{}", name_id.0)); // Fallback

                            return Err(Diagnostic {
                                error: CheckError::UseAfterMove { var: var_name },
                                span: stmt.span,
                            });
                        }
                    }
                }

                // Reset Scope
                // After the loop, the state is effectively the same as start
                // (because we forbade moves), but variables defined INSIDE the loop die.
                self.scope = start_scope;

                Ok(())
            }
            Stmt::ArrayUpdate {
                target,
                target_id,
                index,
                value,
            } => {
                //  Check the Index expression (Read)
                self.check_expr(index)?;

                // 2. Check the Value expression (Read/Move)
                self.check_expr(value)?;

                let id = target_id.expect("Resolver should have assigned an ID to array target");

                // 3. Verify the Array itself is Valid
                if let Some((is_alive, ty)) = self.scope.get(&id) {
                    // Rule: Katon cannot modify a moved array
                    if !is_alive {
                        return Err(Diagnostic {
                            error: CheckError::AssignToMoved {
                                var: target.clone(),
                            },
                            span: stmt.span,
                        });
                    }

                    // Rule: Must actually be an Array type
                    if !matches!(ty, Type::Array(_)) {
                        return Err(Diagnostic {
                            error: CheckError::InvalidIndex {
                                base_ty: ty.clone(),
                            },
                            span: stmt.span,
                        });
                    }
                } else {
                    return Err(Diagnostic {
                        error: CheckError::UndefinedVariable {
                            var: target.clone(),
                        },
                        span: stmt.span,
                    });
                }

                Ok(())
            }
        }
    }

    fn check_expr(&mut self, expr: &SExpr) -> Result<(), Diagnostic> {
        match &expr.node {
            Expr::Var(name, node_id) => {
                let id = node_id.expect("Resolver should have assigned an ID");

                if let Some((is_alive, ty)) = self.scope.get(&id).cloned() {
                    if !is_alive {
                        return Err(Diagnostic {
                            error: CheckError::UseAfterMove { var: name.clone() },
                            span: expr.span,
                        });
                    }

                    // If it's not a Copy type (like an Array), "kill" it (mark as moved)
                    if !self.is_copy(&ty) {
                        self.scope.insert(id, (false, ty));
                    }

                    Ok(())
                } else {
                    Err(Diagnostic {
                        error: CheckError::UndefinedVariable { var: name.clone() },
                        span: expr.span,
                    })
                }
            }
            Expr::Cast(_, inner) => self.check_expr(inner),
            Expr::Binary(lhs, Op::Index, rhs) => {
                // 1. Check the Index (rhs)
                self.check_expr(rhs)?;

                // 2. Check the Array (lhs) carefully
                // If lhs is a variable, we peek at it without killing it
                match &lhs.node {
                    Expr::Var(name, node_id) => {
                        let id = node_id.expect("Resolver missing ID for array");

                        match self.scope.get(&id) {
                            Some((is_alive, _ty)) => {
                                if !is_alive {
                                    return Err(Diagnostic {
                                        error: CheckError::UseAfterMove { var: name.clone() },
                                        span: lhs.span,
                                    });
                                }
                                // DO NOT kill — indexing is a borrow
                                Ok(())
                            }
                            None => Err(Diagnostic {
                                error: CheckError::UndefinedVariable { var: name.clone() },
                                span: lhs.span,
                            }),
                        }
                    }
                    // If lhs is complex (e.g. arr_factory()[0]), process recursively
                    _ => self.check_expr(lhs),
                }
            }
            Expr::Binary(l, _, r) => {
                // Order matters! Left is evaluated/moved first.
                self.check_expr(l)?;
                self.check_expr(r)
            }
            Expr::Old(name, node_id) => {
                let id = node_id.expect("Resolver should have assigned an ID to old()");

                // old(x) usually borrows, so we might check existence without killing?
                // For safety, let's treat it as a read
                if self.scope.contains_key(&id) {
                    Ok(())
                } else {
                    Err(Diagnostic {
                        error: CheckError::UndefinedVariable { var: name.clone() },
                        span: expr.span,
                    })
                }
            }
            _ => Ok(()),
        }
    }

    fn merge_scopes(
        &self,
        s1: HashMap<NodeId, (bool, Type)>,
        s2: HashMap<NodeId, (bool, Type)>,
    ) -> HashMap<NodeId, (bool, Type)> {
        let mut result = HashMap::new();

        // We iterate over the union of keys, but practically iterating s1 is often enough
        // if we assume new variables declared inside blocks die at end of block.
        // But to be safe, let's look at s1.
        for (key, (alive1, ty1)) in s1 {
            if let Some((alive2, _)) = s2.get(&key) {
                // Alive only if alive in BOTH branches
                result.insert(key, (alive1 && *alive2, ty1));
            }
            // If missing in s2, it was defined in s1 block -> Drops out of scope (Dead)
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{Op, Type},
        errors::Spanned,
    };

    use super::*;

    fn var(name: &str) -> SExpr {
        Spanned::dummy(Expr::Var(name.to_string(), Some(NodeId(0))))
    }

    fn int(n: i64) -> SExpr {
        Spanned::dummy(Expr::IntLit(n))
    }

    fn bool_lit(b: bool) -> SExpr {
        Spanned::dummy(Expr::BoolLit(b))
    }

    fn bin(l: SExpr, op: Op, r: SExpr) -> SExpr {
        Spanned::dummy(Expr::Binary(Box::new(l), op, Box::new(r)))
    }

    #[test]
    fn test_borrow_checker_moves() {
        // SCENARIO:
        //
        // func test(x int) {
        //    if true {
        //       let y = x; // x is COPIED here (not moved)
        //    } else {
        //       // x alive here
        //    }
        //
        //    let z = x; // OK: x is still alive because Int is Copy
        // }

        let mut bc = BorrowChecker::new();
        let mut tcx = TyCtx::new();

        // Define the ID for 'x' and register it in the context
        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Int);

        let func = FnDecl {
            name: "test".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Spanned::dummy(Stmt::If {
                    cond: bool_lit(true),
                    then_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "y".to_string(),
                        target_id: Some(NodeId(1)),
                        value: var("x"),
                    })],
                    else_block: vec![],
                }),
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(NodeId(2)),
                    value: var("x"),
                }),
            ],
        };

        let result = bc.check_fn(&func, &tcx);
        assert!(result.is_ok(), "Int should be Copy, so x remains alive");
    }

    #[test]
    fn test_copy_semantics_for_int_and_nat() {
        // SCENARIO:
        //
        // func test(x int, y nat) {
        //      z = x + x;
        //      w = y * y;
        // }
        //
        // This fails if Borrow Checker treats Int/Nat as "Move" (Affine)

        let mut bc = BorrowChecker::new();
        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Int);

        let y_id = NodeId(1);
        tcx.define_local(y_id, "y", Type::Nat);

        let func = FnDecl {
            name: "math_test".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int), (y_id, Type::Nat)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                // 1. Test Int Copy: z = x + x
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(NodeId(1)),
                    value: bin(var("x"), Op::Add, var("x")),
                }),
                // 2. Test Nat Copy: w = y * y
                Spanned::dummy(Stmt::Assign {
                    target: "w".to_string(),
                    target_id: Some(NodeId(2)),
                    value: bin(var("y"), Op::Mul, var("y")),
                }),
            ],
        };

        let result = bc.check_fn(&func, &tcx);

        // Should pass
        assert!(result.is_ok(), "Int and Nat should be Copy types!")
    }

    #[test]
    fn test_scope_leak_if_block() {
        // SCENARIO:
        //
        // func fail(x int) {
        //    if x > 0 {
        //       y = 10
        //    }
        //
        //    z = y  <-- ERROR: 'y' is not in scope here
        // }

        let mut bc = BorrowChecker::new();
        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        tcx.define_local(x_id, "x", Type::Int);

        let func = FnDecl {
            name: "scope_leak".to_string(),
            param_names: vec!["x".to_string()],
            params: vec![(x_id, Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Spanned::dummy(Stmt::If {
                    cond: bin(var("x"), Op::Gt, int(0)),
                    then_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "y".to_string(),
                        target_id: Some(NodeId(1)),
                        value: int(10),
                    })],
                    else_block: vec![],
                }),
                // The illegal access
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(NodeId(2)),
                    value: var("y"),
                }),
            ],
        };

        let result = bc.check_fn(&func, &tcx);
        assert!(result.is_err());

        let err = result.unwrap_err();
        assert_eq!(
            err.error,
            CheckError::UndefinedVariable {
                var: "y".to_string()
            }
        );
    }

    #[test]
    fn test_merge_scope_correctness() {
        // SCENARIO:
        // func merge(cond int) {
        //    if cond > 0 {
        //       y = 1
        //    } else {
        //       y = 2
        //    }
        //
        //    z = y  <-- OK: 'y' is defined in BOTH branches
        // }

        let mut bc = BorrowChecker::new();
        let cond_id = NodeId(0);
        let y_id = NodeId(1); // Same ID for 'y' in both branches
        let z_id = NodeId(2);

        let mut tcx = TyCtx::new();
        // We must tell tcx about these IDs so the checker can find their types
        tcx.define_local(cond_id, "cond", Type::Int);
        tcx.define_local(y_id, "y", Type::Int);
        tcx.define_local(z_id, "z", Type::Int);

        let tcx = TyCtx {
            resolutions: HashMap::new(),
            node_types: HashMap::new(),
        };

        let func = FnDecl {
            name: "merge_valid".to_string(),
            param_names: vec!["cond".to_string()],
            params: vec![(cond_id, Type::Int)],
            requires: vec![],
            ensures: vec![],
            body: vec![
                Spanned::dummy(Stmt::If {
                    cond: bin(var("cond"), Op::Gt, int(0)),
                    then_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "y".to_string(),
                        target_id: Some(y_id),
                        value: int(1),
                    })],
                    else_block: vec![Spanned::dummy(Stmt::Assign {
                        target: "y".to_string(),
                        target_id: Some(y_id),
                        value: int(2),
                    })],
                }),
                // Should succeed because 'y' exists in both paths
                Spanned::dummy(Stmt::Assign {
                    target: "z".to_string(),
                    target_id: Some(z_id),
                    value: var("y"),
                }),
            ],
        };

        let result = bc.check_fn(&func, &tcx);
        assert!(result.is_ok())
    }

    #[test]
    fn test_undefined_variable() {
        // SCENARIO
        // z = unknown_var

        let mut bc = BorrowChecker::new();

        let tcx = TyCtx {
            resolutions: HashMap::new(),
            node_types: HashMap::new(),
        };

        let func = FnDecl {
            name: "bad_var".to_string(),
            param_names: vec![],
            params: vec![], // No params
            requires: vec![],
            ensures: vec![],
            body: vec![Spanned::dummy(Stmt::Assign {
                target: "z".to_string(),
                target_id: Some(NodeId(1)),
                value: var("unknown_var"),
            })],
        };

        let result = bc.check_fn(&func, &tcx);
        assert!(result.is_err());

        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("Variable 'unknown_var' undefined"));
    }
}
