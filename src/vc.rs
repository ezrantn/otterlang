use crate::{
    ast::{Expr, FnDecl, NodeId, Op, SExpr, SStmt, Stmt, Type},
    symbol::TyCtx,
};
use std::collections::{HashMap, HashSet};

struct Env {
    global_gen: HashMap<NodeId, usize>,
    current_scope: HashMap<NodeId, usize>,
    var_types: HashMap<NodeId, Type>,
}

impl Env {
    fn new() -> Self {
        Self {
            global_gen: HashMap::new(),
            current_scope: HashMap::new(),
            var_types: HashMap::new(),
        }
    }

    fn get_smt_name(&self, id: &NodeId, tcx: &TyCtx) -> String {
        let ver = self.current_scope.get(id).unwrap_or(&0);
        let name = tcx.get_name(id);
        format!("{}_{}", name, ver)
    }

    fn register_var(&mut self, id: NodeId, ty: Type) {
        self.var_types.insert(id, ty);
    }

    // Check if variable is Nat using ID
    fn is_nat(&self, id: &NodeId) -> bool {
        matches!(self.var_types.get(id), Some(Type::Nat))
    }

    // For old(x), we always want the 0th version
    fn get_old(&self, id: &NodeId, tcx: &TyCtx) -> String {
        let name = tcx.get_name(id);
        format!("{}_0", name)
    }

    // Create a new SSA version (e.g., for x = ...)
    fn new_version(&mut self, id: NodeId, tcx: &TyCtx) -> String {
        // Increment global generation
        let next_ver = self.global_gen.entry(id).or_insert(0);
        *next_ver += 1;
        let ver = *next_ver;

        // Update current scope to point to this new version
        self.current_scope.insert(id, ver);

        let name = tcx.get_name(&id);
        format!("{}_{}", name, ver)
    }
}

fn expr_to_smt(expr: &SExpr, env: &Env, tcx: &TyCtx) -> String {
    match &expr.node {
        Expr::IntLit(n) => n.to_string(),
        Expr::BoolLit(b) => b.to_string(),
        Expr::Var(_name, node_id) => {
            let id = node_id.expect("VC Gen requires resolved IDs");
            env.get_smt_name(&id, tcx)
        }
        Expr::Old(_name, node_id) => {
            let id = node_id.expect("VC Gen requires resolved IDs for old()");
            env.get_old(&id, tcx)
        }
        Expr::Cast(_, inner) => expr_to_smt(inner, env, tcx), // The safety check happens at the assignment level
        Expr::Binary(lhs, op, rhs) => {
            let l = expr_to_smt(lhs, env, tcx);
            let r = expr_to_smt(rhs, env, tcx);
            let op_str = match op {
                Op::Add => "+",
                Op::Sub => "-",
                Op::Eq => "=",
                Op::Gt => ">",
                Op::Lt => "<",
                Op::Gte => ">=",
                Op::Lte => "<=",
                Op::Mul => "*",
                Op::Neq => "distinct",
                Op::Div => "div",
                Op::Index => "select",
            };
            format!("({} {} {})", op_str, l, r)
        }
    }
}

fn get_modified_vars(stmts: &[SStmt]) -> HashSet<NodeId> {
    let mut modified = HashSet::new();
    for stmt in stmts {
        match &stmt.node {
            Stmt::Assign { target_id, .. } => {
                if let Some(id) = target_id {
                    modified.insert(*id);
                }
            }
            Stmt::ArrayUpdate { target_id, .. } => {
                if let Some(id) = target_id {
                    modified.insert(*id);
                }
            }
            Stmt::If {
                then_block,
                else_block,
                ..
            } => {
                modified.extend(get_modified_vars(then_block));
                modified.extend(get_modified_vars(else_block));
            }
            Stmt::While { body, .. } => {
                modified.extend(get_modified_vars(body));
            }
        }
    }
    modified
}

fn type_to_smt(ty: &Type) -> String {
    match ty {
        Type::Int | Type::Nat => "Int".to_string(),
        Type::Array(inner) => format!("(Array Int {})", type_to_smt(inner)),
    }
}

fn process_block(stmts: &[SStmt], env: &mut Env, smt: &mut String, tcx: &TyCtx) {
    for stmt in stmts {
        match &stmt.node {
            Stmt::Assign {
                target,
                target_id,
                value,
            } => {
                let val_smt = expr_to_smt(value, env, tcx);
                let id = target_id.expect("VC Gen: Missing ID for assignment");

                // If target is Nat, we MUST prove value >= 0 before proceeding
                if env.is_nat(&id) {
                    smt.push_str(&format!("; SAFETY CHECK: {} must be Nat\n", target));
                    smt.push_str("(push)\n");
                    // We assert the negation: "Is it possible for val to be < 0?"
                    smt.push_str(&format!("(assert (< {} 0))\n", val_smt));
                    smt.push_str("(check-sat)\n");
                    // If SAT -> Verification Error: "Assignment violates nat type"
                    smt.push_str("(pop)\n");
                }

                let new_target_name = env.new_version(id, tcx);
                let ty_smt = type_to_smt(env.var_types.get(&id).unwrap_or(&Type::Int));

                smt.push_str(&format!("(declare-const {} {})\n", new_target_name, ty_smt));
                smt.push_str(&format!("(assert (= {} {}))\n", new_target_name, val_smt));

                // Add the type constraint to the main path too, so future logic knows it's positive
                if env.is_nat(&id) {
                    smt.push_str(&format!("(assert (>= {} 0))\n", new_target_name));
                }
            }
            Stmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let cond_smt = expr_to_smt(cond, env, tcx);

                // 1. Save Scope (NOT global counters)
                let start_scope = env.current_scope.clone();

                // 2. Process THEN
                process_block(then_block, env, smt, tcx);
                let then_scope = env.current_scope.clone();

                // 3. Restore Scope & Process ELSE
                env.current_scope = start_scope.clone(); // Reset local scope
                process_block(else_block, env, smt, tcx);
                let else_scope = env.current_scope.clone();

                // Merging logic using Node IDs
                let mut all_vars: HashSet<NodeId> = start_scope.keys().cloned().collect();
                all_vars.extend(then_scope.keys());
                all_vars.extend(else_scope.keys());

                for var_id in all_vars {
                    let v_start = *start_scope.get(&var_id).unwrap_or(&0);
                    let v_then = *then_scope.get(&var_id).unwrap_or(&v_start);
                    let v_else = *else_scope.get(&var_id).unwrap_or(&v_start);

                    if v_then != v_start || v_else != v_start {
                        let merged_name = env.new_version(var_id, tcx);
                        let ty_smt = type_to_smt(env.var_types.get(&var_id).unwrap_or(&Type::Int));

                        let then_name = format!("{}_{}", tcx.get_name(&var_id), v_then);
                        let else_name = format!("{}_{}", tcx.get_name(&var_id), v_else);

                        smt.push_str(&format!("(declare-const {} {})\n", merged_name, ty_smt));
                        smt.push_str(&format!(
                            "(assert (= {} (ite {} {} {})))\n",
                            merged_name, cond_smt, then_name, else_name
                        ));
                    }
                }
            }
            Stmt::While {
                cond,
                invariant,
                body,
            } => {
                // Assert Invariant holds on Entry
                // Does the invariant hold BEFORE the loop starts?
                let inv_entry = expr_to_smt(invariant, env, tcx);
                smt.push_str("; CHECK 1: Loop Entry Invariant\n");
                smt.push_str("(push)\n");
                smt.push_str(&format!("(assert (not {}))\n", inv_entry)); // Negate to find bug
                smt.push_str("(check-sat)\n");
                smt.push_str("(pop)\n");

                // We get the NodeIds of anything changed inside the loop
                // Create a new SSA version for the loop's arbitrary iteration
                let modified = get_modified_vars(body);
                for var_id in &modified {
                    let new_ver_name = env.new_version(*var_id, tcx);
                    let ty_smt = type_to_smt(env.var_types.get(var_id).unwrap_or(&Type::Int));

                    smt.push_str(&format!("(declare-const {} {})\n", new_ver_name, ty_smt));
                }

                // Assume Invariant is True at start of an arbitrary iteration
                let inv_havoc = expr_to_smt(invariant, env, tcx);
                smt.push_str(&format!("(assert {})\n", inv_havoc));

                // CHECK: Loop Body Maintenance
                smt.push_str("; CHECK 2: Loop Body Maintenance\n");
                smt.push_str("(push)\n");

                // A. Assume Loop Condition is True
                let cond_havoc = expr_to_smt(cond, env, tcx);
                smt.push_str(&format!("(assert {})\n", cond_havoc));

                // B. Run Body using a temporary Env clone
                // This uses new ID-based Env fields
                let mut body_env = Env {
                    global_gen: env.global_gen.clone(),
                    current_scope: env.current_scope.clone(),
                    var_types: env.var_types.clone(),
                };

                process_block(body, &mut body_env, smt, tcx);

                // C. Verify Invariant still holds after the body runs
                let inv_post = expr_to_smt(invariant, &body_env, tcx);
                smt.push_str(&format!("(assert (not {}))\n", inv_post));
                smt.push_str("(check-sat)\n");
                smt.push_str("(pop)\n");

                // 5. Termination: Continue main path assuming Loop Condition is False
                let cond_exit = expr_to_smt(cond, env, tcx);
                smt.push_str(&format!("(assert (not {}))\n", cond_exit));
            }
            Stmt::ArrayUpdate {
                target,
                target_id,
                index,
                value,
            } => {
                let id = target_id.expect("VC Gen: Missing ID for array update");

                let idx_smt = expr_to_smt(index, env, tcx);
                let val_smt = expr_to_smt(value, env, tcx);

                let current_arr_name = env.get_smt_name(&id, tcx);

                // Bounds checking
                // Note: This assumes that the array type/logic supports a 'length' property or function
                smt.push_str(&format!("; SAFETY CHECK: {} index out of bounds\n", target));
                smt.push_str("(push)\n");
                // We try to prove a bug exists: (index < 0) OR (index >= length)
                // For now, Katon usually assumes arrays are indexed by Nat
                smt.push_str(&format!("(assert (not (and (>= {0} 0))))\n", idx_smt));
                smt.push_str("(check-sat)\n");
                smt.push_str("(pop)\n");

                // Create new array version
                let new_arr_name = env.new_version(id, tcx);
                let ty_smt = type_to_smt(env.var_types.get(&id).expect("Array type missing"));

                // Emit SMT Logic
                // (declare-const a_1 (Array Int Int))
                smt.push_str(&format!("(declare-const {} {})\n", new_arr_name, ty_smt));

                // (assert (= a_1 (store a_0 index value)))
                smt.push_str(&format!(
                    "(assert (= {} (store {} {} {})))\n",
                    new_arr_name, current_arr_name, idx_smt, val_smt
                ));
            }
        }
    }
}

pub fn compile(func: &FnDecl, tcx: &TyCtx) -> String {
    let mut smt = String::from("(set-logic QF_AUFNIA)\n");
    let mut env = Env::new();

    for (id, ty) in &func.params {
        let name = tcx.get_name(id);
        env.register_var(*id, ty.clone());

        let ty_smt = type_to_smt(ty);

        smt.push_str(&format!("(declare-const {}_0 {})\n", name, ty_smt));

        // Track the current version of this ID in the environment
        env.current_scope.insert(*id, 0);

        // Nat constraint: x >= 0
        if let Type::Nat = ty {
            smt.push_str(&format!("(assert (>= {}_0 0))\n", name));
        }
    }

    // Preconditions
    let requires = if func.requires.is_empty() {
        "true".to_string()
    } else {
        format!(
            "(and {})",
            func.requires
                .iter()
                .map(|r| expr_to_smt(r, &env, tcx))
                .collect::<Vec<_>>()
                .join(" ")
        )
    };
    smt.push_str(&format!("; PRECONDITIONS\n(assert {})\n", requires));

    // This generates all the assignment logic, if-merges, and loop havocs
    process_block(&func.body, &mut env, &mut smt, tcx);

    // Postconditions (Ensures)
    // We prove: (Requires && Body) => Ensures
    // SMT way: (Requires && Body && (not Ensures)) is UNSAT
    for ens in &func.ensures {
        let post = expr_to_smt(ens, &env, tcx);
        smt.push_str("\n; CHECK POSTCONDITION\n");
        smt.push_str("(push)\n");
        smt.push_str(&format!("(assert (not {}))\n", post));
        smt.push_str("(check-sat)\n");
        smt.push_str("(pop)\n");
    }

    smt
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::errors::Spanned;
    use crate::runner::verify_with_z3;

    fn var(name: &str, id: u32) -> SExpr {
        Spanned::dummy(Expr::Var(name.to_string(), Some(NodeId(id))))
    }

    fn old(name: &str, id: u32) -> SExpr {
        Spanned::dummy(Expr::Old(name.to_string(), Some(NodeId(id))))
    }

    fn int(n: i64) -> SExpr {
        Spanned::dummy(Expr::IntLit(n))
    }

    fn bin(l: SExpr, op: Op, r: SExpr) -> SExpr {
        Spanned::dummy(Expr::Binary(Box::new(l), op, Box::new(r)))
    }

    #[test]
    fn test_compile_abs_function_with_merge() {
        // LOGIC TO TEST:
        // func abs(x: int) {
        //    let y = x;       <-- y_1 defined here (Start Scope for IF)
        //    if x < 0 {
        //       y = 0 - x;    <-- y_2 (Then Branch)
        //    } else {
        //       y = x;        <-- y_3 (Else Branch)
        //    }
        //    // Merge happens here: y_4 = ite(..., y_2, y_3)
        // }
        // ensures y >= 0

        let mut tcx = TyCtx::new();

        let x_id = NodeId(0);
        let y_id = NodeId(1);

        tcx.define_local(x_id, "x", Type::Int);
        tcx.define_local(y_id, "y", Type::Int);

        let func = FnDecl {
            name: "abs".to_string(),
            params: vec![(x_id, Type::Int)], // x_0 declared automatically
            param_names: vec!["x".to_string()],
            requires: vec![],
            body: vec![
                // 1. Init y = x
                Spanned::dummy(Stmt::Assign {
                    target: "y".to_string(),
                    target_id: Some(y_id),
                    value: var("x", 0),
                }),
                // 2. If x < 0
                Spanned::dummy(Stmt::If {
                    cond: bin(var("x", 0), Op::Lt, int(0)),
                    then_block: vec![
                        // y = 0 - x
                        Spanned::dummy(Stmt::Assign {
                            target: "y".to_string(),
                            target_id: Some(y_id),
                            value: bin(int(0), Op::Sub, var("x", 0)),
                        }),
                    ],
                    else_block: vec![
                        // y = x
                        Spanned::dummy(Stmt::Assign {
                            target: "y".to_string(),
                            target_id: Some(y_id),
                            value: var("x", 0),
                        }),
                    ],
                }),
            ],
            ensures: vec![
                // y >= 0
                bin(var("y", 1), Op::Gte, int(0)),
            ],
        };

        let smt_output = compile(&func, &tcx);

        // 1. Initial State
        assert!(smt_output.contains("(declare-const x_0 Int)"));

        // 2. Initial Assignment (y = x) -> y_1
        assert!(smt_output.contains("(declare-const y_1 Int)"));
        assert!(smt_output.contains("(= y_1 x_0)"));

        // 3. Branches (y_2 and y_3)
        // Inside 'then', y gets a new global version
        assert!(smt_output.contains("(= y_2 (- 0 x_0))"));
        // Inside 'else', y gets the next global version
        assert!(smt_output.contains("(= y_3 x_0)"));

        // 4. THE MERGE (Phi Node)
        // merge_scopes detects y was changed and creates y_4
        assert!(smt_output.contains("(declare-const y_4 Int)"));
        assert!(smt_output.contains("ite (< x_0 0) y_2 y_3"));

        // 5. Post-condition must check the merged version (y_4)
        assert!(smt_output.contains("(not (>= y_4 0))"));
        assert!(smt_output.contains("(check-sat)"));
    }

    #[test]
    fn test_loop_body_verification_fails() {
        // BUGGY CODE:
        // i = 0
        // while i < n invariant i <= n {
        //    i = i - 1; // <--- BUG! This breaks the invariant (i <= n) or termination?
        //               // Actually, if i becomes -1, -1 <= n is still true...
        //               // Let's make a clearer bug:
        //               // Invariant: i >= 0. Body: i = i - 1.
        // }

        let mut tcx = TyCtx::new();

        let n_id = NodeId(0);
        let i_id = NodeId(1);

        tcx.define_local(n_id, "n", Type::Int);
        tcx.define_local(i_id, "i", Type::Int);

        let func = FnDecl {
            name: "buggy_loop".to_string(),
            param_names: vec!["n".to_string()],
            params: vec![(n_id, Type::Int)],
            requires: vec![bin(var("n", 0), Op::Gt, int(0))],
            body: vec![
                Spanned::dummy(Stmt::Assign {
                    target: "i".to_string(),
                    target_id: Some(i_id),
                    value: int(0),
                }),
                Spanned::dummy(Stmt::While {
                    cond: bin(var("i", 1), Op::Lt, var("n", 0)),
                    invariant: bin(var("i", 1), Op::Gte, int(0)), // i must stay positive
                    body: vec![
                        // BUG: Decrementing i makes it negative!
                        Spanned::dummy(Stmt::Assign {
                            target: "i".to_string(),
                            target_id: Some(i_id),
                            value: bin(var("i", 1), Op::Sub, int(1)),
                        }),
                    ],
                }),
            ],
            ensures: vec![],
        };

        let smt = compile(&func, &tcx);
        let result = verify_with_z3(&smt);

        // Z3 will find that if i=0 and we do i = i - 1, then i becomes -1.
        // -1 >= 0 is FALSE, so the invariant is violated.
        assert!(
            result.is_err(),
            "Verification should fail for decreasing invariant"
        );
    }

    #[test]
    fn test_compile_array_update() {
        // SCENARIO:
        // func update(arr []int) {
        //    arr[0] = 99
        //    ensures arr[0] == 99
        //    ensures arr[1] == old(arr)[1] // Frame property
        // }

        let mut tcx = TyCtx::new();
        let arr_id = NodeId(0);

        tcx.define_local(arr_id, "arr", Type::Array(Box::new(Type::Int)));

        let func = FnDecl {
            name: "update".to_string(),
            param_names: vec!["arr".to_string()],
            params: vec![(arr_id, Type::Array(Box::new(Type::Int)))],
            requires: vec![],
            body: vec![Spanned::dummy(Stmt::ArrayUpdate {
                target: "arr".to_string(),
                target_id: Some(arr_id),
                index: int(0),
                value: int(99),
            })],
            ensures: vec![
                // arr[0] == 99
                bin(bin(var("arr", 0), Op::Index, int(0)), Op::Eq, int(99)),
                // arr[1] == old(arr)[1] (Prove we didn't touch index 1)
                bin(
                    bin(var("arr", 0), Op::Index, int(1)),
                    Op::Eq,
                    bin(old("arr", 0), Op::Index, int(1)),
                ),
            ],
        };

        let smt = compile(&func, &tcx);
        assert!(smt.contains("(declare-const arr_0 (Array Int Int))"));
        assert!(smt.contains("(declare-const arr_1 (Array Int Int))"));
        assert!(smt.contains("(= arr_1 (store arr_0 0 99))"));
        assert!(smt.contains("(select arr_1 0)"));
    }
}
