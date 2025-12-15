pub mod ast;
pub mod check;
pub mod vc;

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub otter);

fn main() {
    let src = r#"
        func Abs(x) {
            requires x > -100
            
            if x < 0 { 
                x = 0 - x 
            } else { 
                x = x 
            }

            ensures x >= 0
        }
    "#;

    let parser = otter::FnDeclParser::new();
    let parse_result = parser.parse(src);

    match parse_result {
        Ok(func_decl) => {
            println!("Parsed '{}' successfully.", func_decl.name);

            // 3. BORROW CHECK IT
            let mut checker = check::BorrowChecker::new();
            match checker.check_fn(&func_decl) {
                Ok(_) => {
                    println!("Borrow Checker Passed.");

                    let z3_code = vc::compile(&func_decl);
                    println!("\n--- Z3 SMT OUTPUT ---\n");
                    println!("{}", z3_code);
                }

                Err(e) => println!("❌ Borrow Check Failed: {}", e),
            }
        }
        Err(e) => {
            use lalrpop_util::ParseError;

            // Map the error to a simple (start, message) tuple
            // We underscore variables we don't use (like `_expected`) to silence warnings
            let (span, message) = match &e {
                ParseError::InvalidToken { location } => {
                    (*location..*location + 1, "Invalid token found here")
                }
                ParseError::UnrecognizedEof {
                    location,
                    expected: _,
                } => (*location..*location, "Unexpected end of file."),
                ParseError::UnrecognizedToken { token, expected: _ } => {
                    let (start, _, end) = token;
                    (*start..*end, "Unrecognized token")
                }
                ParseError::ExtraToken { token } => {
                    let (start, _, end) = token;
                    (*start..*end, "Extra token found")
                }
                ParseError::User { error: _ } => (0..0, "User error"),
            };

            // Simple error printing using ariadne logic (simplified here for standard output)
            println!("Error: {} at {:?}", message, span);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::otter;
    use super::ast::{Expr, FnDecl, Op, Stmt};

    fn int(i: i64) -> Box<Expr> { Box::new(Expr::IntLit(i)) }
    fn var(s: &str) -> Box<Expr> { Box::new(Expr::Var(s.to_string())) }
    fn bin(l: Box<Expr>, op: Op, r: Box<Expr>) -> Expr { Expr::Binary(l, op, r) }

    #[test]
    fn test_basic_arithmetic() {
        let parser = otter::ExprParser::new();

        let res = parser.parse("1 + 2").unwrap();
        assert_eq!(res, bin(int(1), Op::Add, int(2)));

        let res = parser.parse("x == 1 + 2").unwrap();
        assert_eq!(res, bin(
            var("x"), 
            Op::Eq, 
            Box::new(bin(int(1), Op::Add, int(2)))
        ));
    }

    #[test]
    fn test_arithmetic_associativity() {
        let parser = otter::ExprParser::new();

        // In `Term` grammar we handles +, -, *, / in the same tier
        // This results in Left-Associativity for all of them. 
        // "1 + 2 * 3" parses as "(1 + 2) * 3", NOT "1 + (2 * 3)".
        let res = parser.parse("1 + 2 * 3").unwrap();

        assert_eq!(res, bin(
            Box::new(bin(int(1), Op::Add, int(2))), // (1+2) happens first
            Op::Mul, 
            int(3)
        ));
    }
}