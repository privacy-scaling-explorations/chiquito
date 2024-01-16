use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub lang, "/parser/chiquito.rs");

pub mod ast;
pub mod build;

#[cfg(test)]
mod test {
    use super::lang;

    #[test]
    fn test_parser_expressions() {
        let expr = lang::ExpressionParser::new()
            .parse("22 + 44 + 66 * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "(22 + 44) + (66 * a)");
        assert!(expr.is_arith());

        let expr = lang::ExpressionParser::new()
            .parse("0 == 22 + 44 + 66 * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "0 == ((22 + 44) + (66 * a))");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse("0 == 22 + (44 + 66) * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "0 == (22 + ((44 + 66) * a))");
        assert!(expr.is_logic());
    }

    #[test]
    fn test_parser_statements() {
        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 then { 0 === a; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 then {\n 0 === a;\n}\n]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 then { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 then {\n 0 === a; 1 === b;\n}\n]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 then {\n 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 then {\n 0 === a; 1 === b;\n}\n]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 then {\n 0 === a; 1 === b;} b === 1;")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 then {\n 0 === a; 1 === b;\n}\n, b === 1;]"
        );
        assert_eq!(stmts.len(), 2);
    }

    #[test]
    fn test_parser_tracer() {
        let circuit = "
            tracer atracer(signal a_param) {
                signal a;
                signal b;
    
                step astep(var another_param) {
                    signal c;
    
                    a === b + c;
                }
            }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        println!("{:?}", decls);
    }
}
