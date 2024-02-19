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
            .parse("if 0 == 22 { 0 === a; }")
            .unwrap();
        assert_eq!(&format!("{:?}", stmts), "[if 0 == 22 { assert 0 == a; }]");
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 { 0 === a; 1 === b;} b === 1;")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }, assert b == 1;]"
        );
        assert_eq!(stmts.len(), 2);
    }

    #[test]
    fn test_parser_tracer() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get binded to the signal
            // in the initial state (first instance)
            state initial {
             signal c;

             i, a, b, c <== 1, 1, 1, 2;

             -> middle {
              a', b', n' <== b, c, n;
             }
            }

            state middle {
             signal c;

             c <== a + b;

             if i + 1 == n {
              -> final {
               i', b', n' <== i + 1, c, n;
              }
             } else {
              -> middle {
               i', a', b', n' <== i + 1, b, c, n;
              }
             }
            }

            // There is always a state called final.
            // Output signals get automatically bindinded to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        assert_eq!(
            format!("{:?}", decls),
            r#"[machine fibo (signal n;) (signal b;) { signal a, i; state initial { signal c; [i, a, b, c] <== [1, 1, 1, 2]; -> middle { [a', b', n'] <== [b, c, n]; } } state middle { signal c; [c] <== [a + b]; if (i + 1) == n { -> final { [i', b', n'] <== [i + 1, c, n]; } } else { -> middle { [i', a', b', n'] <== [i + 1, b, c, n]; } } } }]"#
        );

        println!("{:?}", decls);
    }
}
