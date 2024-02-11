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
        assert_eq!(&format!("{:?}", stmts), "[if 0 == 22 {\n 0 === a;\n}\n]");
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 {\n 0 === a; 1 === b;\n}\n]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 {\n 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 {\n 0 === a; 1 === b;\n}\n]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse("if 0 == 22 {\n 0 === a; 1 === b;} b === 1;")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 {\n 0 === a; 1 === b;\n}\n, b === 1;]"
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

    #[test]
    #[ignore]
    fn test_parser_for_modular_exp() {
        // Modular Exponentiation Example (Low to High Algorithm)
        // https://en.wikipedia.org/wiki/Modular_exponentiation
        // Example for 2^4
        // 2^4 = 2^2 * 2^2 = 4^2 = 16
        // -------------------------
        // | a | e | acc |
        // |---|---|-----|
        // | 2 | 4 | 1   |
        // | 4 | 2 | 1   |
        // | 16| 1 | 1   |
        // | 16| 0 | 16  |
        // -------------------------
        // Example for 3^5
        // 3^5 = 3^2 * 3^2 * 3 = 9^2 * 3 = 81 * 3 = 243
        // -------------------------
        // | a | e | acc |
        // |---|---|-----|
        // | 3 | 5 | 1   |
        // | 9 | 2 | 3   |
        // | 81| 1 | 3   |
        // | 81| 0 | 243 |
        // -------------------------

        let circuit = "
        machine modular_exp(signal a, signal e) (signal acc: field) {
            // a, e and acc are created automatically as shared signals

            state initial {
                acc <== 1;
                -> middle {
                    a', e' <== a, e;
                }
            }

            state middle {
                if e == 0 {
                    -> final {
                        acc' <== acc;
                    }
                } else {
                    if e % 2 == 0 {
                        -> middle {
                            a', e' <== a * a, e / 2;
                        }
                    } else {
                        -> middle {
                            acc', a', e' <== acc * a, a * a, e / 2;
                        }
                    }
                }
            }
        })
        ";

        let decls = lang::TLDeclsParser::new().parse(circuit).unwrap();

        println!("{:?}", decls);
    }
}
