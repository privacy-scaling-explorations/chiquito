use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub lang, "/parser/chiquito.rs");

pub mod ast;
pub mod build;

#[cfg(test)]
mod test {
    use crate::parser::ast::debug_sym_factory::DebugSymRefFactory;

    use super::lang;

    #[test]
    fn test_parser_expressions() {
        let debug_sym_ref_factory = DebugSymRefFactory::new("", "");
        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "22 + 44 + 66 * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "(22 + 44) + (66 * a)");
        assert!(expr.is_arith());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "0 == 22 + 44 + 66 * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "0 == ((22 + 44) + (66 * a))");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "0 == 22 + (44 + 66) * a")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "0 == (22 + ((44 + 66) * a))");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "a == 12 && b == 22 + 44 + 66 * a")
            .unwrap();
        assert_eq!(
            &format!("{:?}", expr),
            "(a == 12) && (b == ((22 + 44) + (66 * a)))"
        );
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "true || false && a == 12")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "true || (false && (a == 12))");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "12 * a**2 / 3 < 12 << 2")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "((12 * (a ** 2)) / 3) < (12 << 2)");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "a << 2 & b")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "(a << 2) & b");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "a << 2 & ~b | c")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "((a << 2) & (~b)) | c");
        assert!(expr.is_logic());

        let expr = lang::ExpressionParser::new()
            .parse(&debug_sym_ref_factory, "a << 2 * -(b + ~c)")
            .unwrap();
        assert_eq!(&format!("{:?}", expr), "a << (2 * (-(b + (~c))))");
        assert!(expr.is_arith());
    }

    #[test]
    fn test_parser_statements() {
        let debug_sym_ref_factory = DebugSymRefFactory::new("", "");
        let stmts = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "if 0 == 22 { 0 === a; }")
            .unwrap();
        assert_eq!(&format!("{:?}", stmts), "[if 0 == 22 { assert 0 == a; }]");
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "if 0 == 22 { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "if 0 == 22 { 0 === a; 1 === b; }")
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }]"
        );
        assert_eq!(stmts.len(), 1);

        let stmts = lang::StatementsParser::new()
            .parse(
                &debug_sym_ref_factory,
                "if 0 == 22 { 0 === a; 1 === b;} b === 1;",
            )
            .unwrap();
        assert_eq!(
            &format!("{:?}", stmts),
            "[if 0 == 22 { assert 0 == a; assert 1 == b; }, assert b == 1;]"
        );
        assert_eq!(stmts.len(), 2);
    }

    #[test]
    fn test_parser_declarations() {
        let debug_sym_ref_factory = DebugSymRefFactory::new("", "");
        let signal_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "signal a: field, b, c;")
            .unwrap();
        assert_eq!(format!("{:?}", signal_decl), r#"[signal a, b, c;]"#);

        let typed_signal_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "signal a: field;")
            .unwrap();
        assert_eq!(format!("{:?}", typed_signal_decl), r#"[signal a;]"#);

        let var_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "var a: field, b, c;")
            .unwrap();
        assert_eq!(format!("{:?}", var_decl), r#"[var a, b, c;]"#);

        let signal_array_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "signal a[7];")
            .unwrap();
        assert_eq!(format!("{:?}", signal_array_decl), r#"[signal a[7];]"#);

        let signal_typed_array_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "signal a: field[7];")
            .unwrap();
        assert_eq!(
            format!("{:?}", signal_typed_array_decl),
            r#"[signal a[7];]"#
        );

        let var_array_decl = lang::StatementsParser::new()
            .parse(&debug_sym_ref_factory, "var a[7];")
            .unwrap();
        assert_eq!(format!("{:?}", var_array_decl), r#"[var a[7];]"#);
    }

    #[test]
    fn test_parser_tracer() {
        let circuit = "
        machine fibo(signal n) (signal b: field) {
            // n and be are created automatically as shared
            // signals
            signal a: field, i;

            // there is always a state called initial
            // input signals get bound to the signal
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
            // Output signals get automatically bound to the signals
            // with the same name in the final step (last instance).
            // This state can be implicit if there are no constraints in it.
           }
        ";

        let debug_sym_ref_factory = DebugSymRefFactory::new("", circuit);
        let decls = lang::TLDeclsParser::new()
            .parse(&debug_sym_ref_factory, circuit)
            .unwrap();

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

        let circuit = r"
        machine modular_exp(signal a, signal e) (signal acc: field) {
            // a, e and acc are created automatically as shared signals

            state initial {
                acc <== 1;
                -> middle {
                    acc', a', e' <== acc, a, e;
                }
            }

            state middle {
                signal new_acc;
                signal rem;
                signal div;


                rem <-- e % 2;
                div <-- e / 2;

                e === div * 2 + rem;

                if (rem == 0) {
                    new_acc <== acc;
                } else {
                    new_acc <== acc * a;
                }

                if e == 0 {
                    -> final {
                        acc' <== acc;
                    }
                } else {
                    -> middle {
                        acc', a', e' <== new_acc, a * a, div;
                    }
                }
            }
        })
        ";

        let debug_sym_ref_factory = DebugSymRefFactory::new("", circuit);
        let decls = lang::TLDeclsParser::new()
            .parse(&debug_sym_ref_factory, circuit)
            .unwrap();

        println!("{:?}", decls);
    }
}
