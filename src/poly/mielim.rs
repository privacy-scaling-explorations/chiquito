use std::{fmt::Debug, hash::Hash};

use super::{ConstrDecomp, Expr, SignalFactory};
use crate::field::Field;

/// This function eliminates MI operators from the PI expression, by creating new signals that are
/// constraint to the MI sub-expressions.
pub fn mi_elimination<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    constr: Expr<F, V>,
    signal_factory: &mut SF,
) -> ConstrDecomp<F, V> {
    use Expr::*;

    match constr {
        Expr::Const(_) => ConstrDecomp::from(constr),
        Expr::Sum(ses) => {
            let ses_elim: Vec<_> = ses
                .iter()
                .map(|se| mi_elimination(se.clone(), signal_factory))
                .collect();

            let root_expr = Expr::Sum(ses_elim.iter().map(|r| r.root_constr.clone()).collect());

            ConstrDecomp::merge(root_expr, ses_elim)
        }
        Expr::Mul(ses) => {
            let ses_elim: Vec<_> = ses
                .iter()
                .map(|se| mi_elimination(se.clone(), signal_factory))
                .collect();

            let root_expr = Expr::Mul(ses_elim.iter().map(|r| r.root_constr.clone()).collect());

            ConstrDecomp::merge(root_expr, ses_elim)
        }
        Expr::Neg(se) => {
            let se_elim = mi_elimination(*se, signal_factory);

            let root_expr = Expr::Neg(Box::new(se_elim.root_constr.clone()));

            ConstrDecomp::merge(root_expr, vec![se_elim])
        }
        Expr::Pow(se, exp) => {
            let se_elim = mi_elimination(*se, signal_factory);

            let root_expr = Expr::Pow(Box::new(se_elim.root_constr.clone()), exp);

            ConstrDecomp::merge(root_expr, vec![se_elim])
        }
        Expr::Query(_) => ConstrDecomp::from(constr),
        Expr::Halo2Expr(_) => ConstrDecomp::from(constr),
        Expr::MI(se) => {
            let se_elim = mi_elimination(*se.clone(), signal_factory);

            let virtual_mi = signal_factory.create("virtual_inv");
            let root_expr = Query(virtual_mi.clone());

            let mut result = ConstrDecomp::from(root_expr);
            result.auto_signals.insert(virtual_mi.clone(), MI(se));

            let virtual_constr = se_elim.root_constr.clone()
                * (Const(F::ONE) - (se_elim.root_constr.clone() * Query(virtual_mi)));

            result.constrs.push(virtual_constr);

            result.expand(vec![se_elim]);

            result
        }
    }
}

#[cfg(test)]
mod test {
    use halo2curves::bn256::Fr;

    use crate::{
        poly::{ConstrDecomp, Expr},
        sbpir::{query::Queriable, InternalSignal},
    };

    use super::{mi_elimination, SignalFactory};

    #[derive(Default)]
    struct TestSignalFactory {
        counter: u32,
    }

    impl SignalFactory<Queriable<Fr>> for TestSignalFactory {
        fn create<S: Into<String>>(&mut self, _annotation: S) -> Queriable<Fr> {
            self.counter += 1;

            Queriable::Internal(InternalSignal::new(format!("v{}", self.counter)))
        }
    }

    #[test]
    fn test_mi_elimination() {
        use Expr::*;

        let a: Queriable<Fr> = Queriable::Internal(InternalSignal::new("a"));
        let b: Queriable<Fr> = Queriable::Internal(InternalSignal::new("b"));
        let c: Queriable<Fr> = Queriable::Internal(InternalSignal::new("c"));
        let d: Queriable<Fr> = Queriable::Internal(InternalSignal::new("d"));
        let e: Queriable<Fr> = Queriable::Internal(InternalSignal::new("e"));
        let f: Queriable<Fr> = Queriable::Internal(InternalSignal::new("f"));

        let result: ConstrDecomp<Fr, Queriable<Fr>> =
            mi_elimination(MI(Box::new(Query(a))), &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result.root_constr), "v1");
        assert_eq!(
            format!("{:#?}", result.constrs[0]),
            "(a * (0x1 + (-(a * v1))))"
        );
        assert_eq!(result.constrs.len(), 1);
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi(a)"));
        assert_eq!(result.auto_signals.len(), 1);

        let constr = a * MI(Box::new(b + c));
        let result: ConstrDecomp<Fr, Queriable<Fr>> =
            mi_elimination(constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result.root_constr), "(a * v1)");
        assert_eq!(
            format!("{:#?}", result.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(result.constrs.len(), 1);
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert_eq!(result.auto_signals.len(), 1);

        let constr = c + MI(Box::new(a * MI(Box::new(b + c))));
        let result: ConstrDecomp<Fr, Queriable<Fr>> =
            mi_elimination(constr.clone(), &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result.root_constr), "(c + v2)");
        assert_eq!(
            format!("{:#?}", result.constrs[0]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(
            format!("{:#?}", result.constrs[1]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(result.constrs.len(), 2);
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert_eq!(result.auto_signals.len(), 2);

        let constr = constr * (f + MI(Box::new(d * MI(Box::new(e + f)))));
        let result: ConstrDecomp<Fr, Queriable<Fr>> =
            mi_elimination(constr, &mut TestSignalFactory::default());

        assert_eq!(
            format!("{:#?}", result.root_constr),
            "((c + v2) * (f + v4))"
        );
        assert_eq!(
            format!("{:#?}", result.constrs[0]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(
            format!("{:#?}", result.constrs[1]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(
            format!("{:#?}", result.constrs[2]),
            "(d * v3 * (0x1 + (-(d * v3 * v4))))"
        );
        assert_eq!(
            format!("{:#?}", result.constrs[3]),
            "((e + f) * (0x1 + (-((e + f) * v3))))"
        );
        assert_eq!(result.constrs.len(), 4);
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: mi((e + f))"));
        assert!(result
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: mi((d * mi((e + f))))"));
        assert_eq!(result.auto_signals.len(), 4);
    }
}
