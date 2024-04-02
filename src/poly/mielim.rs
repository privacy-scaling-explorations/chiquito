use std::{fmt::Debug, hash::Hash};

use super::{ConstrDecomp, Expr, SignalFactory};
use crate::field::Field;

/// This function eliminates MI operators from the PI expression, by creating new signals that are
/// constraint to the MI sub-expressions.
pub fn mi_elimination<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    constr: Expr<F, V>,
    signal_factory: &mut SF,
) -> (Expr<F, V>, ConstrDecomp<F, V>) {
    let mut decomp = ConstrDecomp::default();
    let expr = mi_elimination_recursive(&mut decomp, constr, signal_factory);

    (expr, decomp)
}

fn mi_elimination_recursive<
    F: Field,
    V: Clone + Eq + PartialEq + Hash + Debug,
    SF: SignalFactory<V>,
>(
    decomp: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    use Expr::*;

    match constr {
        Expr::Const(_) => constr,
        Expr::Sum(ses) => Expr::Sum(
            ses.into_iter()
                .map(|se| mi_elimination_recursive(decomp, se, signal_factory))
                .collect(),
        ),
        Expr::Mul(ses) => Expr::Mul(
            ses.into_iter()
                .map(|se| mi_elimination_recursive(decomp, se, signal_factory))
                .collect(),
        ),
        Expr::Neg(se) => Expr::Neg(Box::new(mi_elimination_recursive(
            decomp,
            *se,
            signal_factory,
        ))),
        Expr::Pow(se, exp) => Expr::Pow(
            Box::new(mi_elimination_recursive(decomp, *se, signal_factory)),
            exp,
        ),
        Expr::Query(_) => constr,
        Expr::Halo2Expr(_) => constr,
        Expr::MI(se) => {
            let se_elim = mi_elimination_recursive(decomp, *se.clone(), signal_factory);

            let virtual_mi = signal_factory.create("virtual_inv");
            let constr_inv = Query(virtual_mi.clone());

            decomp.auto_signals.insert(virtual_mi.clone(), MI(se));

            let virtual_constr = se_elim.clone() * (Const(F::ONE) - (se_elim * Query(virtual_mi)));

            decomp.constrs.push(virtual_constr);
            constr_inv
        }
    }
}

#[cfg(test)]
mod test {
    use halo2_proofs::halo2curves::bn256::Fr;

    use crate::{
        poly::{mielim::mi_elimination, Expr},
        sbpir::{query::Queriable, InternalSignal},
    };

    use super::SignalFactory;

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

        let constr: Expr<Fr, _> = MI(Box::new(Query(a)));
        let (result, decomp) = mi_elimination(constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "v1");
        assert_eq!(
            format!("{:#?}", decomp.constrs[0]),
            "(a * (0x1 + (-(a * v1))))"
        );
        assert_eq!(decomp.constrs.len(), 1);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi(a)"));
        assert_eq!(decomp.auto_signals.len(), 1);

        let constr = a * MI(Box::new(b + c));
        let (result, decomp) = mi_elimination(constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(
            format!("{:#?}", decomp.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(decomp.constrs.len(), 1);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert_eq!(decomp.auto_signals.len(), 1);

        let constr = c + MI(Box::new(a * MI(Box::new(b + c))));
        let (result, decomp) = mi_elimination(constr.clone(), &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "(c + v2)");
        assert_eq!(
            format!("{:#?}", decomp.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(
            format!("{:#?}", decomp.constrs[1]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(decomp.constrs.len(), 2);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert_eq!(decomp.auto_signals.len(), 2);

        let constr = constr * (f + MI(Box::new(d * MI(Box::new(e + f)))));
        let (result, decomp) = mi_elimination(constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "((c + v2) * (f + v4))");
        assert_eq!(
            format!("{:#?}", decomp.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(
            format!("{:#?}", decomp.constrs[1]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(
            format!("{:#?}", decomp.constrs[2]),
            "((e + f) * (0x1 + (-((e + f) * v3))))"
        );
        assert_eq!(
            format!("{:#?}", decomp.constrs[3]),
            "(d * v3 * (0x1 + (-(d * v3 * v4))))"
        );
        assert_eq!(decomp.constrs.len(), 4);
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: mi((e + f))"));
        assert!(decomp
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: mi((d * mi((e + f))))"));
        assert_eq!(decomp.auto_signals.len(), 4);
    }
}
