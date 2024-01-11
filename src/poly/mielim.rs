use std::{collections::HashMap, fmt::Debug, hash::Hash};

use super::{ConstrDecomp, Expr, SignalFactory};
use crate::field::Field;

pub fn mi_elimination<F: Field, V: Clone + Eq + PartialEq + Hash + Debug, SF: SignalFactory<V>>(
    ctx: &mut ConstrDecomp<F, V>,
    constr: Expr<F, V>,
    signal_factory: &mut SF,
) -> Expr<F, V> {
    use Expr::*;

    match constr {
        Expr::Const(_) => constr,
        Expr::Sum(ses) => Expr::Sum(
            ses.into_iter()
                .map(|se| mi_elimination(ctx, se, signal_factory))
                .collect(),
        ),
        Expr::Mul(ses) => Expr::Mul(
            ses.into_iter()
                .map(|se| mi_elimination(ctx, se, signal_factory))
                .collect(),
        ),
        Expr::Neg(se) => Expr::Neg(Box::new(mi_elimination(ctx, *se, signal_factory))),
        Expr::Pow(se, exp) => Expr::Pow(Box::new(mi_elimination(ctx, *se, signal_factory)), exp),
        Expr::Query(_) => constr,
        Expr::Halo2Expr(_) => constr,
        Expr::MI(se) => {
            let se_elim = mi_elimination(ctx, *se.clone(), signal_factory);

            let virtual_mi = signal_factory.create("virtual_inv");
            let constr_inv = Query(virtual_mi.clone());

            ctx.auto_signals.insert(virtual_mi.clone(), MI(se));

            let virtual_constr =
                se_elim.clone() * (Const(F::ONE) - (se_elim.clone() * Query(virtual_mi)));

            ctx.constrs.push(virtual_constr);
            constr_inv
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

        let constr: Expr<Fr, _> = MI(Box::new(Query(a)));
        let mut ctx = ConstrDecomp::new();
        let result = mi_elimination(&mut ctx, constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "v1");
        assert_eq!(
            format!("{:#?}", ctx.constrs[0]),
            "(a * (0x1 + (-(a * v1))))"
        );
        assert_eq!(ctx.constrs.len(), 1);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi(a)"));
        assert_eq!(ctx.auto_signals.len(), 1);

        let constr = a * MI(Box::new(b + c));
        let mut ctx = ConstrDecomp::new();
        let result = mi_elimination(&mut ctx, constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "(a * v1)");
        assert_eq!(
            format!("{:#?}", ctx.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(ctx.constrs.len(), 1);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert_eq!(ctx.auto_signals.len(), 1);

        let constr = c + MI(Box::new(a * MI(Box::new(b + c))));
        let mut ctx = ConstrDecomp::new();
        let result = mi_elimination(&mut ctx, constr.clone(), &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "(c + v2)");
        assert_eq!(
            format!("{:#?}", ctx.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(
            format!("{:#?}", ctx.constrs[1]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(ctx.constrs.len(), 2);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert_eq!(ctx.auto_signals.len(), 2);

        let constr = constr * (f + MI(Box::new(d * MI(Box::new(e + f)))));
        let mut ctx = ConstrDecomp::new();
        let result = mi_elimination(&mut ctx, constr, &mut TestSignalFactory::default());

        assert_eq!(format!("{:#?}", result), "((c + v2) * (f + v4))");
        assert_eq!(
            format!("{:#?}", ctx.constrs[0]),
            "((b + c) * (0x1 + (-((b + c) * v1))))"
        );
        assert_eq!(
            format!("{:#?}", ctx.constrs[1]),
            "(a * v1 * (0x1 + (-(a * v1 * v2))))"
        );
        assert_eq!(
            format!("{:#?}", ctx.constrs[2]),
            "((e + f) * (0x1 + (-((e + f) * v3))))"
        );
        assert_eq!(
            format!("{:#?}", ctx.constrs[3]),
            "(d * v3 * (0x1 + (-(d * v3 * v4))))"
        );
        assert_eq!(ctx.constrs.len(), 4);
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v1: mi((b + c))"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v2: mi((a * mi((b + c))))"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v3: mi((e + f))"));
        assert!(ctx
            .auto_signals
            .iter()
            .any(|(s, expr)| format!("{:#?}: {:#?}", s, expr) == "v4: mi((d * mi((e + f))))"));
        assert_eq!(ctx.auto_signals.len(), 4);
    }
}
