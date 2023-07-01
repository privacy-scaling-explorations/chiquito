use chiquito::{
    ast::{ToExpr, ToField},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::{cb::lookup, circuit},
};
use halo2_proofs::halo2curves::bn256::Fr;

fn main() {
    let sc = circuit::<Fr, Vec<i32>, i32, _>("a circuit", |ctx| {
        let a = ctx.forward("a");
        let b = ctx.forward("b");
        let c = ctx.forward("c");

        let s1 = ctx.step_type("s1");
        let s1_wg = ctx.step_type_def(s1, |ctx| {
            let d = ctx.internal("d");
            let f = ctx.internal("f");

            ctx.setup(move |ctx| {
                ctx.constr((a + b) * (c - 1));
                ctx.constr(1.expr() + (a + b) * (c - 1));
                ctx.transition(a + 1);

                ctx.add_lookup(lookup().add(a, b).enable(d).add(d + a, f * c));
            });

            ctx.wg(move |ctx, _| {
                ctx.assign(a, 13.field());
                ctx.assign(b, 13.field());
                ctx.assign(c, 13.field());

                ctx.assign(d, 1.field());
                ctx.assign(f, 2.field());
            })
        });

        let s2 = ctx.step_type("s2");
        let s2_wg = ctx.step_type_def(s2, |ctx| {
            // ...

            ctx.wg(move |ctx, _| {
                ctx.assign(a, 13.field());
            })
        });

        ctx.trace(move |ctx, _| {
            let v: i32 = 1;
            ctx.add(&s2_wg, v);
            ctx.add(&s1_wg, v);
        });
    });

    let compiler = Compiler::new(SingleRowCellManager {}, SimpleStepSelectorBuilder {});

    let (circuit, _) = compiler.compile(&sc);

    println!("{:#?}", circuit);
}
