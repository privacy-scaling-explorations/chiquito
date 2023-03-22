use chiquito::{
    ast::{ToExpr, ToField},
    compiler::{
        cell_manager::SimpleCellManager, step_selector::SimpleStepSelectorBuilder, Compiler,
    },
    dsl::circuit,
};
use halo2_proofs::halo2curves::bn256::Fr;

fn main() {
    let sc = circuit::<Fr, Vec<i32>, i32, _>("a circuit", |ctx| {
        let a = ctx.forward("a");
        let b = ctx.forward("b");
        let c = ctx.forward("c");

        let s1 = ctx.step_type("s1", |ctx| {
            let d = ctx.signal("d");
            let f = ctx.signal("f");

            ctx.constr("annotation", (a + b) * (c - 1.expr()));
            ctx.transition("annotation", a + 1.expr());

            ctx.wg(move |ctx, _| {
                ctx.assign(a, 13.field());
                ctx.assign(b, 13.field());
                ctx.assign(c, 13.field());

                ctx.assign(d, 1.field());
                ctx.assign(f, 2.field());
            });
        });

        let s2 = ctx.step_type("s2", |ctx| {
            // ...

            ctx.wg(move |ctx, _| {
                ctx.assign(a, 13.field());
            })
        });

        ctx.trace(move |ctx, _| {
            let v: i32 = 1;
            s2.add(ctx, v);
            s1.add(ctx, v);
        });
    });

    let compiler = Compiler::new(SimpleCellManager {}, SimpleStepSelectorBuilder {});

    println!("{:#?}", compiler.compile(sc));
}
