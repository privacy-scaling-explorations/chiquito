use chiquito::{
    ast::{ToExpr, ToField},
    dsl::circuit,
};
use halo2_proofs::halo2curves::bn256::Fr;

fn main() {
    circuit::<Fr, Vec<i32>, i32, _>("a circuit", |ctx| {
        let a = ctx.forward("a");
        let b = ctx.forward("b");
        let c = ctx.forward("c");

        let s1 = ctx.step_type("s1", |ctx| {
            let d = ctx.signal("d");
            let f = ctx.signal("f");

            ctx.cond("annotation", 0.into());
            ctx.transition("annotation", a.expr() + 1);

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
            // ...
            let v: i32 = 1;
            ctx.add(&s2, v);
            ctx.add(&s1, v);
        });
    });
}
