# Chiquito architecture

Chiquito is implemented like most compiler but substituting the lexer and parser by declarative programming in Python or Rust.

![](images/chiquito_arch_concept.jpg)

The front-end uses declarative programming to create an Abstract Syntax Tree (AST) that represent the intention of the developer, directly puts in a data structure all the information from the chiquito ZKP circuit.

The AST already contains the constraints translated to polynomial identities on the signals. In the future we want to do this in the compiler so it can be more efficiently done for different backends and arithmetizations

```
Circuit {
    step_types: {
        281282176211935008643818839171708619274: StepType {
            id: 281282176211935008643818839171708619274,
            signals: [],
            constraints: [],
            transition_constraints: [
                TransitionConstraint {
                    annotation: "b == next(b)",
                    expr: (b + (-next(b))),
                },
                TransitionConstraint {
                    annotation: "n == next(n)",
                    expr: (n + (-next(n))),
                },
            ],
        },
        281282073769920877700029204819473992202: StepType {
            id: 281282073769920877700029204819473992202,
            signals: [
                InternalSignal {
                    id: 281282081534280804097934570461757835786,
                    annotation: "c",
                },
            ],
            constraints: [
                Constraint {
                    annotation: "a == 0x1",
                    expr: (a + (-0x1)),
                },
                Constraint {
                    annotation: "b == 0x1",
                    expr: (b + (-0x1)),
                },
                Constraint {
                    annotation: "(a + b) == c",
                    expr: (a + b + (-c)),
                },
            ],
            transition_constraints: [
                TransitionConstraint {
                    annotation: "b == next(a)",
                    expr: (b + (-next(a))),
                },
                TransitionConstraint {
                    annotation: "c == next(b)",
                    expr: (c + (-next(b))),
                },
                TransitionConstraint {
                    annotation: "n == next(n)",
                    expr: (n + (-next(n))),
                },
            ],
        },
        281282153948821342135539412435905153546: StepType {
            id: 281282153948821342135539412435905153546,
            signals: [
                InternalSignal {
                    id: 281282157751773142820227898400991480330,
                    annotation: "c",
                },
            ],
            constraints: [
                Constraint {
                    annotation: "(a + b) == c",
                    expr: (a + b + (-c)),
                },
            ],
            transition_constraints: [
                TransitionConstraint {
                    annotation: "b == next(a)",
                    expr: (b + (-next(a))),
                },
                TransitionConstraint {
                    annotation: "c == next(b)",
                    expr: (c + (-next(b))),
                },
                TransitionConstraint {
                    annotation: "n == next(n)",
                    expr: (n + (-next(n))),
                },
            ],
        },
    },
    forward_signals: [
        ForwardSignal {
            id: 281282057290463074733046140937402190346,
            phase: 0,
            annotation: "a",
        },
        ForwardSignal {
            id: 281282068699318476787111035882707749386,
            phase: 0,
            annotation: "b",
        },
        ForwardSignal {
            id: 281282071076163352215041445164002970122,
            phase: 0,
            annotation: "n",
        },
    ],
    shared_signals: [],
    fixed_signals: [],
    halo2_advice: [],
    halo2_fixed: [],
    exposed: [
        (
            b,
            Last,
        ),
        (
            n,
            Last,
        ),
    ],
    annotations: {
        281282153948821342135539412435905153546: "fibo step",
        281282071076163352215041445164002970122: "n",
        281282073769920877700029204819473992202: "fibo first step",
        281282068699318476787111035882707749386: "b",
        281282057290463074733046140937402190346: "a",
        281282176211935008643818839171708619274: "padding",
    },
    fixed_assignments: None,
    first_step: Some(
        281282073769920877700029204819473992202,
    ),
    last_step: Some(
        281282176211935008643818839171708619274,
    ),
    num_steps: 11,
    q_enable: true,
}
```

## Plonkish arithmatization

This is the arithmetization used by Halo2.

The plonkish arithmetization is based on columns, rows and polynomial identities.

There are a number of columns defined by the circuit of three types: advice, instance and fixed.

The polynomial identities are polynomial expressions which variables are (columns, rotation) pairs.

For example: `(a, 0) * (b, 1) - (c, 2)`.

The rotations are offset of rows.

All polynomial identities has to evaluate to zero for the circuit to be valid.

TODO: Diagrams, explain better

## Plonkish compiler

The plonkish compiler takes a chiquito AST and produces a Plonkish representation based on columns, rows and polynomial identities.

### Cell Manager

The cell manager is an abstract component of the compiler, that places the signals in the plonkish table. There are more than one implementation, that use different strategies for it. A chiquito step can use more than one row of the plonkish table, and that way use less columns.

The result of its execution is a placement like this:

```
Placement {
    forward: {
        ForwardSignal {
            id: 112757503094494736886533768524178524682,
            phase: 0,
            annotation: "n",
        }: SignalPlacement {
            column: Column {
                annotation: "mwcm forward signal a",
                ctype: Advice,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: 112757574875209974810026443024764635658,
            },
            rotation: 1,
        },
        ForwardSignal {
            id: 112757502381441274258154448707306261002,
            phase: 0,
            annotation: "b",
        }: SignalPlacement {
            column: Column {
                annotation: "mwcm forward signal b",
                ctype: Advice,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: 112757577568967500295014202680235657738,
            },
            rotation: 0,
        },
        ForwardSignal {
            id: 112757497944664173459351261993868331530,
            phase: 0,
            annotation: "a",
        }: SignalPlacement {
            column: Column {
                annotation: "mwcm forward signal a",
                ctype: Advice,
                halo2_advice: None,
                halo2_fixed: None,
                phase: 0,
                id: 112757574875209974810026443024764635658,
            },
            rotation: 0,
        },
    },
    shared: {},
    fixed: {},
    steps: {
        112757545640018007046483900682209987082: StepPlacement {
            height: 2,
            signals: {
                InternalSignal {
                    id: 112757546907668607274713583653889903114,
                    annotation: "c",
                }: SignalPlacement {
                    column: Column {
                        annotation: "mwcm forward signal b",
                        ctype: Advice,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: 112757577568967500295014202680235657738,
                    },
                    rotation: 1,
                },
            },
        },
        112757553404377933444389547799470541322: StepPlacement {
            height: 2,
            signals: {},
        },
        112757504045232687057706101121682639370: StepPlacement {
            height: 2,
            signals: {
                InternalSignal {
                    id: 112757506659762050028429523183609711114,
                    annotation: "c",
                }: SignalPlacement {
                    column: Column {
                        annotation: "mwcm forward signal b",
                        ctype: Advice,
                        halo2_advice: None,
                        halo2_fixed: None,
                        phase: 0,
                        id: 112757577568967500295014202680235657738,
                    },
                    rotation: 1,
                },
            },
        },
    },
    columns: [
        Column {
            annotation: "mwcm forward signal a",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 112757574875209974810026443024764635658,
        },
        Column {
            annotation: "mwcm forward signal b",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 112757577568967500295014202680235657738,
        },
    ],
    base_height: 2,
}
```

### Step Selector

```
StepSelector {
    selector_expr: {
        315264198831617735253233275444124060170: (Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264299134471478311887765095509002762 }, 0, "'step selector for fibo first step'"),
        315264247477709519011537120830062987786: (Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264304284302041739069990150842485258 }, 0, "'step selector for fibo step'"),
        315264254766700470323856742386059840010: (Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264306265006104595678711464417954314 }, 0, "'step selector for padding'"),
    },
    selector_expr_not: {
        315264198831617735253233275444124060170: (0x1 + (-(Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264299134471478311887765095509002762 }, 0, "'step selector for fibo first step'"))),
        315264247477709519011537120830062987786: (0x1 + (-(Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264304284302041739069990150842485258 }, 0, "'step selector for fibo step'"))),
        315264254766700470323856742386059840010: (0x1 + (-(Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264306265006104595678711464417954314 }, 0, "'step selector for padding'"))),
    },
    selector_assignment: {
        315264247477709519011537120830062987786: [
            (
                (Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264304284302041739069990150842485258 }, 0, "'step selector for fibo step'"),
                0x0000000000000000000000000000000000000000000000000000000000000001,
            ),
        ],
        315264198831617735253233275444124060170: [
            (
                (Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264299134471478311887765095509002762 }, 0, "'step selector for fibo first step'"),
                0x0000000000000000000000000000000000000000000000000000000000000001,
            ),
        ],
        315264254766700470323856742386059840010: [
            (
                (Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 315264306265006104595678711464417954314 }, 0, "'step selector for padding'"),
                0x0000000000000000000000000000000000000000000000000000000000000001,
            ),
        ],
    },
    columns: [
        Column {
            annotation: "'step selector for fibo first step'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 315264299134471478311887765095509002762,
        },
        Column {
            annotation: "'step selector for fibo step'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 315264304284302041739069990150842485258,
        },
        Column {
            annotation: "'step selector for padding'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 315264306265006104595678711464417954314,
        },
    ],
}
```

Plonkish IR

```
Circuit {
    columns: [
        Column {
            annotation: "mwcm forward signal a",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230476331769351576842702038531557689866,
        },
        Column {
            annotation: "mwcm forward signal b",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230477086892968500296103924073925052938,
        },
        Column {
            annotation: "q_enable",
            ctype: Fixed,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230476295562081307823898632382065543690,
        },
        Column {
            annotation: "q_first",
            ctype: Fixed,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230476296275134770452277952198937807370,
        },
        Column {
            annotation: "q_last",
            ctype: Fixed,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230476296671275583023599921641634269706,
        },
        Column {
            annotation: "'step selector for fibo step'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230477106700009128862188603934889347594,
        },
        Column {
            annotation: "'step selector for padding'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230477111453698879718049141022503078410,
        },
        Column {
            annotation: "'step selector for fibo first step'",
            ctype: Advice,
            halo2_advice: None,
            halo2_fixed: None,
            phase: 0,
            id: 230477122070272656629470660032369134090,
        },
    ],
    polys: [
        fibo step::(a + b) == c => (a + b + (-c)) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477106700009128862188603934889347594 }, 0, "'step selector for fibo step'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 0, "a[mwcm forward signal a, 0]") + (Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-(Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 1, "c[mwcm forward signal b, 1]"))))),
        fibo step::b == next(a) => (b + (-next(a))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477106700009128862188603934889347594 }, 0, "'step selector for fibo step'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-(Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 2, "next(a)[mwcm forward signal a, 2]")))))),
        fibo step::c == next(b) => (c + (-next(b))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477106700009128862188603934889347594 }, 0, "'step selector for fibo step'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 1, "c[mwcm forward signal b, 1]") + (-(Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 2, "next(b)[mwcm forward signal b, 2]")))))),
        fibo step::n == next(n) => (n + (-next(n))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477106700009128862188603934889347594 }, 0, "'step selector for fibo step'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 1, "n[mwcm forward signal a, 1]") + (-(Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 3, "next(n)[mwcm forward signal a, 3]")))))),
        padding::b == next(b) => (b + (-next(b))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477111453698879718049141022503078410 }, 0, "'step selector for padding'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-(Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 2, "next(b)[mwcm forward signal b, 2]")))))),
        padding::n == next(n) => (n + (-next(n))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477111453698879718049141022503078410 }, 0, "'step selector for padding'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 1, "n[mwcm forward signal a, 1]") + (-(Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 3, "next(n)[mwcm forward signal a, 3]")))))),
        fibo first step::a == 0x1 => (a + (-0x1)) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 0, "a[mwcm forward signal a, 0]") + (-0x1)))),
        fibo first step::b == 0x1 => (b + (-0x1)) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-0x1)))),
        fibo first step::(a + b) == c => (a + b + (-c)) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 0, "a[mwcm forward signal a, 0]") + (Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-(Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 1, "c[mwcm forward signal b, 1]"))))),
        fibo first step::b == next(a) => (b + (-next(a))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 0, "b[mwcm forward signal b, 0]") + (-(Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 2, "next(a)[mwcm forward signal a, 2]")))))),
        fibo first step::c == next(b) => (c + (-next(b))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 1, "c[mwcm forward signal b, 1]") + (-(Column { annotation: "mwcm forward signal b", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477086892968500296103924073925052938 }, 2, "next(b)[mwcm forward signal b, 2]")))))),
        fibo first step::n == next(n) => (n + (-next(n))) => ((Column { annotation: "q_enable", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476295562081307823898632382065543690 }, 0, "q_enable") * ((0x1 + (-(Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last"))) * ((Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'") * ((Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 1, "n[mwcm forward signal a, 1]") + (-(Column { annotation: "mwcm forward signal a", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476331769351576842702038531557689866 }, 3, "next(n)[mwcm forward signal a, 3]")))))),
        q_first => ((Column { annotation: "q_first", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296275134770452277952198937807370 }, 0, "q_first") * (0x1 + (-(Column { annotation: "'step selector for fibo first step'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477122070272656629470660032369134090 }, 0, "'step selector for fibo first step'")))),
        q_last => ((Column { annotation: "q_last", ctype: Fixed, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230476296671275583023599921641634269706 }, 0, "q_last") * (0x1 + (-(Column { annotation: "'step selector for padding'", ctype: Advice, halo2_advice: None, halo2_fixed: None, phase: 0, id: 230477111453698879718049141022503078410 }, 0, "'step selector for padding'")))),
    ],
    lookups: [],
}
```
