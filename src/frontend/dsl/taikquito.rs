#[macro_export]
macro_rules! circuit {
    ($id:ident, $content:block) => {{
        use halo2_proofs::halo2curves::bn256::Fr;

        chiquito::dsl::circuit::<Fr, (), _>(stringify!($id), |ctx| {
            use $crate::circuit_context;
            circuit_context!(ctx);

            $content
        })
    }};
}

#[macro_export]
macro_rules! circuit_context {
    ($ctx: expr) => {
        macro_rules! forward {
            ($id_forward:ident) => {
                $ctx.forward(stringify!($id_forward))
            };

            ($id_forward:literal) => {
                $ctx.forward($id_forward)
            };
        };

        macro_rules! step_type_def {
            ($id_step: ident $step_def_content: block) => {
                $ctx.step_type_def(stringify!($id_step), |ctx| {
                    use $crate::step_type_context;
                    step_type_context!(ctx, $);

                    $step_def_content
                })
            };

            ($id_step: literal $step_def_content: block) => {
                $ctx.step_type_def($id_step, |ctx| {
                    use $crate::step_type_context;
                    step_type_context!(ctx, $);

                    $step_def_content
                })
            };
        };

        macro_rules! pragma_num_steps {
            ($num_steps:expr) => {
                $ctx.pragma_num_steps($num_steps);
            };
        }

        macro_rules! trace {
            ($trace_content:block) => {
                $ctx.trace(move |ctx, _| {
                    use $crate::circuit_trace_context;
                    circuit_trace_context!(ctx);

                    $trace_content
                })
            };
        }
    };
}

#[macro_export]
macro_rules! step_type_context {
    ($ctx: expr, $d:tt) => {
        macro_rules! internal {
            ($id_internal:ident) => {
                $ctx.internal(stringify!($id_internal))
            };
        }

        macro_rules! setup {
            ($setup_content: block) => {
                $ctx.setup(|ctx| {
                    use $crate::step_type_setup_context;
                    step_type_setup_context!(ctx);

                    $setup_content
                });
            };
        }

        macro_rules! wg {
                                    ($d($args_id: ident : $args_ty:ty),+ $wg_content: block) => {
                                        $ctx.wg(move |ctx, ($d($args_id),*): ($d($args_ty),*)| {
                                            use $crate::step_type_wg_context;
                                            step_type_wg_context!(ctx);

                                            $wg_content
                                        })
                                    };
                                }
    };
}

#[macro_export]
macro_rules! step_type_setup_context {
    ($ctx: expr) => {
        macro_rules! require {
            ($lhs:expr => $rhs:expr) => {{
                $ctx.constr($crate::dsl::cb::eq($lhs, $rhs));
            }};

            (transition $lhs:expr => $rhs:expr) => {{
                $ctx.transition($crate::dsl::cb::eq($lhs, $rhs));
            }};
        }
    };
}

#[macro_export]
macro_rules! step_type_wg_context {
    ($ctx: expr) => {
        macro_rules! assign {
            ($signal:expr => $value:expr) => {
                $ctx.assign($signal, $value)
            };
        }
    };
}

#[macro_export]
macro_rules! circuit_trace_context {
    ($ctx: expr) => {
        macro_rules! add {
            ($step_type: expr, $args: expr) => {
                $ctx.add($step_type, $args);
            };
        };
    };
}
