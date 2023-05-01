# Chiquito README

# Project Description

Chiquito is a high-level DSL that provides syntax sugar and abstraction for constraint building and column placement when writing Halo2 circuits. It allows the user to manipulate an AST that’s compiled to a Chiquito Halo2 backend, which can be integrated into any Halo2 circuit.

## **Design Principles**

**Abstraction**. As circuit complexity increases, abstraction is inevitable. By abstracting constraint building and column placement, Chiquito improves the readability and learnability of Halo2 circuits, which can not only standardize and simplify the code base for complex projects such as the zkEVM, but also onboard more circuit developers.

**Composability**. Chiquito circuits are fully composable with Halo2 circuits, which allows developers to write any part or the entirety of a circuit in Chiquito and integrate with other Halo2 circuits.

**Modularity**. The AST and IR representations of a circuit allow Chiquito to integrate any frontend that can compile into the AST data structure and any backend that can compile from the IR data structure. For example, we can have a Python frontend that compiles to Chiquito AST/IR, which compiles to a Sangria backend. Modularity allows for future extensions.

**User Experience**. Chiquito simplifies and optimizes user experience. For example, annotations for constraints are automatically generated for debugging messages.

## **Architecture**

There are two major architectural differences between Chiquito and Halo2:

- Chiquito circuit is composed of “steps”. Each step defines the constraints among witnesses, fixed columns, and lookup tables, and can be composed of one or multiple rows in a PLONKish table. That’s why steps are also called “super rows”. We made this design choice to allow for more complex constraints, which sometimes require allocating multiple Halo2 rows.
- Chiquito DSL is based on “signals” rather than columns in order to abstract away column placements. One signal can be placed in different columns across different steps, all handled by Chiquito’s compiler.

Chiquito circuit has the following architecture

- Circuit (with optional input from Halo2)
    - Forward signals (signals with constraints across different steps)
    - Fixed columns
    - Step types
        - Internal signals (signals with constraints only within one step)
        - Internal constraints (constraints for internal signals only)
        - Transition constraints (constraints involving forward signals)
        - Witness generation function for one step type instance
    - Trace (global circuit witness generation)
        - Adds instances of step types

## **Project Status (as of April 2023)**

The current implementation includes:

- A DSL in Rust
- A backend in Halo2
- Composability with Halo2 circuits
- A working prototype that passes zkEVM bytecode circuit tests
- Hashing function circuit examples

## **Vision and Next Steps**

Modularity

- Expand frontend to other programming languages, e.g. Python
- Integrate additional backends and proof systems

Library

- Add additional circuit examples

Infrastructure

- Cmd tool and npm package for developers

# **Getting Started**

## Setup

Add the following line to `Cargo.toml` of your project:

```rust
chiquito = { git = "[https://github.com/privacy-scaling-explorations/chiquito](https://github.com/privacy-scaling-explorations/chiquito)", tag = "v2023_04_24_2" }
```

Paste the following standard crate import header to the top of your circuit code file:

```rust
use chiquito::{
    dsl::{
        circuit, // main function for constructing an AST circuit
        cb::*, // functions for constraint building
    },
    ast::{
        query::*,
        expr::*,
    },
    compiler::{
        cell_manager::SingleRowCellManager, // input for constructing the compiler
        step_selector::SimpleStepSelectorBuilder, // input for constructing the compiler
        Compiler, // compiles AST to IR
    },
    ir::Circuit, // IR object that the compiler compiles to
    backend::halo2::{chiquito2Halo2, ChiquitoHalo2}, // compiles to Chiquito Halo2 backend, which can be integrated into Halo2 circuit
    stdlib::*, // standard library
};
```

## Example: Build zkEVM Bytecode Chiquito Circuit

The following annotated example uses Chiquito DSL to generate an AST representation of the zkEVM bytecode circuit, which is compiled to an IR. For specific usage of each DSL function, please refer to the API docs [[Link]].

```rust
use std::cell::RefCell;

use bus_mapping::state_db::EMPTY_CODE_HASH_LE;

// the crate import header can be adapted to fit the need of a specific circuit
use chiquito::{
    ast::{ToExpr, ToField},
    compiler::{
        cell_manager::SingleRowCellManager, step_selector::TwoStepsSelectorBuilder, Compiler,
    },
    dsl::circuit,
    ir::Circuit,
    stdlib::IsZero,
};
use eth_types::Field;
use halo2_proofs::plonk::{Column, Fixed};

use crate::bytecode_circuit::bytecode_unroller::unroll;

use super::{
    circuit::{BytecodeCircuitConfigArgs, WitnessInput},
    wit_gen::BytecodeWitnessGen,
};

pub fn bytecode_circuit<F: Field + From<u64>>( 
    BytecodeCircuitConfigArgs {
        bytecode_table, // import Halo2 lookup tables for composability
        keccak_table, 
        challenges,
    }: &BytecodeCircuitConfigArgs<F>,
    push_data_table_value: Column<Fixed>, // import Halo2 fixed columns for composability
    push_data_table_size: Column<Fixed>, 
) -> Circuit<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>> { // returns the compiled IR of a Chiquito circuit
    let bytecode_circuit = circuit::<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>, _>( // the DSL function that returns Chiquito's AST representation of a circuit
        "bytecode circuit",
        |ctx| {
            use chiquito::dsl::cb::*; // import constraint building functions
            // the following objects (forward signals, imported halo2 columns, steptypes) are defined on the circuit-level
            let length = ctx.forward("length"); // forward signals can have constraints across different steps
            let push_data_left = ctx.forward("push_data_left");
            let value_rlc = ctx.forward_with_phase("value_rlc", 1);

            let index = ctx.import_halo2_advice("index", bytecode_table.index); // import halo2 columns for lookup tables
            let hash = ctx.import_halo2_advice("hash", bytecode_table.code_hash);
            let is_code = ctx.import_halo2_advice("is_code", bytecode_table.is_code);
            let value = ctx.import_halo2_advice("value", bytecode_table.value);
            let _tag = ctx.import_halo2_advice("tag", bytecode_table.tag);

            let push_data_table_value =
                ctx.import_halo2_fixed("push_data_value", push_data_table_value);
            let push_data_table_size =
                ctx.import_halo2_fixed("push_data_size", push_data_table_size);

            let keccak_is_enabled =
                ctx.import_halo2_advice("keccak_is_enabled", keccak_table.is_enabled);
            let keccak_value_rlc =
                ctx.import_halo2_advice("keccak_value_rlc", keccak_table.input_rlc);
            let keccak_length = ctx.import_halo2_advice("keccak_length", keccak_table.input_len);
            let keccak_hash = ctx.import_halo2_advice("keccak_hash", keccak_table.output_rlc);

            let header = ctx.step_type("header"); // initiate step type for future definition
            let byte_step = ctx.step_type("byte");

            ctx.pragma_first_step(header); // enforce step type of the first step
            ctx.pragma_last_step(header); // enforce step type of the last step

            ctx.step_type_def(header, move |ctx| { // define step type
                // the following objects (constraints, transition constraints, witness generation function, fixed column generation function)
                // are defined on the step type-level

                // regular constraints are for internal signals only
                ctx.constr(isz(index)); // constrain that index is zero, by invoking isz function from constraint builder
                ctx.constr(eq(value, length)); // constrain that value is equal to length, by invoking eq function from constraint builder
                // transition constraints accepts forward signals as well
                ctx.transition(if_next_step(header, isz(length))); // if the next step type is header, constrain length to zero

                let empty_hash = rlc(
                    &EMPTY_CODE_HASH_LE.map(|v| (v as u64).expr()),
                    challenges.evm_word(),
                );

                ctx.transition(if_next_step(header, eq(hash, empty_hash)));

                ctx.transition(if_next_step(byte_step, eq(length, length.next())));
                ctx.transition(if_next_step(byte_step, isz(index.next())));
                ctx.transition(if_next_step(byte_step, eq(is_code.next(), 1)));
                ctx.transition(if_next_step(byte_step, eq(hash, hash.next())));
                ctx.transition(if_next_step(byte_step, eq(value_rlc.next(), value.next())));
                // witness generation (wg) function is Turing complete and allows arbitrary user defined logics for assigning witness values
                // wg function is defined here but not yet invoked
                ctx.wg(move |ctx, wit| {
                    let wit = wit.borrow();

                    ctx.assign(index, 0.field()); // assign arbitrary value to witness
                    ctx.assign(length, wit.length.field());
                    ctx.assign(value, wit.length.field());
                    ctx.assign(is_code, 0.field());
                    ctx.assign(value_rlc, 0.field());

                    wit.code_hash.map(|v| ctx.assign(hash, v));
                })
            });

            ctx.step_type_def(byte_step, move |ctx| {
                // internal signals can only have constraints within the same step
                let push_data_size = ctx.internal("push_data_size");
                let push_data_left_inv = ctx.internal("push_data_left_inv");
                let index_length_diff_inv = ctx.internal("index_length_diff_inv");

                let push_data_left_is_zero =
                    IsZero::setup(ctx, push_data_left, push_data_left_inv); // IsZero gadget is invoked from the standard library, which is growing

                let index_length_diff_is_zero = IsZero::<F>::setup(ctx, index + 1 - length,  index_length_diff_inv);

                ctx.constr(
                    eq(is_code, push_data_left_is_zero.is_zero()),
                );
                // add_lookup function adds a lookup table to the step type
                ctx.add_lookup(
                    lookup() // lookup function generates an empty LookupBuilder, which manipulates the lookup table
                    .add(value, push_data_table_value) // add function adds a source column-lookup column pair to the lookup table
                    .add(push_data_size, push_data_table_size) 
                    // one can infinitely chain add function calls to the lookup table, 
                    // or call the enable function to set up a selector column for the lookup table
                    // for example: lookup().add(source_col, lookup_col).add(source_col, lookup_col).enable(selector_col)
                );
                
                ctx.transition(
                    if_next_step(byte_step,
                        eq(length, length.next())
                    )
                );
                ctx.transition(
                    if_next_step(byte_step,
                        eq(index + 1, index.next())
                    )
                );
                ctx.transition(
                    if_next_step(byte_step,
                        eq(hash, hash.next())
                    )
                );
                ctx.transition(
                    if_next_step(byte_step,
                        eq(value_rlc.next(), (value_rlc * challenges.keccak_input()) + value.next())
                    )
                );
                ctx.transition(
                    if_next_step(byte_step,
                        eq(
                            push_data_left.next(),
                            select(is_code, push_data_size, push_data_left - 1),
                        )
                    )
                );

                ctx.transition(
                    if_next_step(header,
                        eq(index + 1, length)
                    )
                );

                ctx.transition(select(index_length_diff_is_zero.is_zero(), next_step_must_be(header), 0));

                ctx.add_lookup(
                    lookup()
                    .add(1, keccak_is_enabled)
                    .add(value_rlc, keccak_value_rlc)
                    .add(length, keccak_length)
                    .add(hash, keccak_hash)
                    .enable(header.next()) // add a selector column to the lookup table
                );

                ctx.wg(move |ctx, wit| {
                    let wit = wit.borrow();

                    ctx.assign(index, wit.index());
                    ctx.assign(length, wit.length.field());
                    ctx.assign(value, wit.value());
                    ctx.assign(is_code, wit.is_code());

                    wit.value_rlc.map(|v| ctx.assign(value_rlc, v));
                    wit.code_hash.map(|v| ctx.assign(hash, v));

                    ctx.assign(push_data_size, wit.push_data_size.field());
                    ctx.assign(push_data_left, wit.push_data_left.field());
                    push_data_left_is_zero.wg(ctx, wit.push_data_left.field());
                    index_length_diff_is_zero.wg(ctx, wit.index() + <i32 as chiquito::ast::ToField<F>>::field(&1) - <usize as chiquito::ast::ToField<F>>::field(&wit.length));
                });
            });
            // trace function is responsible for adding step instantiations defined in step_type_def function above
            // trace function is Turing complete and allows arbitrary user defined logics for assigning witness values
            ctx.trace(
                move |ctx, (bytecodes, challenges, last_row_offset, overwrite_len)| {
                    ctx.set_height(last_row_offset + 1);

                    let mut offset = 0;
                    for bytecode in bytecodes.iter() {
                        let wit = if overwrite_len == 0 {
                            RefCell::new(BytecodeWitnessGen::new(bytecode, &challenges))
                        } else {
                            RefCell::new(BytecodeWitnessGen::new_overwrite_len(
                                bytecode,
                                &challenges,
                                overwrite_len,
                            ))
                        };

                        println!("start wit gen");

                        if offset < last_row_offset - 1 {
                            ctx.add(&header, wit.clone()); // add function adds a step instantiation to the main circuit and calls witness generation function defined in step_type_def
                            offset += 1;
                        }

                        while wit.borrow_mut().has_more() && offset < last_row_offset - 1 {
                            wit.borrow_mut().next_row();
                            ctx.add(&byte_step, wit.clone());
                            offset += 1;
                        }
                    }

                    let wit = RefCell::new(BytecodeWitnessGen::new(&unroll(vec![]), &challenges));

                    while offset <= last_row_offset {
                        ctx.add(&header, wit.clone());
                        offset += 1;
                    }
                },
            )
        },
    );
    // create a new compiler using a cell manager instance and a selector builder instance
    let compiler = Compiler::new(
        SingleRowCellManager::default(),
        TwoStepsSelectorBuilder {
            halo2_column: Some(bytecode_table.tag),
            hint_one: Some("byte".to_string()),
        },
    );
    // compile the circuit into an IR object
    compiler.compile(&bytecode_circuit)
}
```

Important functions such as fixed_gen, which generates fixed columns from scratch, are not used in this example, but can be found in the API docs [[link]].

After compiling Chiquito AST to an IR, it is further parsed by a Chiquito Halo2 backend and integrated into a Halo2 circuit, which we expand in the next example.

## Example: Integrate zkEVM Bytecode Chiquito Circuit in Halo2

On the high level, to integrate Chiquito IR circuit in Halo2, we:

- Call `chiquito2Halo2` function in Halo2 backend to convert the `ir::Circuit` object to a `ChiquitoHalo2` object
- Integrate `ChiquitoHalo2` object into a Halo2 circuit by including it in the Halo2 circuit config struct
- Call `configure` and `synthesize` functions defined in the Halo2 backend on the `ChiquitoHalo2` object

See an example for the zkEVM bytecode Chiquito circuit below:

```rust
pub type WitnessInput<F> = (Vec<UnrolledBytecode<F>>, Challenges<Value<F>>, usize, usize);

#[derive(Clone, Debug)]
pub struct BytecodeCircuitConfig<F: Field> {
    // chiquito2Halo2 function in Halo2 backend can convert ir::Circuit object to a ChiquitoHalo2 object, 
    // which can be further integrated into a Halo2 circuit in the example below
    compiled: ChiquitoHalo2<F, WitnessInput<F>, RefCell<BytecodeWitnessGen<F>>>, // ChiquitoHalo2 object in the bytecode circuit config struct
    push_data_table: ChiquitoHalo2<F, (), ()>,
    pub(crate) keccak_table: KeccakTable,

    minimum_rows: usize,
}

pub struct BytecodeCircuitConfigArgs<F: Field> {
    pub bytecode_table: BytecodeTable,
    pub keccak_table: KeccakTable,
    pub challenges: Challenges<Expression<F>>,
}

impl<F: Field> SubCircuitConfig<F> for BytecodeCircuitConfig<F> {
    type ConfigArgs = BytecodeCircuitConfigArgs<F>;

    fn new(meta: &mut ConstraintSystem<F>, config: Self::ConfigArgs) -> Self {
        let push_data_value = meta.fixed_column();
        let push_data_size = meta.fixed_column();

        let mut push_data_table =
            chiquito2Halo2(push_data_table_circuit(push_data_value, push_data_size));

        push_data_table.configure(meta); // ChiquitoHalo2 objects have their own configure and synthesize functions defined in the Chiquito Halo2 backend

        let mut circuit =
            chiquito2Halo2(bytecode_circuit(&config, push_data_value, push_data_size));

        circuit.configure(meta);

        Self {
            compiled: circuit, // ChiquitoHalo2 object in the bytecode circuit config struct
            push_data_table,
            keccak_table: config.keccak_table,
            minimum_rows: meta.minimum_rows(),
        }
    }
}

#[derive(Default, Debug, Clone)]
pub struct BytecodeCircuit<F: Field> {
    pub bytecodes: Vec<UnrolledBytecode<F>>,
    pub size: usize,
    pub overwrite_len: usize,
}

impl<F: Field> BytecodeCircuit<F> {
    pub fn new(bytecodes: Vec<UnrolledBytecode<F>>, size: usize) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite_len: 0,
        }
    }

    pub fn new_overwrite_len(
        bytecodes: Vec<UnrolledBytecode<F>>,
        size: usize,
        overwrite_len: usize,
    ) -> Self {
        BytecodeCircuit {
            bytecodes,
            size,
            overwrite_len,
        }
    }

    pub fn new_from_block_sized(block: &witness::Block<F>, bytecode_size: usize) -> Self {
        let bytecodes: Vec<UnrolledBytecode<F>> = block
            .bytecodes
            .iter()
            .map(|(_, b)| unroll(b.bytes.clone()))
            .collect();
        Self::new(bytecodes, bytecode_size)
    }
}

impl<F: Field> SubCircuit<F> for BytecodeCircuit<F> {
    type Config = BytecodeCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        let bytecode_size = block.circuits_params.max_bytecode + 128;
        Self::new_from_block_sized(block, bytecode_size)
    }

    fn synthesize_sub(
        &self,
        config: &Self::Config,
        challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        config.push_data_table.synthesize(layouter, ());
        config.compiled.synthesize( // ChiquitoHalo2 objects have their own configure and synthesize functions defined in the Chiquito Halo2 backend
            layouter,
            (
                self.bytecodes.clone(),
                *challenges,
                self.size - (config.minimum_rows + 1),
                self.overwrite_len,
            ),
        );

        Ok(())
    }

    fn min_num_rows_block(block: &witness::Block<F>) -> (usize, usize) {
        (
            block
                .bytecodes
                .values()
                .map(|bytecode| bytecode.bytes.len() + 1)
                .sum(),
            block.circuits_params.max_bytecode,
        )
    }
}
```

# Testing and Links

Reference to the zkEVM bytecode circuit written chiquito passing the tests. Pull request link: https://github.com/privacy-scaling-explorations/zkevm-circuits/pull/1348

# Licenses

MIT OR Apache-2.0