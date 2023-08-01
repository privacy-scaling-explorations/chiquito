# Chiquito

# Project Description

Chiquito is a step-based high-level rust DSL (pychiquito is a python DSL for chiquito) that provides better syntax and abstraction for constraint building and column placement when writing plonkish circuits and has a Halo2 backend, and other backends are in the works. It allows the user to manipulate an AST that’s compiled to a Chiquito Halo2 backend, which can be integrated into any Halo2 circuit.

It's **HIGHLY RECOMMENDED** that you read the [design principles](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#design-principles),  [architecture, and specific terms](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#architecture) of a Chiquito circuit before getting started.

You can also learn about the project's [current status](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#project-status-as-of-april-2023)) and its [next steps](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#vision-and-next-steps). 

# Getting Started

## Setup
Run the following in command line to add Chiquito as a dependency for your project:
```
cargo add --git https://github.com/privacy-scaling-explorations/chiquito 
```

Use the following examples to understand how Chiquito works or use them as starting templates for building your own Chiquito circuit.

Refer to the Appendix on the [exposed user functions](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#exposed-user-functions) and [overall workflow](https://github.com/privacy-scaling-explorations/chiquito/blob/main/Appendix.md/#overall-workflow) of a Chiquito circuit.

Refer to [Testing and Links](#testing-and-links) on detailed API documentations.


## Example: Fibonacci Circuit
Run the following in command line:
```
cargo run --example fibonacci
```

This example demonstrates how to construct signals, step types, constraints, and witness generation in Chiquito. Best for first time Chiquito users.

## Example: MiMC7 Circuit
TODO: annotate this code example

This example demonstrates how to construct a lookup table and use external inputs as trace arguments in Chiquito, besides covering concepts in the Fibonacci example. MiMC7 is a zk-friendly hashing function.

## Example: zkEVM Bytecode Circuit
https://github.com/privacy-scaling-explorations/zkevm-circuits/pull/1348

This example rewrites the zkEVM bytecode circuit using Chiquito and passes all original tests. It demonstrates how Chiquito can standardize and simplify larger scale circuits on the production level.

# Testing and Links
**API documentation**: `cargo doc --no-deps --package chiquito --open`

Currently API documentation is only written for exposed user functions, which are scattered across the DSL, constraint builder, compiler, and AST. **Refer to the following subdirectories for specific functions:**
- Circuit building (DSL): https://qwang98.github.io/chiquito/chiquito/dsl/index.html
- Constraint building (constraint builder): https://qwang98.github.io/chiquito/chiquito/dsl/cb/index.html
- Witness generation (compiler): https://qwang98.github.io/chiquito/chiquito/compiler/trait.WitnessGenContext.html
- Fixed column generation (compiler): https://qwang98.github.io/chiquito/chiquito/compiler/trait.FixedGenContext.html
- Invoking the next instance of a forward signal (AST): https://qwang98.github.io/chiquito/chiquito/ast/expr/query/enum.Queriable.html#method.next

# Licenses

MIT OR Apache-2.0
