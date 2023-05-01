# Chiquito README

# Project Description

Chiquito is a high-level DSL that provides syntax sugar and abstraction for constraint building and column placement when writing Halo2 circuits. It allows the user to manipulate an AST that’s compiled to a Chiquito Halo2 backend, which can be integrated into any Halo2 circuit.

It's **HIGHLY RECOMMENDED** that you read the [design principles](#Design),  [architecture, and specific terms](#Architecture) of a Chiquito circuit before getting started.

You can also learn about the project's [current status](#ProjectStatus) and its [next steps](#NextSteps). 

# **Getting Started**

## Setup

Add the following line to `Cargo.toml` of your project:

```rust
chiquito = { git = "[https://github.com/privacy-scaling-explorations/chiquito](https://github.com/privacy-scaling-explorations/chiquito)", tag = "v2023_04_24_2" }
```

Use the following examples to understand how Chiquito works or use them as starting templates for building your own Chiquito circuit.

Refer to the Appendix on the [exposed user functions](#UserFunctions) and [overall workflow](#Workflow) of a Chiquito circuit.

Refer to [Testing and Links](#Links) on detailed API documentations.


## Example: Fibonacci Circuit
https://github.com/privacy-scaling-explorations/chiquito/blob/main/examples/fibonacci.rs

This example demonstrates how to construct signals, step types, constraints, and witness generation in Chiquito. Best for first time Chiquito users.

## Example: MiMC7 Circuit
TODO: annotate this code example

This example demonstrates how to construct a lookup table and use external inputs as trace arguments in Chiquito, besides covering concepts in the Fibonacci example. MiMC7 is a zk-friendly hashing function.

## Example: zkEVM Bytecode Circuit
https://github.com/privacy-scaling-explorations/zkevm-circuits/pull/1348

This example rewrites the zkEVM bytecode circuit using Chiquito and passes all original tests. It demonstrates how Chiquito can standardize and simplify larger scale circuits on the production level.

# <a id="Links"></a> Testing and Links
**API documentation**: https://qwang98.github.io/chiquito/chiquito/index.html

Currently API documentation is only written for exposed user functions, which are scattered across the DSL, constraint builder, compiler, and AST. **Refer to the following subdirectories for specific functions:**
- Circuit building (DSL): https://qwang98.github.io/chiquito/chiquito/dsl/index.html
- Constraint building (constraint builder): https://qwang98.github.io/chiquito/chiquito/dsl/cb/index.html
- Witness generation (compiler): https://qwang98.github.io/chiquito/chiquito/compiler/trait.WitnessGenContext.html
- Fixed column generation (compiler): https://qwang98.github.io/chiquito/chiquito/compiler/trait.FixedGenContext.html
- Invoking the next instance of a forward signal (AST): https://qwang98.github.io/chiquito/chiquito/ast/expr/query/enum.Queriable.html#method.next

# Licenses

MIT OR Apache-2.0

# Appendix

## <a id="Design"></a> **Design Principles**

**Abstraction**. As circuit complexity increases, abstraction is inevitable. By abstracting constraint building and column placement, Chiquito improves the readability and learnability of Halo2 circuits, which can not only standardize and simplify the code base for complex projects such as the zkEVM, but also onboard more circuit developers.

**Composability**. Chiquito circuits are fully composable with Halo2 circuits, which allows developers to write any part or the entirety of a circuit in Chiquito and integrate with other Halo2 circuits.

**Modularity**. The AST and IR representations of a circuit allow Chiquito to integrate any frontend that can compile into the AST data structure and any backend that can compile from the IR data structure. For example, we can have a Python frontend that compiles to Chiquito AST/IR, which compiles to a Sangria backend. Modularity allows for future extensions.

**User Experience**. Chiquito simplifies and optimizes user experience. For example, annotations for constraints are automatically generated for debugging messages.

## <a id="Architecture"></a> **Architecture**

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

## <a id="Workflow"></a> Overall Workflow

Chiquito is a DSL that compiles Chiquito AST to an IR which can be parsed by a Chiquito Halo2 backend and integrated into a Halo2 circuit. Therefore, to create a Halo2 circuit using Chiquito, we need to:

- Call `circuit` function in DSL, which returns an `ast::Circuit` object. The `circuit` function defines the `ast::Circuit` object by:
    - Importing Halo2 columns
    - Generating fixed columns
    - Adding forward signals
    - Defining and instantiating “steps”, which defines internal signals, constraints, lookups, and witness generation
- Create a `Compiler` object that compiles the `ast::Circuit` object to an `ir::Circuit` object
- Call `chiquito2Halo2` function in Halo2 backend to convert the `ir::Circuit` object to a `ChiquitoHalo2` object
- Integrate `ChiquitoHalo2` object into a Halo2 circuit by including it in the Halo2 circuit config struct
- Call `configure` and `synthesize` functions defined in the Halo2 backend on the `ChiquitoHalo2` object

## <a id="UserFunctions"></a> Exposed User Functions

The above section describes the high level process of building and integrating a Chiquito Halo2 backend object into a Halo2 circuit. However, when building a circuit using Chiquito, the developer mostly call DSL functions to manipulate the `ast::Circuit` object.

DSL functions are defined on five different levels, with nested relationships:

- Circuit level: define and manipulate circuit-level objects, such as forward signals, step types, fixed columns, and imported Halo2 columns
    - Step type level: define and manipulate step-specific objects, such as internal signals, constraints, witness generations
        - Witness generation level: allow user-defined Turing-complete function to manipulate witness generation inputs and assign witness values
    - Fixed column generation level: allow user-defined Turing-complete function to manipulate fixed column generation inputs and assign fixed column values
    - Trace level: create the main circuit by instantiating step types; allow user-defined Turing-complete function to manipulate external trace inputs and assign input values to step type instances

## <a id="ProjectStatus"></a> **Project Status (as of April 2023)** 

The current implementation includes:

- A DSL in Rust
- A backend in Halo2
- Composability with Halo2 circuits
- A working prototype that passes zkEVM bytecode circuit tests
- Hashing function circuit examples

## <a id="NextSteps"></a> **Vision and Next Steps**

Modularity

- Expand frontend to other programming languages, e.g. Python
- Integrate additional backends and proof systems

Library

- Add additional circuit examples

Infrastructure

- Cmd tool and npm package for developers