# Appendix

## Design Principles

**Abstraction**. As circuit complexity increases, abstraction is inevitable. By abstracting constraint building and column placement, Chiquito improves the readability and learnability of Halo2 circuits, which can not only standardize and simplify the code base for complex projects such as the zkEVM, but also onboard more circuit developers.

**Composability**. Chiquito circuits are fully composable with Halo2 circuits, which allows developers to write any part or the entirety of a circuit in Chiquito and integrate with other Halo2 circuits.

**Modularity**. The AST and IR representations of a circuit allow Chiquito to integrate any frontend that can compile into the AST data structure and any backend that can compile from the IR data structure. For example, we can have a Python frontend that compiles to Chiquito AST/IR, which compiles to a Sangria backend. Modularity allows for future extensions.

**User Experience**. Chiquito simplifies and optimizes user experience. For example, annotations for constraints are automatically generated for debugging messages.

## Architecture

There are two major architectural differences between Chiquito and Halo2:

- Chiquito circuit is composed of “step” instances. Each step type defines the constraints among witnesses, fixed columns, and lookup tables. Step instances are also called “super rows”, each composed of one or multiple rows in a PLONKish table. We made this design choice to allow for more complex constraints, which sometimes require allocating multiple Halo2 rows.
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

## Overall Workflow

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

## Exposed User Functions

The above section describes the high level process of building and integrating a Chiquito Halo2 backend object into a Halo2 circuit. However, when building a circuit using Chiquito, the developer mostly call DSL functions to manipulate the `ast::Circuit` object.

DSL functions are defined on five different levels, with nested relationships:

- Circuit level: define and manipulate circuit-level objects, such as forward signals, step types, fixed columns, and imported Halo2 columns
    - Step type level: define and manipulate step-specific objects, such as internal signals, constraints, witness generations
        - Witness generation level: allow user-defined Turing-complete function to manipulate witness generation inputs and assign witness values
    - Fixed column generation level: allow user-defined Turing-complete function to manipulate fixed column generation inputs and assign fixed column values
    - Trace level: create the main circuit by instantiating step types; allow user-defined Turing-complete function to manipulate external trace inputs and assign input values to step type instances

## Project Status (as of April 2023)

The current implementation includes:

- A DSL in Rust
- A backend in Halo2
- Composability with Halo2 circuits
- A working prototype that passes zkEVM bytecode circuit tests
- Hashing function circuit examples

## Vision and Next Steps

Modularity

- Expand frontend to other programming languages, e.g. Python
- Integrate additional backends and proof systems

Library

- Add additional circuit examples

Infrastructure

- Cmd tool and npm package for developers
