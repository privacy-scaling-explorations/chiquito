# Design Principles

**Abstraction**. As circuit complexity increases, abstraction is inevitable. By abstracting constraint building and column placement, Chiquito improves the readability and learnability of Halo2 circuits, which can not only standardize and simplify the code base for complex projects such as the zkEVM, but also onboard more circuit developers.

**Composability**. Chiquito circuits are fully composable with Halo2 circuits, which allows developers to write any part or the entirety of a circuit in Chiquito and integrate with other Halo2 circuits.

**Modularity**. The AST and IR representations of a circuit allow Chiquito to integrate any frontend that can compile into the AST data structure and any backend that can compile from the IR data structure. For example, we can have a Python frontend that compiles to Chiquito AST/IR, which compiles to a Sangria backend. Modularity allows for future extensions.

**User Experience**. Chiquito simplifies and optimizes user experience. For example, annotations for constraints are automatically generated for debugging messages.
