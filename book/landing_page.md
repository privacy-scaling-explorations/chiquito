# Meet Chiquito

Chiquito is a high-level structured language for implementing zero knowledge proof applications, currently being implemented in the DSL Working Group of PSE, Ethereum Foundation. It is a step-based zkDSL (zero knowledge domain specific language) that provides better syntax and abstraction for features like constraint building and column placement. Chiquito has a Halo2 backend, which is a low level zkDSL that writes circuits using the PLONKish arithemtization and is working on supporting additional backends.

Chiquito can be written in both Python and Rust. This tutorial focuses on Python.

The key advantages of Chiquito include: 
- Abstraction and simplification on the readability and learnability of Halo2 circuits.
- Composabiity with other Halo2 circuits.
- Modularity of using multiple frontends (Python and Rust) and backends (Halo2 and beyond).
- Smooth user experience with a dynamically typed language (Python).

<p align="center">
  <img src="https://hackmd.io/_uploads/HyuEr1cB2.png" width="180" height="80" alt="Image 2">
  &nbsp; &nbsp; &nbsp;
  <img src="https://hackmd.io/_uploads/HyZ0rycS2.png" width="70" height="100" alt="Image 3">
</p>
