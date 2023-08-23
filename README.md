# Chiquito

Chiquito is a high-level structured language for implementing zero knowledge proof applications.

Chiquito is being implemented in the DSL Working Group of PSE, Ethereum Foundation.

<p align="center">
  <img src="https://hackmd.io/_uploads/HyuEr1cB2.png" width="180" height="80" alt="Image 2">
  &nbsp; &nbsp; &nbsp;
  <img src="https://hackmd.io/_uploads/HyZ0rycS2.png" width="70" height="100" alt="Image 3">
</p>


## Why is chiquito different from other ZKP DSLs?

Most ZKP DSLs are based on writing constraints, witness generation and some abstraction for DRY like templates or gadgets.

Chiquito allows the developer to think in more high-level and structured abstractions that most ZKP DSLs, while not sacrificing performance.

## What is the chiquito programming model?

Chiquito starts from the idea that every zero knowledge proof represents a program (the setup), which can have many computations (the trace) that is proven for a certain input, output and intermediate values (the witness).

The main structured abstraction in chiquito is the **step**. Any computation can be divided in individual steps. A program is represented by a circuit that has one or many **step types**, a particular computation is represented as a series of **step instances** that can have arbitrary order.

A step type contains:
 + Setup: a series of constraints or assertions that must hold for a step instance of this type to be valid.
 + Witness generation: code that for a particular input sets the values of the witness for a particular step instance.

A chiquito circuit contains a trace function that for a given input will generate the step instances in a particular order and use the step type witness generation.

Another important piece of Chiquito are the signals. They represent elements of the witness.

There are several types:

 + Internal signals: they are private for a particular step, and cannot be constriants for other steps.
 + Shared signals: they are shared by all steps in the circuit, and they can be constraints for their values on relative step instances (**rotation**). For example, if "a" is a shared signal, you could assert in a step type setup that `a == a.rot(2)` which means that `a` is equal to `a` in the next of the next step (super rotation `+2`).
 + Forward signals: They are like shared signals with the restriction that they can only constrain in the current and the next step instances. For example you could assert `a == a.next()` but you could not assert `a == a.prev()`. Forward signal has the advantage of allowing for witness size optimisations.
 + Fixed signals: Their values are set during setup and cannot change.

Chiquito has many more features, but these are enough to start writing basic circuits.

## What proving system chiquito uses?

Currently Halo2 backend is implemented, but we are looking into implementing other backends.

Chiquito frontend comes in two flavours: rust and python, so you can write Chiquito applications in either Rust or Python. PyChiquito, and any other language interface in the future, uses ChiquitoCore for most of its work, so adding new languages is easy.

## What are the features of chiquito?

 + Step-based, that abstracts out the computation that you want to prove.
 + Signals, that abstract out the data (witness) and how it is placed and handled.
 + Constraint builder, allows you to write the constraints of your application in a more readable and natural way.
 + Trace based witness generation, a way to generate the data that you are trying to prove that matches how computation is done.
 + Super circuits, that allow combining many circuits into one.
 + Lookup tables, that allow sharing data between multiple circuits.
 + Expose signals as public very easily.
 + Automatic padding.
 + Completely modular platform, that allows writing circuits in multiple languages and use different proving systems.

PLONKish-specific features:
 + Halo2 backend ready.
 + PLONKish Cell Managers. These are modular strategies to place signals in the PLONKish columns and rotations. These allows for steps to use different numbers of rows and columns, in a configurable way, so you can find the most efficient structure for your circuit.
 + PLONKish step selector builders. These are modular strategies to activate the steps in the witness.

Planned:
 + Nested steps, will allow more complex circuits and allow circuits coordination in proving systems without advice based lookup tables.
 + Gadget abstraction.
 + Arbitrary boolean assertions.

In research:
 + Signal typing system, which allows statically checking for soundness issues.
 + Folding backend with ProtoStar, HyperNova, and/or others.

## Fibonnaci circtuit in Chiquito's Python frontend.

But better see for yourself:

```
class FiboStep(StepType):
    def setup(self: FiboStep):
        self.c = self.internal("c")
        self.constr(eq(self.circuit.a + self.circuit.b, self.c))
        self.transition(eq(self.circuit.b, self.circuit.a.next()))
        self.transition(eq(self.c, self.circuit.b.next()))

    def wg(self: FiboStep, args: Tuple[int, int]):
        a_value, b_value = args
        self.assign(self.circuit.a, F(a_value))
        self.assign(self.circuit.b, F(b_value))
        self.assign(self.c, F(a_value + b_value))

class Fibonacci(Circuit):
    def setup(self: Fibonacci):
        self.a: Queriable = self.forward("a")
        self.b: Queriable = self.forward("b")

        self.fibo_step = self.step_type(FiboStep(self, "fibo_step"))

        self.pragma_num_steps(11)

    def trace(self: Fibonacci, args: Any):
        self.add(self.fibo_step, (1, 1))
        a = 1
        b = 2
        for i in range(1, 11):
            self.add(self.fibo_step, (a, b))
            prev_a = a
            a = b
            b += prev_a

fibo = Fibonacci()
fibo_witness = fibo.gen_witness(None)
fibo.halo2_mock_prover(fibo_witness)
```

This is explained in more detail in the tutorial, but you can see already how concise and clear it is.


## Getting Started

### Read the tutorial

All located in the [tutorial](https://github.com/privacy-scaling-explorations/chiquito/tree/main/tutorials) folder.

### Run the tutorial locally

Follow [Part 2: Quick Start](https://github.com/privacy-scaling-explorations/chiquito/blob/main/tutorials/tutorial_pt2.ipynb) of the `tutorial` folder.

### Writing a chiquito circuit in your project

To use chiquito in Python, just need to install it with pip:

```bash
pip install chiquito
```

To use chiquito in Rust (TODO)

## Build from source

Chiquito is built in Rust. First [install Rust](https://www.rust-lang.org/tools/install). Then clone this repo and enter the repo directory.

```bash
git clone https://github.com/privacy-scaling-explorations/chiquito
cd chiquito
```

Then to build Python chiquito with maturin

```bash
python -m venv .env
source .env/bin/activate
pip install -r requirements.txt
maturin develop
```

# Testing and Links

**API documentation**: `cargo doc --no-deps --package chiquito --open`

Also auto-published here for the latest commit to main: [apidocs.pecadorplonkish.xyz/](apidocs.pecadorplonkish.xyz/)

# Licenses

MIT OR Apache-2.0
