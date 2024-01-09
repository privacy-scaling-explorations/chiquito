# Python Syntax

## Constraint builder

One of the most important parts of defining a circuit is the constraints. The basis for writing constraints are arithmetic operations with signals. You use the operators `*`, `+` and `-` with numbers and signals. For example:

`a + 1 * b`

When you need to do a rotation on a signal you can use the operators `.next()`, `prev()` and or `.rot(n)`.  For example:

`a + 1 * b.next()`

 There are several helper functions to define constraints:
 + `cb_and([a1 ... an])`: And operator
 + `cb_or([a1 ... an])`: Or operator
 + `xor(a, b)`: Xor operator
 + `eq(a, b)`: Arithmetic equality.
 + `select(selector, when_true, when_false)`: trinary operator
 + `when(selector, when_true)`:  Logical imply.
 + `unless(selector, when_false)`: Logical imply when !selector.
 + `cb_not(a)`: Not operator.
 + `isz(a)`: Equal to zero.
 + `if_next_step(step_type, a)`: If next step is step_type, implies a.
 + `next_step_must_be(step_type)`: Enforces next step must be step_type.
 + `next_step_must_not_be(step_type)`: Enforces next step must not be step_type.

In the current version of chiquito these operator cannot be combined arbitrarily, there is a solution in the works. For example `cb_and` cannot have operands that are `eq`.

## Defining a step

A chiquito circuit is made of steps, this is how we define steps:

```python=
class AStep(StepType):
	def setup(self):
		# setup: rules about a valid step
	def wg(self, a, b, c):
		# witness generation: set data for a step instance
```

For the setup we need to define constraints that define which step witness is valid and also define the internal signals. For example:

```python=
class AStep(StepType):
	def setup(self):
		self.c = self.internal("c")
```

To access shared signals we can do it with `self.circuit.signal_identifier`.

For the constraints that we can use the method `constr`. For example:

```python=
class AStep(StepType):
	def setup(self):
		self.constr(eq(self.circuit.a, self.circuit.b * 3))
		self.constr(when(self.circuit.a, eq(self.circuit.b, self.c))

# ...
```

The first constraint means that `a` must be equal to `b times 3`. The second that when `a` value is `1` then `b` must be equal to `c`.

When you have a rotation you should use the method `transition`. For example:

```python=
class AStep(StepType):
	def setup(self):
		self.transition(eq(self.circuit.a, self.circuit.b.next() * 3))
		self.transition(when(self.circuit.a, eq(self.circuit.b.next(), self.c))

# ...
```


For the data of one step instance in the `wg` method we must use the `assign` method to assign all signals.

```python=
class AStep(StepType):
	def wg(self, a_val, b_val):
		self.assign(self.circuit.a, a_val)
		self.assign(self.circuit.b, b_val)
		self.assign(self.c, a_val + b_val)

# ...
```

The method `wg` can have any parameters, and do any computation to calculate the assignations. But signals cannot be rotated for assignation, you can only assign the current step.

## Defining the circuit

To put everything together we define the circuit, also with two methods.

```python=
class ACircuit(Circuit):
	def setup(self):
		# Define shared signals and step types used, number of total steps plus more setup configuration.
	def trace(self, arg1, arg2):
		# Define algorithm to create the trace from the input.
```

For the setup we defined shared signals, step types and number of steps in the trace. For example:

```python=
class ACircuit(Circuit):
	def setup(self):
		# shared signals
		self.a = self.forward("a")
		self.b = self.forward("b")
		self.n = self.forward("n")

		# step types
		self.a_step = self.step_type(AStep(self, "a_step"))
		self.b_step = self.step_type(BStep(self, "b_step"))
		self.c_step = self.step_type(CStep(self, "c_step"))

		# number of trace steps
		self.pragma_num_steps(10)

# ...
```

There are many optional things that you can also configure in the circuit setup:

```python=
class ACircuit(Circuit):
	def setup(self):
		self.pragma_first_step(self.a_step)
		self.pragma_last_step(self.b_step)

		self.expose(self.b, Last())
		self.expose(self.n, Last())

# ... 
```

Then, we should define `trace`, this method add step instances or trace steps to create a particular trace. The most important method is `add()`, the first parameter is a step type, and the rest are the parameters to the step type `wg` method. This method adds a trace step

For example:

```python=
class ACircuit(Circuit):
	def trace(self, n):
		self.add(self.a_step, 1, 1, n)
		a = 1
		b = 2
		for i in range(1, n):
			self.add(self.b_step, a, b, n)
			prev_a = a
			a = b
			b += prev_a
		
		while self.needs_padding():
			self.add(self.b_step, a, b, n)

# ... 
```