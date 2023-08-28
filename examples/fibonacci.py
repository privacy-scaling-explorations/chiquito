from chiquito.dsl import Circuit, StepType
from chiquito.cb import eq
from chiquito.util import F
from chiquito.chiquito_ast import Last
from chiquito.rust_chiquito import convert_and_print_ast


class FiboFirstStep(StepType):
    def setup(self):
        self.c = self.internal("c")
        self.constr(eq(self.circuit.a, 1))
        self.constr(eq(self.circuit.b, 1))
        self.constr(eq(self.circuit.a + self.circuit.b, self.c))
        self.transition(eq(self.circuit.b, self.circuit.a.next()))
        self.transition(eq(self.c, self.circuit.b.next()))
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, args):
        a_value, b_value, n_value = args
        self.assign(self.circuit.a, F(a_value))
        self.assign(self.circuit.b, F(b_value))
        self.assign(self.c, F(a_value + b_value))
        self.assign(self.circuit.n, F(n_value))


class FiboStep(StepType):
    def setup(self):
        self.c = self.internal("c")
        self.constr(eq(self.circuit.a + self.circuit.b, self.c))
        self.transition(eq(self.circuit.b, self.circuit.a.next()))
        self.transition(eq(self.c, self.circuit.b.next()))
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, args):
        a_value, b_value, n_value = args
        self.assign(self.circuit.a, F(a_value))
        self.assign(self.circuit.b, F(b_value))
        self.assign(self.c, F(a_value + b_value))
        self.assign(self.circuit.n, F(n_value))


class Padding(StepType):
    def setup(self):
        self.transition(eq(self.circuit.b, self.circuit.b.next()))
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, args):
        a_value, b_value, n_value = args
        self.assign(self.circuit.a, F(a_value))
        self.assign(self.circuit.b, F(b_value))
        self.assign(self.circuit.n, F(n_value))


class Fibonacci(Circuit):
    def setup(self):
        self.a = self.forward("a")
        self.b = self.forward("b")
        self.n = self.forward("n")

        self.fibo_first_step = self.step_type(FiboFirstStep(self, "fibo_first_step"))
        self.fibo_step = self.step_type(FiboStep(self, "fibo_step"))
        self.padding = self.step_type(Padding(self, "padding"))

        self.pragma_num_steps(10)
        self.pragma_first_step(self.fibo_first_step)
        self.pragma_last_step(self.padding)

        self.expose(self.b, Last())
        self.expose(self.n, Last())

    def trace(self, n):
        self.add(self.fibo_first_step, (1, 1, n))
        a = 1
        b = 2
        for i in range(1, n):
            self.add(self.fibo_step, (a, b, n))
            prev_a = a
            a = b
            b += prev_a
        while self.needs_padding():
            self.add(self.padding, (a, b, n))


fibo = Fibonacci()
fibo_witness = fibo.gen_witness(7)
fibo.halo2_mock_prover(fibo_witness)
another_fibo_witness = fibo.gen_witness(4)
fibo.halo2_mock_prover(another_fibo_witness)
