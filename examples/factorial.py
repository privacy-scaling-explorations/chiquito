from chiquito.dsl import Circuit, StepType
from chiquito.cb import eq
from chiquito.util import F
from chiquito.chiquito_ast import Last

MAX_FACTORIAL = 100


class FactorialStep(StepType):
    def setup(self):
        # constrain the next value of x to be the product of the current x and the next i
        self.transition(eq(self.circuit.x * (self.circuit.i + 1), self.circuit.x.next()))
        # constrain the value of n to not change across iterations
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, n_value, i_value, x_value):
        self.assign(self.circuit.n, F(n_value))
        self.assign(self.circuit.i, F(i_value))
        self.assign(self.circuit.x, F(x_value))


class FactorialFinalStep(StepType):
    def setup(self):
        # constrain x to not change on the next step
        self.transition(eq(self.circuit.x, self.circuit.x.next()))
        # constrain n to not change on the next step
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, n_value, x_value):
        self.assign(self.circuit.n, F(n_value))
        self.assign(self.circuit.x, F(x_value))


class PaddingStep(StepType):
    def setup(self):
        # constrain x to not change on the next step
        self.transition(eq(self.circuit.x, self.circuit.x.next()))
        # constrain n to not change on the next step
        self.transition(eq(self.circuit.n, self.circuit.n.next()))

    def wg(self, n_value, x_value):
        self.assign(self.circuit.n, F(n_value))
        self.assign(self.circuit.x, F(x_value))


class Factorial(Circuit):
    def setup(self):
        # n will hold the requested factorial
        self.n = self.forward("n")
        # i will hold the current iteration on the computation
        self.i = self.forward("i")
        # x will hold the current result of the current factorial
        self.x = self.forward("x")

        self.factorial_step = self.step_type(FactorialStep(self, "factorial_step"))
        self.factorial_final_step = self.step_type(FactorialFinalStep(self, "factorial_final_step"))
        self.padding_step = self.step_type(PaddingStep(self, "padding_step"))

        self.pragma_num_steps(MAX_FACTORIAL + 1)
        self.pragma_first_step(self.factorial_step)
        self.pragma_last_step(self.padding_step)

        self.expose(self.x, Last())
        self.expose(self.n, Last())

    def trace(self, n):
        result = 1
        for i in range(0, n + 1):
            # on the first iteration, we don't want to bring the current result to zero
            if i != 0:
                result *= i

            # when we reach the last iteration
            if i == n:
                if i == 0:
                    # add a normal step if factorial of zero was requested
                    # we need this because we constrain the first step to be of this type
                    self.add(self.factorial_step, n, i, result)
                else:
                    # add the final type of step on other cases, to have different constraints on the step
                    self.add(self.factorial_final_step, n, result)
            else:
                # if we are in a middle step, we keep adding the same type
                self.add(self.factorial_step, n, i, result)

        # after all compute steps are added, fill with padding
        while self.needs_padding():
            self.add(self.padding_step, n, result)


factorial = Factorial()
factorial_witness = factorial.gen_witness(0)
factorial.halo2_mock_prover(factorial_witness)
