from chiquito.dsl import Circuit, StepType
from chiquito.cb import eq
from chiquito.util import F
from chiquito.chiquito_ast import Last

MAX_FACTORIAL = 10

"""
|    step_type      |  i  |  x   |
----------------------------------
|  first_step       |  0  |  1   |
|  operation_step   |  1  |  1   |
|  operation_step   |  2  |  2   |
|  operation_step   |  3  |  6   |
|  result_step      |  4  |  24  |
|  result_step      |  4  |  24  |
|  result_step      |  4  |  24  |
        ...
"""


class FirstStep(StepType):
    def setup(self):
        # constrain `i` to zero
        self.constr(eq(self.circuit.i, 0))
        # constrain `x` to one
        self.constr(eq(self.circuit.x, 1))
        # constrain the next `x` to be equal to the current `x`
        self.transition(eq(self.circuit.x, self.circuit.x.next()))

    def wg(self):
        self.assign(self.circuit.i, F(0))
        self.assign(self.circuit.x, F(1))


class OperationStep(StepType):
    def setup(self):
        # constrain i.prev() + 1 == i
        self.transition(eq(self.circuit.i.rot(-1) + 1, self.circuit.i))
        # constrain i + 1 == i.next()
        self.transition(eq(self.circuit.i + 1, self.circuit.i.next()))
        # constrain the next `x` to be the product of the current `x` and the next `i`
        self.transition(
            eq(self.circuit.x * (self.circuit.i + 1), self.circuit.x.next())
        )

    def wg(self, i_value, x_value):
        self.assign(self.circuit.i, F(i_value))
        self.assign(self.circuit.x, F(x_value))


class ResultStep(StepType):
    def setup(self):
        # constrain `x` to not change
        self.transition(eq(self.circuit.x, self.circuit.x.next()))
        # constrain `i` to not change
        self.transition(eq(self.circuit.i, self.circuit.i.next()))

    def wg(self, i_value, x_value):
        self.assign(self.circuit.i, F(i_value))
        self.assign(self.circuit.x, F(x_value))


class Factorial(Circuit):
    def setup(self):
        # `i` holds the current iteration number
        self.i = self.shared("i")
        # `x` holds the current total result
        self.x = self.forward("x")

        self.first_step = self.step_type(FirstStep(self, "first_step"))
        self.operation_step = self.step_type(OperationStep(self, "operation_step"))
        self.result_step = self.step_type(ResultStep(self, "result_step"))

        self.pragma_num_steps(MAX_FACTORIAL + 1)
        self.pragma_first_step(self.first_step)
        self.pragma_last_step(self.result_step)

        self.expose(self.x, Last())
        self.expose(self.i, Last())

    def trace(self, n):
        self.add(self.first_step)
        current_result = 1

        for i in range(1, n + 1):
            current_result *= i
            if i == n:
                # we found the result
                self.add(self.result_step, i, current_result)
            else:
                # more operations need to be done
                self.add(self.operation_step, i, current_result)

        while self.needs_padding():
            # if padding is needed, we propagate final values
            self.add(self.result_step, n, current_result)


class Examples:
    def test_zero(self):
        factorial = Factorial()
        factorial_witness = factorial.gen_witness(0)
        last_assignments = list(
            factorial_witness.step_instances[10].assignments.values()
        )
        assert last_assignments[0] == 0  # i
        assert last_assignments[1] == 1  # x
        factorial.halo2_mock_prover(factorial_witness)

    def test_basic(self):
        factorial = Factorial()
        factorial_witness = factorial.gen_witness(7)
        last_assignments = list(
            factorial_witness.step_instances[10].assignments.values()
        )
        assert last_assignments[0] == 7  # i
        assert last_assignments[1] == 5040  # x
        factorial.halo2_mock_prover(factorial_witness)


if __name__ == "__main__":
    x = Examples()
    for method in [
        method
        for method in dir(x)
        if callable(getattr(x, method))
        if not method.startswith("_")
    ]:
        getattr(x, method)()
