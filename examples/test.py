from chiquito.dsl import Circuit, StepType, SuperCircuit
from chiquito.cb import eq, table
from chiquito.util import F

MAX_SIZE = 10


class CircuitOneStep(StepType):
    def setup(self):
        self.constr(eq(self.circuit.b, self.circuit.a + 1))
        self.transition(eq(self.circuit.a * self.circuit.b, self.circuit.a.next()))

    def wg(self, a_value, b_value):
        self.assign(self.circuit.a, F(a_value))
        self.assign(self.circuit.b, F(b_value))


class CircuitOne(Circuit):
    """
    example circuit that will create a lookup table that will be looked by another circuit
    """

    def setup(self):
        # define circuit signals
        self.a = self.forward("a")
        self.b = self.forward("b")

        # define necessary steps
        self.step = self.step_type(CircuitOneStep(self, "step"))

        # define circuit constraints
        self.pragma_num_steps(MAX_SIZE)
        self.pragma_first_step(self.step)
        self.pragma_last_step(self.step)

        # define lookup table
        self.results_table = self.new_table(
            table()
            .add(self.a)
            .add(self.b)
        )

    def trace(self):
        a = 1
        b = 2
        for i in range(1, MAX_SIZE + 1):
            self.add(self.step, a, b)
            a *= b
            b = a + 1


class CircuitTwoStep(StepType):
    def setup(self):
        # define internal signals
        self.a = self.internal("a")
        self.b = self.internal("b")

        # add lookup constraint
        self.add_lookup(
            self.circuit.lookup_table
            # .apply(self.a)
            # .apply(self.b)
            # TODO-FIX: hardcoded values below should make this constraint fail
            .apply(99)
            .apply(99)
        )

    def wg(self, a_value, b_value):
        self.assign(self.a, F(a_value))
        self.assign(self.b, F(b_value))


class CircuitTwo(Circuit):
    """
    example circuit that will use a step that is constrained to have values that exist on
    a lookup table of another circuit
    """

    def setup(self):
        # define necessary steps
        self.step = self.step_type(CircuitTwoStep(self, "step"))

        # define circuit constraints
        self.pragma_num_steps(MAX_SIZE)
        self.pragma_first_step(self.step)
        self.pragma_last_step(self.step)

    def trace(self):
        # initial values are different from CircuitOne,
        # if we use real signals in the lookup constraint (CircuitTwoStep)
        # it should fail
        a = 2
        b = 3
        for i in range(1, MAX_SIZE + 1):
            self.add(self.step, a, b)
            a *= b
            b = a + 1


class TestSuperCircuit(SuperCircuit):
    """
    example super-circuit to cross both example circuits above
    """

    def setup(self):
        self.circuit_one = self.sub_circuit(
            CircuitOne(self)
        )
        self.circuit_two = self.sub_circuit(
            CircuitTwo(self, lookup_table=self.circuit_one.results_table)
        )

    def mapping(self):
        self.map(self.circuit_one)
        self.map(self.circuit_two)


class Examples:
    def test_table_lookup(self):
        # instantiate circuit
        super_circuit = TestSuperCircuit()
        # generate witness
        witness = super_circuit.gen_witness()
        # filter the trace of first sub-circuit
        trace_circuit_one = list(witness.values())[0]

        found = False

        # iterate over all step instances
        for step in trace_circuit_one.step_instances:
            # get list of step assignments
            assignments_list = list(step.assignments.values())
            # we are looking to find a matching element
            # we have a hardcoded lookup with those values
            if assignments_list == [99, 99]:
                found = True

        # this assertion verifies that no element was found
        assert not found

        # print(list(witness.values())[0])

        # yet, the prover returns ok
        super_circuit.halo2_mock_prover(witness)

        # print(list(witness.values())[0])

if __name__ == "__main__":
    x = Examples()
    for method in [
        method
        for method in dir(x)
        if callable(getattr(x, method))
        if not method.startswith("_")
    ]:
        getattr(x, method)()
        