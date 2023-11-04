from __future__ import annotations

from chiquito.dsl import SuperCircuit, Circuit, StepType
from chiquito.cb import eq, table
from chiquito.util import F

from poseidon_constants import poseidon_constants, poseidon_matrix


class PoseidonConstants(Circuit):
    def setup(self):
        self.row = self.fixed("row")
        self.value = self.fixed("value")
        param_t = self.circuit.n_inputs

        self.constants = poseidon_constants(param_t)
        self.lens = len(self.constants)

        self.pragma_num_steps(self.lens)

        self.table = self.new_table(
            table()
            .add(self.row)
            .add(self.value)
        )

    def fixed_gen(self):
        for i, round_key in enumerate(self.constants[0:self.lens]):
            self.assign(i, self.row, F(i))
            self.assign(i, self.value, F(round_key))


class PoseidonMatrix(Circuit):
    def setup(self):
        self.row = self.fixed("row")
        self.value = self.fixed("value")
        param_t = self.circuit.n_inputs

        self.matrix = poseidon_matrix(param_t)
        self.lens = len(self.matrix)

        self.pragma_num_steps(self.lens)

        self.table = self.new_table(
            table()
            .add(self.row)
            .add(self.value)
        )

    def fixed_gen(self):
        for i, round_key in enumerate(self.matrix[0:self.lens]):
            self.assign(i, self.row, F(i))
            self.assign(i, self.value, F(round_key))


class PoseidonStepFirstRound(StepType):
    def setup(self):
        param_t = self.circuit.param_t

        for i in range(0, param_t):
            if i == 0:
                self.constr(eq(setup_constants[i], setup_x_vec[i]))
            else:
                self.constr(eq(setup_inputs[i - 1] + setup_constants[i], setup_x_vec[i]))

            self.add_lookup(
                self.circuit.constants_table
                .apply(i)
                .apply(setup_constants[i])
            )

            self.constr(
                eq(
                    setup_x_vec[i]
                    * setup_x_vec[i]
                    * setup_x_vec[i]
                    * setup_x_vec[i]
                    * setup_x_vec[i],
                    setup_sboxs[i],
                )
            )

        for i in range(0, param_t):
            m_offset = i * param_t
            for j in range(0, param_t):
                self.add_lookup(
                    self.circuit.params.matrix_table
                    .apply(m_offset + j)
                    .apply(setup_matrix[m_offset + j])
                )

            lc = setup_sboxs[0] * setup_matrix[m_offset]

            for s in range(1, param_t):
                lc = lc + setup_sboxs[s] * setup_matrix[m_offset + s]

            for k in range(param_t, self.circuit.params.lens.n_inputs):
                lc = lc + setup_inputs[k] * setup_matrix[m_offset + k]

            self.constr(eq(lc, setup_outs[i]))
            self.transition(eq(setup_outs[i], setup_inputs[i].next()))

        self.constr(eq(self.circuit.round, 0))
        self.transition(eq(self.circuit.round + 1, self.circuit.round.next()))

    def wg(self):
        pass


class PoseidonStepFullRound(StepType):
    def setup(self):
        pass

    def wg(self):
        pass


class PoseidonStepPartialRound(StepType):
    def setup(self):
        pass

    def wg(self):
        pass


class PoseidonStepLastRound(StepType):
    def setup(self):
        pass

    def wg(self):
        pass


class PoseidonCircuit(Circuit):

    def setup(self):
        n_rounds_p = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
        self.param_t = self.circuit.params.lens.n_inputs + 1
        self.param_f = 8
        self.param_p = n_rounds_p[self.param_t - 2]
        self.param_c = 1

        assert self.circuit.params.lens.n_inputs < self.param_t
        assert self.circuit.params.lens.n_outputs < self.param_t

        self.round = self.forward("round")

        self.step_first_round = self.step_type(PoseidonStepFirstRound(self, "step_first_round"))
        self.step_full_round = self.step_type(PoseidonStepFullRound(self, "step_full_round"))
        self.step_partial_round = self.step_type(PoseidonStepPartialRound(self, "step_partial_round"))
        self.step_last_round = self.step_type(PoseidonStepLastRound(self, "step_last_round"))

        self.pragma_first_step(self.step_first_round)
        self.pragma_last_step(self.step_last_round)
        self.pragma_num_steps(self.param_f + self.param_p)

    def trace(self, values):
        constants = poseidon_constants(self.param_t)


class PoseidonSuperCircuit(SuperCircuit):
    def setup(self):
        lens = self.circuit.lens
        n_inputs = lens.n_inputs
        self.constants_circuit = self.sub_circuit(
            PoseidonConstants(self, n_inputs=n_inputs)
        )
        self.matrix_circuit = self.sub_circuit(
            PoseidonMatrix(self, n_inputs=n_inputs)
        )
        self.poseidon_circuit = self.sub_circuit(
            PoseidonCircuit(self, params={
                "lens": lens,
                "constants_table": self.constants_circuit.table,
                "matrix_table": self.matrix_circuit.table,
            })
        )

    def mapping(self, values):
        self.map(self.poseidon_circuit, values)


class Examples:
    def test_basic(self):
        # Arrange
        values = {
            "inputs": [
                1, 1
            ],
            "n_outputs": 1,
        }
        lens = {
            "n_inputs": 2,
            "n_outputs": 1,
        }

        # Act
        poseidon = PoseidonSuperCircuit(lens=lens)
        witness = poseidon.gen_witness(values)

        # Assert
        poseidon.halo2_mock_prover(witness)


if __name__ == "__main__":
    x = Examples()
    for method in [
        method for method in dir(x)
        if callable(getattr(x, method))
        if not method.startswith("_")
    ]:
        getattr(x, method)()
