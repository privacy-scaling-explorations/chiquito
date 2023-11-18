from __future__ import annotations

from chiquito.dsl import SuperCircuit, Circuit, StepType
from chiquito.cb import eq, table
from chiquito.util import F

from poseidon_constants import poseidon_constants, poseidon_matrix


class PoseidonConstants(Circuit):
    def setup(self):
        self.row = self.fixed("row")
        self.value = self.fixed("value")
        param_t = self.n_inputs

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
        param_t = self.n_inputs

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

        matrix = self.circuit.matrix
        constants = self.circuit.constants
        inputs = self.circuit.inputs
        outs = self.circuit.outs
        sboxs = self.circuit.sboxs
        x_vec = self.circuit.x_vec

        for i in range(0, param_t):
            if i == 0:
                self.constr(eq(constants[i], x_vec[i]))
            else:
                self.constr(eq(inputs[i - 1] + constants[i], x_vec[i]))

            self.add_lookup(
                self.circuit.constants_table
                .apply(i)
                .apply(constants[i])
            )

            self.constr(
                eq(
                    x_vec[i]
                    * x_vec[i]
                    * x_vec[i]
                    * x_vec[i]
                    * x_vec[i],
                    sboxs[i],
                )
            )

        for i in range(0, param_t):
            m_offset = i * param_t
            for j in range(0, param_t):
                self.add_lookup(
                    self.circuit.matrix_table
                    .apply(m_offset + j)
                    .apply(matrix[m_offset + j])
                )

            lc = sboxs[0] * matrix[m_offset]

            for s in range(1, param_t):
                lc = lc + sboxs[s] * matrix[m_offset + s]

            for k in range(param_t, self.circuit.lens["n_inputs"]):
                lc = lc + inputs[k] * matrix[m_offset + k]

            self.constr(eq(lc, outs[i]))
            self.transition(eq(outs[i], inputs[i].next()))

        self.constr(eq(self.circuit.round, 0))
        self.transition(eq(self.circuit.round + 1, self.circuit.round.next()))

    def wg(self, round_values):
        for signal, value in zip(self.circuit.matrix, round_values["matrix_values"]):
            self.assign(signal, F(value))

        for i in range(0, self.circuit.param_t):
            self.assign(self.circuit.constants[i], F(round_values["constant_values"][i]))
            if i < len(round_values["input_values"]):
                self.assign(self.circuit.inputs[i], F(round_values["input_values"][i]))
            else:
                self.assign(self.circuit.inputs[i], F(0))
            self.assign(self.circuit.x_vec[i], F(round_values["x_values"][i]))
            self.assign(self.circuit.sboxs[i], F(round_values["sbox_values"][i]))
            self.assign(self.circuit.outs[i], F(round_values["out_values"][i]))
            self.assign(self.circuit.round, F(round_values["round"]))


class PoseidonStepFullRound(StepType):
    def setup(self):
        param_t = self.circuit.param_t

        matrix = self.circuit.matrix
        constants = self.circuit.constants
        inputs = self.circuit.inputs
        outs = self.circuit.outs
        sboxs = self.circuit.sboxs
        x_vec = self.circuit.x_vec

        for i in range(0, param_t):
            self.constr(eq(inputs[i] + constants[i], x_vec[i]))
            self.constr(eq(
                x_vec[i]
                * x_vec[i]
                * x_vec[i]
                * x_vec[i]
                * x_vec[i],
                sboxs[i],
            ))
            self.add_lookup(
                self.circuit.constants_table
                .apply(self.circuit.round * param_t + i)
                .apply(constants[i]),
            )

        for i in range(0, param_t):
            m_offset = i * param_t
            for j in range(0, param_t):
                self.add_lookup(
                    self.circuit.matrix_table
                    .apply(m_offset * j)
                    .apply(matrix[m_offset + j]),
                )

            lc = sboxs[0] * matrix[m_offset]
            for s in range(1, param_t):
                lc = lc + sboxs[s] * matrix[m_offset + s]

            self.constr(eq(lc, outs[i]))
            self.transition(eq(outs[i], inputs[i].next()))

        self.transition(
            eq(self.circuit.round + 1, self.circuit.round.next())
        )

    def wg(self, round_values):
        for signal, value in zip(
                self.circuit.matrix,
                round_values["matrix_values"]
        ):
            self.assign(signal, F(value))

        for i in range(0, self.circuit.param_t):
            self.assign(self.circuit.constants[i], F(round_values["constant_values"][i]))
            self.assign(self.circuit.inputs[i], F(round_values["input_values"][i]))
            self.assign(self.circuit.x_vec[i], F(round_values["x_values"][i]))
            self.assign(self.circuit.sboxs[i], F(round_values["sbox_values"][i]))
            self.assign(self.circuit.outs[i], F(round_values["out_values"][i]))

        self.assign(self.circuit.round, F(round_values["round"]))


class PoseidonStepPartialRound(StepType):
    def setup(self):
        param_t = self.circuit.param_t
        param_c = self.circuit.param_c

        matrix = self.circuit.matrix
        constants = self.circuit.constants
        inputs = self.circuit.inputs
        outs = self.circuit.outs
        sboxs = self.circuit.sboxs
        x_vec = self.circuit.x_vec

        for i in range(0, param_t):
            self.constr(eq(inputs[i] + constants[i], x_vec[i]))
            self.add_lookup(
                self.circuit.constants_table
                .apply(self.circuit.round * param_t + i)
                .apply(constants[i]),
            )

        for i in range(0, param_c):
            self.constr(
                eq(
                    x_vec[i]
                    * x_vec[i]
                    * x_vec[i]
                    * x_vec[i]
                    * x_vec[i],
                    sboxs[i],
                )
            )

        for i in range(0, param_t):
            m_offset = i * param_t
            for j in range(0, param_t):
                self.add_lookup(
                    self.circuit.matrix_table
                    .apply(m_offset + j)
                    .apply(matrix[m_offset + j]),
                )

            lc = sboxs[0] * matrix[m_offset]
            for s in range(1, param_c):
                lc = lc + sboxs[s] * matrix[m_offset + s]
            for k in range(param_c, param_t):
                lc = lc + x_vec[k] * matrix[m_offset + k]

            self.constr(eq(lc, outs[i]))
            self.transition(eq(outs[i], inputs[i].next()))

        self.transition(
            eq(self.circuit.round + 1, self.circuit.round.next())
        )

    def wg(self, round_values):
        for signal, value in zip(
                self.circuit.matrix,
                round_values["matrix_values"]
        ):
            self.assign(signal, F(value))

        for i in range(0, self.circuit.param_t):
            self.assign(self.circuit.constants[i], F(round_values["constant_values"][i]))
            self.assign(self.circuit.inputs[i], F(round_values["input_values"][i]))
            self.assign(self.circuit.outs[i], F(round_values["out_values"][i]))
            self.assign(self.circuit.x_vec[i], F(round_values["x_values"][i]))

        for i, sbox in enumerate(self.circuit.sboxs[0:self.circuit.param_c]):
            self.assign(sbox, F(round_values["sbox_values"][i]))

        self.assign(self.circuit.round, F(round_values["round"]))


class PoseidonStepLastRound(StepType):
    def setup(self):
        param_t = self.circuit.param_t

        matrix = self.circuit.matrix
        constants = self.circuit.constants
        inputs = self.circuit.inputs
        outs = self.circuit.outs
        sboxs = self.circuit.sboxs
        x_vec = self.circuit.x_vec

        for i in range(0, param_t):
            self.constr(eq(inputs[i] + constants[i], x_vec[i]))
            self.constr(eq(
                x_vec[i]
                * x_vec[i]
                * x_vec[i]
                * x_vec[i]
                * x_vec[i],
                sboxs[i],
            ))
            self.add_lookup(
                self.circuit.constants_table
                .apply(self.circuit.round * param_t + i)
                .apply(constants[i]),
            )

        for i in range(0, param_t):
            m_offset = i * param_t
            for j in range(0, param_t):
                self.add_lookup(
                    self.circuit.matrix_table
                    .apply(m_offset + j)
                    .apply(matrix[m_offset + j])
                )

        for i, out in enumerate(outs[0:self.circuit.lens["n_outputs"]]):
            m_offset = i * param_t
            lc = sboxs[0] * matrix[m_offset]
            for s in range(1, param_t):
                lc = lc + sboxs[s] * matrix[m_offset + s]
            self.constr(eq(lc, out))

    def wg(self, round_values):
        for signal, value in zip(
                self.circuit.matrix,
                round_values["matrix_values"]
        ):
            self.assign(signal, F(value))

        for i in range(0, self.circuit.param_t):
            self.assign(self.circuit.constants[i], F(round_values["constant_values"][i]))
            self.assign(self.circuit.inputs[i], F(round_values["input_values"][i]))
            self.assign(self.circuit.x_vec[i], F(round_values["x_values"][i]))
            self.assign(self.circuit.sboxs[i], F(round_values["sbox_values"][i]))

        for signal, value in zip(
                self.circuit.outs,
                round_values["out_values"]
        ):
            self.assign(signal, F(value))

        self.assign(self.circuit.round, F(round_values["round"]))


class PoseidonCircuit(Circuit):

    def setup(self):
        n_rounds_p = [56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]
        self.param_t = self.lens["n_inputs"] + 1
        self.param_f = 8
        self.param_p = n_rounds_p[self.param_t - 2]
        self.param_c = 1

        assert self.lens["n_inputs"] < self.param_t
        assert self.lens["n_outputs"] < self.param_t

        self.matrix = [self.forward("matrix_" + str(i)) for i in range(0, self.param_t * self.param_t)]
        self.constants = [self.forward("constant_" + str(i)) for i in range(0, self.param_t)]
        self.inputs = [self.forward("input_" + str(i)) for i in range(0, self.param_t)]
        self.outs = [self.forward("output_" + str(i)) for i in range(0, self.param_t)]
        self.sboxs = [self.forward("sbox_" + str(i)) for i in range(0, self.param_t)]
        self.x_vec = [self.forward("x_" + str(i)) for i in range(0, self.param_t)]

        self.round = self.forward("round")

        self.step_first_round = self.step_type(PoseidonStepFirstRound(self, "step_first_round"))
        self.step_full_round = self.step_type(PoseidonStepFullRound(self, "step_full_round"))
        self.step_partial_round = self.step_type(PoseidonStepPartialRound(self, "step_partial_round"))
        self.step_last_round = self.step_type(PoseidonStepLastRound(self, "step_last_round"))

        self.pragma_first_step(self.step_first_round)
        self.pragma_last_step(self.step_last_round)
        self.pragma_num_steps(self.param_f + self.param_p)

    def trace(self, values):
        param_t = self.param_t
        param_c = self.param_c
        param_f = self.param_f
        param_p = self.param_p

        constants = poseidon_constants(param_t)
        constant_values = [F(v) for v in constants]

        matrix = poseidon_matrix(param_t)
        matrix_values = [F(v) for v in matrix]

        inputs = values["inputs"]
        print("[poseidon hash] inputs = ", inputs)

        x_values = []
        for i in range(0, param_t):
            x_value = constant_values[i]
            if i != 0:
                x_value = inputs[i - 1] + constant_values[i]
            x_values.append(x_value)

        sbox_values = []
        for x_value in x_values:
            sbox_values.append(x_value ** 5)

        outputs = []
        for i in range(0, param_t):
            m_offset = i * param_t
            out_value = sbox_values[0] * matrix_values[m_offset]
            for s in range(1, param_t):
                out_value += sbox_values[s] * matrix_values[m_offset + s]
            for k in range(param_t, len(inputs)):
                out_value += inputs[k] * matrix_values[m_offset + k]
            outputs.append(out_value)

        round_values = {
            "input_values": inputs,
            "constant_values": constant_values[0:param_t],
            "matrix_values": matrix_values,
            "x_values": x_values,
            "sbox_values": sbox_values,
            "out_values": outputs,
            "round": F(0),
        }
        self.add(self.step_first_round, round_values)
        inputs = outputs

        for i in range(1, int(param_t / 2) + 1):
            x_values = [
                inputs[j] + constant_values[i * param_t + j]
                for j in range(0, param_t)
            ]
            sbox_values = [x_value ** 5 for x_value in x_values]

            def method(j):
                m_offset = j * param_t
                out_value = sbox_values[0] * matrix_values[m_offset]
                for s in range(1, param_t):
                    out_value += sbox_values[s] * matrix_values[m_offset + s]
                return out_value

            outputs = [
                method(j) for j in range(0, param_t)
            ]
            round_values = {
                "input_values": inputs,
                "constant_values": constant_values[i * param_t:(i + 1) * param_t],
                "matrix_values": matrix_values,
                "x_values": x_values,
                "sbox_values": sbox_values,
                "out_values": outputs,
                "round": F(i),
            }
            self.add(self.step_full_round, round_values)
            inputs = outputs

        for i in range(0, param_p):
            x_values = [
                inputs[j] + constant_values[j + int(i + param_f / 2) * param_t]
                for j in range(0, param_t)
            ]
            sbox_values = [x_value ** 5 for x_value in x_values]

            def method(t):
                m_offset = t * param_t
                out_value = sbox_values[0] * matrix_values[m_offset]
                for s in range(1, param_c):
                    out_value += sbox_values[s] * matrix_values[m_offset + s]
                for k in range(param_c, param_t):
                    out_value += x_values[k] * matrix_values[m_offset + k]
                return out_value

            outputs = [
                method(j) for j in range(0, param_t)
            ]

            round_values = {
                "input_values": inputs,
                "constant_values": constant_values[int(i + param_f / 2) * param_t:int(i + param_f / 2 + 1) * param_t],
                "matrix_values": matrix_values,
                "x_values": x_values,
                "sbox_values": sbox_values,
                "out_values": outputs,
                "round": F(int(i + param_f / 2)),
            }
            self.add(self.step_partial_round, round_values)
            inputs = outputs

        for i in range(0, int(param_f / 2) - 1):
            x_values = [
                inputs[j] + constant_values[(i + int(param_f / 2) + param_p) * param_t + j]
                for j in range(0, param_t)
            ]
            sbox_values = [x_value ** 5 for x_value in x_values]

            def method(j):
                m_offset = j * param_t
                out_value = sbox_values[0] * matrix_values[m_offset]
                for s in range(1, param_t):
                    out_value += sbox_values[s] * matrix_values[m_offset + s]
                return out_value

            outputs = [
                method(j) for j in range(0, param_t)
            ]
            round_values = {
                "input_values": inputs,
                "constant_values": constant_values[(i + int(param_f / 2) + param_p) * param_t:(i + int(param_f / 2) + param_p + 1) * param_t],
                "matrix_values": matrix_values,
                "x_values": x_values,
                "sbox_values": sbox_values,
                "out_values": outputs,
                "round": F(i + int(param_f / 2) + param_p),
            }
            self.add(self.step_full_round, round_values)
            inputs = outputs

        x_values = [
            inputs[i] + constant_values[i + (param_p + param_f - 1) * param_t]
            for i in range(0, param_t)
        ]
        sbox_values = [x_value ** 5 for x_value in x_values]

        def method(i):
            m_offset = i * param_t
            out_value = sbox_values[0] * matrix_values[m_offset]
            for s in range(1, param_t):
                out_value += sbox_values[s] * matrix_values[m_offset + s]
            return out_value

        outputs = [
            method(i)
            for i in range(0, values["n_outputs"])
        ]
        print("[poseidon hash] outputs = ", outputs)

        round_values = {
            "input_values": inputs,
            "constant_values": constant_values[(param_p + param_f - 1) * param_t:(param_p + param_f) * param_t],
            "matrix_values": matrix_values,
            "x_values": x_values,
            "sbox_values": sbox_values,
            "out_values": outputs,
            "round": F(param_p + param_f - 1),
        }
        self.add(self.step_last_round, round_values)


class PoseidonSuperCircuit(SuperCircuit):
    def setup(self):
        lens = {
            "n_inputs": 6,
            "n_outputs": 1,
        }
        n_inputs = lens["n_inputs"]
        self.constants_circuit = self.sub_circuit(
            PoseidonConstants(self, n_inputs=n_inputs)
        )
        self.matrix_circuit = self.sub_circuit(
            PoseidonMatrix(self, n_inputs=n_inputs)
        )
        self.poseidon_circuit = self.sub_circuit(
            PoseidonCircuit(
                self,
                lens=lens,
                constants_table=self.constants_circuit.table,
                matrix_table=self.matrix_circuit.table,
            )
        )

    def mapping(self, values):
        self.map(self.poseidon_circuit, values)


class Examples:
    def test_basic(self):
        # Arrange
        values = {
            "inputs": [
                1, 1, 1, 1, 1, 1
            ],
            "n_outputs": 1,
        }
        lens = {
            "n_inputs": 6,
            "n_outputs": 1,
        }

        # Act
        poseidon = PoseidonSuperCircuit()
        witness = poseidon.gen_witness(values)

        # print(list(witness.values())[0])
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
