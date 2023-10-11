from __future__ import annotations

from chiquito.chiquito_ast import Last
from chiquito.dsl import SuperCircuit, Circuit, StepType
from chiquito.cb import eq, table
from chiquito.expr import Const, to_expr
from chiquito.util import F

from mimc7_constants import ROUND_CONSTANTS

ROUNDS = 91


# It's the best practice to wrap all values in F, even though the `assign` functions automatically wrap values in F.
class Mimc7Constants(Circuit):
    def setup(self):
        self.pragma_num_steps(ROUNDS)
        self.lookup_row = self.fixed("constant row")
        self.lookup_c = self.fixed("constant value")
        self.lookup_table = self.new_table(
            table().add(self.lookup_row).add(self.lookup_c)
        )

    def fixed_gen(self):
        for i, round_key in enumerate(ROUND_CONSTANTS):
            self.assign(i, self.lookup_row, F(i))
            self.assign(i, self.lookup_c, F(round_key))


class Mimc7FirstStep(StepType):
    def setup(self):
        self.xkc = self.internal("xkc")
        self.y = self.internal("y")
        self.c = self.internal("c")

        self.constr(eq(self.circuit.enable_lookup, 0))
        self.constr(eq(self.circuit.x + self.circuit.k + self.c, self.xkc))
        self.constr(
            eq(
                self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc,
                self.y,
            )
        )

        self.transition(eq(self.y, self.circuit.x.next()))
        self.transition(eq(self.circuit.k, self.circuit.k.next()))
        self.transition(eq(self.circuit.row, 0))
        self.transition(eq(self.circuit.row + 1, self.circuit.row.next()))

        self.add_lookup(
            self.circuit.constants_table.apply(self.circuit.row).apply(self.c)
        )

    def wg(self, x_value, k_value, c_value, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.c, F(c_value))
        self.assign(self.circuit.row, F(row_value))

        xkc_value = F(x_value + k_value + c_value)
        self.assign(self.xkc, F(xkc_value))
        self.assign(self.y, F(xkc_value ** 7))
        self.assign(self.circuit.enable_lookup, F(0))


class Mimc7Step(StepType):
    def setup(self):
        self.xkc = self.internal("xkc")
        self.y = self.internal("y")
        self.c = self.internal("c")

        self.constr(eq(self.circuit.enable_lookup, 0))
        self.constr(eq(self.circuit.x + self.circuit.k + self.c, self.xkc))
        self.constr(
            eq(
                self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc
                * self.xkc,
                self.y,
            )
        )

        self.transition(eq(self.y, self.circuit.x.next()))
        self.transition(eq(self.circuit.k, self.circuit.k.next()))
        self.transition(eq(self.circuit.row + 1, self.circuit.row.next()))

        self.add_lookup(
            self.circuit.constants_table.apply(self.circuit.row).apply(self.c)
        )

    def wg(self, x_value, k_value, c_value, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.c, F(c_value))
        self.assign(self.circuit.row, F(row_value))

        xkc_value = F(x_value + k_value + c_value)
        self.assign(self.xkc, F(xkc_value))
        self.assign(self.y, F(xkc_value ** 7))
        self.assign(self.circuit.enable_lookup, F(0))


class Mimc7LastStep(StepType):
    def setup(self):
        self.constr(eq(self.circuit.x + self.circuit.k, self.circuit.out))
        self.constr(eq(self.circuit.enable_lookup, 1))

    def wg(self, x_value, k_value, _, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.circuit.row, F(row_value))
        self.assign(self.circuit.out, F(x_value + k_value))
        self.assign(self.circuit.enable_lookup, F(1))


class Mimc7Circuit(Circuit):
    def setup(self):
        self.x = self.forward("x")
        self.k = self.forward("k")
        self.row = self.forward("row")
        self.out = self.forward("out")
        self.enable_lookup = self.forward("enable_lookup")

        self.mimc7_first_step = self.step_type(Mimc7FirstStep(self, "mimc7_first_step"))
        self.mimc7_step = self.step_type(Mimc7Step(self, "mimc7_step"))
        self.mimc7_last_step = self.step_type(Mimc7LastStep(self, "mimc7_last_step"))

        self.pragma_first_step(self.mimc7_first_step)
        self.pragma_last_step(self.mimc7_last_step)
        self.pragma_num_steps((ROUNDS + 2 - 1) * 2)

        self.hashes_table = self.new_table(
            table().add(self.enable_lookup).add(self.out)
        )

    def trace(self, x_values, k_value):
        for x_value in x_values:
            self.trace_single(x_value, k_value)

    def trace_single(self, x_in_value, k_value):
        c_value = F(ROUND_CONSTANTS[0])
        x_value = F(x_in_value)
        row_value = F(0)

        self.add(self.mimc7_first_step, x_value, k_value, c_value, row_value)

        for i in range(1, ROUNDS):
            row_value += F(1)
            x_value += F(k_value + c_value)
            x_value = F(x_value ** 7)
            c_value = F(ROUND_CONSTANTS[i])

            self.add(self.mimc7_step, x_value, k_value, c_value, row_value)

        row_value += F(1)
        x_value += F(k_value + c_value)
        x_value = F(x_value ** 7)

        self.add(self.mimc7_last_step, x_value, k_value, c_value, row_value)


class MtipStep(StepType):
    def setup(self):
        self.index = self.internal("index")
        self.result = self.internal("result")
        self.constr(eq(self.index * (1 - self.index), 0))

        # TODO: soundness lookup input

        self.transition(eq(self.result, self.circuit.hash.next()))

        self.add_lookup(self.circuit.hashes_table.apply(1).apply(self.result))

    def wg(self, index, result, hash):
        self.assign(self.index, F(index))
        self.assign(self.result, F(result))
        self.assign(self.circuit.hash, F(hash))


class MtipLastStep(StepType):
    def setup(self):
        self.constr(eq(self.circuit.hash, self.circuit.root))

    def wg(self, root, hash):
        self.assign(self.circuit.hash, F(hash))
        self.assign(self.circuit.root, F(root))


class MtipCircuit(Circuit):
    def setup(self):
        self.hash = self.forward("hash")
        self.root = self.forward("root")

        self.step = self.step_type(MtipStep(self, "step"))
        self.last_step = self.step_type(MtipLastStep(self, "last_step"))

        self.pragma_last_step(self.last_step)
        self.expose(self.root, Last())

    def trace(self, path_indices, hashes):
        levels = 20
        for i in range(0, levels):
            self.add(self.step, path_indices[i], hashes[i + 1], hashes[i])

        self.add(self.last_step, hashes[levels])


class Mimc7MultiSuperCircuit(SuperCircuit):
    def setup(self):
        self.mimc7_constants = self.sub_circuit(Mimc7Constants(self))
        self.mimc7_circuit = self.sub_circuit(
            Mimc7Circuit(self, constants_table=self.mimc7_constants.lookup_table)
        )
        self.mtip_circuit = self.sub_circuit(
            MtipCircuit(self, hashes_table=self.mimc7_circuit.hashes_table)
        )

    def mapping(self, k_value, leaf, siblings, path_indices):
        x_values = []
        hashes = [leaf]
        for i in range(0, 20):
            input_1 = ((siblings[i] - hashes[i]) * path_indices[i]) + hashes[i]
            input_2 = ((hashes[i] - siblings[i]) * path_indices[i]) + siblings[i]

            x_values.push(input_1 + input_2)
            result = self.mimc7(input_1 + input_2, k_value)
            hashes[i + 1] = result

        self.map(self.mimc7_circuit, x_values, k_value)
        self.map(self.mtip_circuit, leaf, siblings, path_indices, hashes)

    def mimc7(self, x_in_value, k_value):
        c_value = F(ROUND_CONSTANTS[0])
        x_value = F(x_in_value)
        row_value = F(0)

        for i in range(1, ROUNDS):
            row_value += F(1)
            x_value += F(k_value + c_value)
            x_value = F(x_value ** 7)
            c_value = F(ROUND_CONSTANTS[i])

        row_value += F(1)
        x_value += F(k_value + c_value)
        x_value = F(x_value ** 7)

        return x_value + k_value


mimc7 = Mimc7MultiSuperCircuit()
mimc7_super_witness = mimc7.gen_witness([F(1), F(2)], F(1))
print(mimc7_super_witness)
# for key, value in mimc7_super_witness.items():
#     print(f"{key}: {str(value)}")
mimc7.halo2_mock_prover(mimc7_super_witness)
