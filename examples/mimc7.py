from __future__ import annotations
from chiquito.dsl import SuperCircuit, Circuit, StepType
from chiquito.cb import eq, table
from chiquito.util import F

from mimc7_constants import ROUND_KEYS

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
        for i, round_key in enumerate(ROUND_KEYS):
            self.assign(i, self.lookup_row, F(i))
            self.assign(i, self.lookup_c, F(round_key))


class Mimc7FirstStep(StepType):
    def setup(self):
        self.xkc = self.internal("xkc")
        self.y = self.internal("y")

        self.constr(eq(self.circuit.x + self.circuit.k + self.circuit.c, self.xkc))
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
            self.circuit.constants_table.apply(self.circuit.row).apply(self.circuit.c)
        )

    def wg(self, x_value, k_value, c_value, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.circuit.c, F(c_value))
        self.assign(self.circuit.row, F(row_value))

        xkc_value = F(x_value + k_value + c_value)
        self.assign(self.xkc, F(xkc_value))
        self.assign(self.y, F(xkc_value**7))


class Mimc7Step(StepType):
    def setup(self):
        self.xkc = self.internal("xkc")
        self.y = self.internal("y")

        self.constr(eq(self.circuit.x + self.circuit.k + self.circuit.c, self.xkc))
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
            self.circuit.constants_table.apply(self.circuit.row).apply(self.circuit.c)
        )

    def wg(self, x_value, k_value, c_value, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.circuit.c, F(c_value))
        self.assign(self.circuit.row, F(row_value))

        xkc_value = F(x_value + k_value + c_value)
        self.assign(self.xkc, F(xkc_value))
        self.assign(self.y, F(xkc_value**7))


class Mimc7LastStep(StepType):
    def setup(self):
        self.out = self.internal("out")

        self.constr(eq(self.circuit.x + self.circuit.k, self.out))

    def wg(self, x_value, k_value, _, row_value):
        self.assign(self.circuit.x, F(x_value))
        self.assign(self.circuit.k, F(k_value))
        self.assign(self.circuit.row, F(row_value))
        self.assign(self.out, F(x_value + k_value))


class Mimc7Circuit(Circuit):
    def setup(self):
        self.x = self.forward("x")
        self.k = self.forward("k")
        self.c = self.forward("c")
        self.row = self.forward("row")

        self.mimc7_first_step = self.step_type(Mimc7FirstStep(self, "mimc7_first_step"))
        self.mimc7_step = self.step_type(Mimc7Step(self, "mimc7_step"))
        self.mimc7_last_step = self.step_type(Mimc7LastStep(self, "mimc7_last_step"))

        self.pragma_first_step(self.mimc7_first_step)
        self.pragma_last_step(self.mimc7_last_step)
        self.pragma_num_steps(ROUNDS + 2 - 1)

    def trace(self, x_in_value, k_value):
        c_value = F(ROUND_KEYS[0])
        x_value = F(x_in_value)
        row_value = F(0)

        self.add(self.mimc7_first_step, x_value, k_value, c_value, row_value)

        for i in range(1, ROUNDS):
            row_value += F(1)
            x_value += F(k_value + c_value)
            x_value = F(x_value**7)
            c_value = F(ROUND_KEYS[i])

            self.add(self.mimc7_step, x_value, k_value, c_value, row_value)

        row_value += F(1)
        x_value += F(k_value + c_value)
        x_value = F(x_value**7)

        self.add(self.mimc7_last_step, x_value, k_value, c_value, row_value)


class Mimc7SuperCircuit(SuperCircuit):
    def setup(self):
        self.mimc7_constants = self.sub_circuit(Mimc7Constants(self))
        self.mimc7_circuit = self.sub_circuit(
            Mimc7Circuit(self, constants_table=self.mimc7_constants.lookup_table)
        )

    def mapping(self, x_in_value, k_value):
        self.map(self.mimc7_circuit, x_in_value, k_value)


mimc7 = Mimc7SuperCircuit()
mimc7_super_witness = mimc7.gen_witness(F(1), F(2))
# for key, value in mimc7_super_witness.items():
#     print(f"{key}: {str(value)}")
mimc7.halo2_mock_prover(mimc7_super_witness)
