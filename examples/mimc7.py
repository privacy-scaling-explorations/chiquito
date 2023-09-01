from __future__ import annotations

from chiquito.dsl import Circuit, StepType
from chiquito.cb import eq, table
from chiquito.util import F

from chiquito.rust_chiquito import convert_and_print_ast

from mimc7_constants import ROUND_KEYS

ROUNDS = 91


class Mimc7Constants(Circuit):
    def setup(self):
        self.pragma_num_steps(ROUNDS)
        self.lookup_row = self.fixed("constant row")
        self.lookup_c = self.fixed("constant value")
        self.new_table(table().add(self.lookup_row).add(self.lookup_c))

    def fixed_gen(self):
        for i, round_key in enumerate(ROUND_KEYS):
            self.assign(i, self.lookup_row, F(i))
            self.assign(i, self.lookup_c, F(round_key))


mimc7_constants = Mimc7Constants()
mimc7_constants_json = mimc7_constants.get_ast_json()
convert_and_print_ast(mimc7_constants_json)
