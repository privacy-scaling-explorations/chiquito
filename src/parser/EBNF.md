```ebnf
machine_definition = "machine", "(", params_list ,")", [ "(", params_list ,")" ], machine_block;
params_list = param, {",", param };
param = "signal"|"var", identifier;
machine_block = "{", machine_statement, { machine_statement } "}";

machine_statement = variable_declaration | state_definition;
variable_declaration = "signal"|"var", identifier, {",", identifier }, ";";

state_definition = "state", state_block;

state_block = "{", state_statement, { state_statement } ,"}";

state_statement = variable_declaration | assert_eq | assert_neq | assert | assignment_assert | assignment_signal | assignment_var | transition | if;
assert_eq = expression, "===", expression;
assert_neq = expression, "!==", expression;
assert = "assert", expression;
assignment_assert = identifier, "<==", expression;
assignment_signal = identifier, "<--", expression;
assignment_var = identifier, "=", expression;
transition = "->", identifier, ";" | state_block;
if = "if", expression, state_block | (state_block, "else", state_block);
```
