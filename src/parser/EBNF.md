# Chiquito EBNF

Expression and terminals are not included.

```ebnf
grammar = { machine_definition };

(* MACHINE *)
machine_definition = "machine", identifier, "(", params_list ,")", ["(", params_list ,")" ], machine_block;
params_list = param, {",", param };
param = ("signal"|"var"), identifier;
machine_block = "{", machine_statement, { machine_statement }, "}";
machine_statement = variable_declaration | state_definition;

(* STATE *)
state_definition = "state", identifier, state_block;
state_block = "{", state_statement, { state_statement } ,"}";
inner_state_block = "{", inner_state_statement, { inner_state_statement } ,"}";
state_statement = variable_declaration | inner_state_statement;
inner_state_statement = transition | general_statement | if_state;

(* TRANSITION *)
transition = "->", identifier, (";" | transition_block);
transition_block = "{", transition_statement ,"}";
transition_statement = general_statement | if_transition;

(* STATEMENTS *)
general_statement = assert_eq | assert_neq | assert | assignment_assert | assignment_signal | assignment_var;

assert_eq = expression, "===", expression, ";";
assert_neq = expression, "!==", expression, ";";
assert = "assert", expression, ";";
assignment_assert = identifier, "<==", expression, ";";
assignment_signal = identifier, "<--", expression, ";";
assignment_var = identifier, "=", expression, ";";

if_state = "if", expression, (inner_state_block | (inner_state_block, "else", inner_state_block));
if_transition = "if", expression, (transition_block | (transition_block, "else", transition_block));

(* COMMON *)
variable_declaration = ("signal"|"var"), identifier, {",", identifier }, ";";
```
