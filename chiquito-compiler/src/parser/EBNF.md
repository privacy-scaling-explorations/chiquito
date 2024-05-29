# Chiquito EBNF

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
inner_state_statement = transition | general_statement | if_state;

(* TRANSITION *)
transition = "->", identifier, (";" | transition_block);
transition_block = "{", transition_statement ,"}";
transition_statement = general_statement | if_transition;

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

(* expression *)

expression = expression, "||", expr1 | expr1;
expr1 = expr1, "&&", expr2 | expr2;
expr2 = expr2, ("==", "!=", "<", ">", "<=", ">="), expr3 | expr3;
expr3 = expr3, "|", expr4 | expr4;
expr4 = expr4, "^", expr5 | expr5;
expr5 = expr5, "&", expr6 | expr6;
expr6 = expr6, ("<<", ">>"), expr7 | expr7;
expr7 = expr7, ("+", "-"), expr8 | expr8;
expr8 = expr8, ("*", "/", "%"), expr9 | expr9;
expr9 = ("-", "!"), terminal | terminal;
terminal = constant | var_with_rotation | "(", expression, ")";

(* TERMINALS *)
constant = integer | hex;
integer = digit,{digit};
hex = "0x", hexdigit, {hexdigit};
identifier = alpha, {alphanum | "_"};
var_with_rotation = identifier, ["'"];

alpha = "A" | "B" | "C" | "D" | "E" | "F" | "G"
       | "H" | "I" | "J" | "K" | "L" | "M" | "N"
       | "O" | "P" | "Q" | "R" | "S" | "T" | "U"
       | "V" | "W" | "X" | "Y" | "Z" | "a" | "b"
       | "c" | "d" | "e" | "f" | "g" | "h" | "i"
       | "j" | "k" | "l" | "m" | "n" | "o" | "p"
       | "q" | "r" | "s" | "t" | "u" | "v" | "w"
       | "x" | "y" | "z" ;
digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
alphanum = alpha | digit;
hexdigit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" | "A" | "B" | "C" | "D" | "E" | "F" | "a" | "b"
       | "c" | "d" | "e" | "f";

```
