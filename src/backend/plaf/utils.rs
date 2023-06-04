use polyexen::plaf::Plaf;
use convert_case::{Case, Casing};

// adapted from polyexen-demo
// keep a version for Chiquito plaf backend that we can maintain independently
pub fn alias_replace(plaf: &mut Plaf) {
    for aliases in plaf
        .columns
        .fixed
        .iter_mut()
        .map(|c| &mut c.aliases)
        .chain(plaf.columns.public.iter_mut().map(|c| &mut c.aliases))
        .chain(plaf.columns.witness.iter_mut().map(|c| &mut c.aliases))
    {
        for alias in aliases.iter_mut() {
            for (before, after) in [
                ("LOOKUP_", "lu."),
                ("lookup", "lu"),
                ("normalize", "norm"),
                ("context", "ctx"),
                ("address", "addr"),
                ("input", "in"),
                ("output", "out"),
                ("inverse", "inv"),
                ("binary", "bin"),
                ("initial", "init"),
                ("difference", "diff"),
                ("first", "fst"),
                // Bytecode
                ("BYTECODE_", "bc."),
                // Bytecode Chiquito
                ("halo2 fixed ", ""),
                ("halo2 advice ", ""),
                ("srcm forward ", "fwd_"),
                ("srcm internal signal ", "int_"),
                ("length", "len"),
                ("value", "val"),
                // EVM
                ("EVM_", "ev."),
                // Exp
                ("EXP_", "ex."),
                ("GADGET_MUL_ADD_", "MulAdd."),
                ("_col", "_c"),
                ("identifier", "id"),
                ("parity_check", "parChe"),
                // Keccak
                ("KECCAK_", "kc."),
                // State
                ("STATE", "st."),
                // CamelCase
                ("0_", "0."),
                ("1_", "1."),
                ("2_", "2."),
                ("3_", "3."),
                ("4_", "4."),
                ("5_", "5."),
                ("6_", "6."),
                ("7_", "7."),
                ("8_", "8."),
                ("9_", "9."),
            ] {
                *alias = alias.replace(before, after);
            }
            *alias = alias.to_case(Case::Camel);
        }
    }
}