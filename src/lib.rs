pub mod ast;
pub mod backend;
pub mod compiler;
pub mod dsl;
pub mod frontend;
pub mod ir;
pub mod stdlib;
mod util;
pub mod wit_gen;


#[cfg(test)]
mod tests {
    use halo2_proofs::halo2curves::bn256::Fr;

    use super::*;
    use crate::ast::{ToExpr, ToField};

    #[test]
    fn test_1() {
        let fr = Fr::from_raw([1, 0, 0, 0]);
        let json = serde_json::to_string(&fr).unwrap();
        println!("{:?}", json);
    }

    #[test]
    fn test_2() {
        let json = "[1, 0, 0, 0]";
        let fr: Fr = serde_json::from_str(json).unwrap();
        let json_2 = serde_json::to_string(&fr).unwrap();
        println!("{:?}", json_2);
    }
}