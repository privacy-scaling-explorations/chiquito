#[derive(Clone)]
pub enum AExprIR<F, V> {
    Const(F),
    Sum(Vec<AExprIR<F, V>>),
    Mul(Vec<AExprIR<F, V>>),
    Neg(Box<AExprIR<F, V>>),
    Pow(Box<AExprIR<F, V>>, u32),

    Query(V),

    // Multiplicative inverse if != 0, any value if = 0
    MI(Box<AExprIR<F, V>>),
}

impl<F: Clone + From<u64>, V: Clone> AExprIR<F, V> {
    pub fn cost(&self, config: &CostConfig) -> u64 {
        match self {
            AExprIR::Const(_) => 0,
            AExprIR::Sum(ses) => ses.iter().map(|se| se.cost(&config)).max().unwrap(),
            AExprIR::Mul(ses) => ses.iter().map(|se| se.cost(&config)).fold(0, |a, c| a + c),
            AExprIR::Neg(se) => se.cost(&config),
            AExprIR::Pow(se, exp) => se.cost(&config) ^ (*exp as u64),
            AExprIR::Query(_) => config.query,
            AExprIR::MI(se) => se.cost(&config) + config.mult_inverse,
        }
    }

    pub fn one_minus(&self) -> AExprIR<F, V> {
        use AExprIR::*;

        Sum(vec![Const(F::from(1u64)), Neg(Box::new((*self).clone()))])
    }

    // OZ -> 1T, 0F
    // anti-booly -> 0T, >0F

    pub fn cast_anti_booly(&self) -> AExprIR<F, V> {
        self.one_minus()
    }

    // is_zero(X) -> 1 - X*MI(X)
    // MI(X) = MIX
    // 0 == X(1 - X*MIX)
    // MIX <- X.inverse()

    pub fn cast_one_zero(&self) -> AExprIR<F, V> {
        use AExprIR::*;

        Mul(vec![self.clone(), MI(Box::new(self.clone()))]).one_minus()
    }
}

pub struct CostConfig {
    pub query: u64,
    pub mult_inverse: u64,
}

impl Default for CostConfig {
    fn default() -> Self {
        Self {
            query: 1,
            mult_inverse: 4,
        }
    }
}
