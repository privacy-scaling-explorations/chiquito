use crate::field::Field;

#[derive(Clone, Copy, Debug)]
pub enum Value<F: Field> {
    Field(F),
    Bool(bool),
}

impl<F: Field> Value<F> {
    pub fn unwrap(&self) -> F {
        use Value::*;

        match self {
            Field(v) => *v,
            Bool(b) => {
                if *b {
                    F::ONE
                } else {
                    F::ZERO
                }
            }
        }
    }

    pub fn get_field(&self) -> Result<F, String> {
        match self {
            Value::Field(v) => Ok(*v),
            _ => Err("it is not a field element".to_string()),
        }
    }

    pub fn get_bool(&self) -> Result<bool, String> {
        match self {
            Value::Bool(v) => Ok(*v),
            _ => Err("it is not a boolean".to_string()),
        }
    }

    pub fn sum(&self, other: &Self) -> Result<Value<F>, String> {
        match self {
            Value::Field(v) => Ok(Value::Field(*v + other.get_field()?)),
            _ => Err("operation not implemented for type".to_string()),
        }
    }

    pub fn sub(&self, other: &Self) -> Result<Value<F>, String> {
        match self {
            Value::Field(v) => Ok(Value::Field(*v + other.get_field()?.neg())),
            _ => Err("operation not implemented for type".to_string()),
        }
    }

    pub fn mul(&self, other: &Self) -> Result<Value<F>, String> {
        match self {
            Value::Field(v) => Ok(Value::Field(*v * other.get_field()?)),
            _ => Err("operation not implemented for type".to_string()),
        }
    }

    pub fn neg(&self) -> Result<Value<F>, String> {
        match self {
            Value::Field(v) => Ok(Value::Field(v.neg())),
            _ => Err("operation not implemented for type".to_string()),
        }
    }

    pub fn eq(&self, other: &Self) -> Result<Value<F>, String> {
        match self {
            Value::Field(v) => Ok(Value::Bool(*v == other.get_field()?)),
            Value::Bool(v) => Ok(Value::Bool(*v == other.get_bool()?)),
        }
    }
}
