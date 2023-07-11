use uuid::Uuid;

#[allow(clippy::upper_case_acronyms)]
pub type UUID = u128;

pub fn uuid() -> UUID {
    Uuid::now_v1(&[10; 6]).as_u128()
}
