use crate::hasher::BinaryHasher;
use crate::permute::permute;

pub struct Skyscraper {}

impl BinaryHasher<Field> for Skyscraper {
    fn hash(a: Field, b: Field) -> Field {
        let x = permute([a, b]);
        x[0] + a
    }
}
