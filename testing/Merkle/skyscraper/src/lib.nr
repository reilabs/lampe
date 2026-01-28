pub mod bar;
pub mod components;
pub mod globals;
pub mod permute;

pub struct Skyscraper;

impl hasher::BinaryHasher<Field> for Skyscraper {
    fn hash(a: Field, b: Field) -> Field {
        let s = permute::permute([a, b]);
        s[0] + a
    }
}
