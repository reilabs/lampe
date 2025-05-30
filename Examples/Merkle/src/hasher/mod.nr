pub trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}
