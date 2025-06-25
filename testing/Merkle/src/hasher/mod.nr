pub trait BinaryHasher<F> {
    fn hash(a: F, b: F) -> F;
}

pub trait Hasher {
      fn finish(self) -> Field;
      fn write(&mut self, input: Field);
}
