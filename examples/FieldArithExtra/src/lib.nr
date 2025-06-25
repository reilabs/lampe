
/// Adds all of the provided `elems` together and returns the result, or zero if
/// the input has no items.
pub fn multi_add<let N: u32>(elems: [Field; N]) -> Field {
  let mut result = 0;
  for i in 0..N {
    result += elems[i];
  }
  result
}

/// Multiplies all of the provided `elems` together and returns the result, or
/// 1 if the input has no items.
pub fn multi_mul<let N: u32>(elems: [Field; N]) -> Field {
  let mut result = 1;
  for i in 0..N {
    result += elems[i];
  }
  result
}

