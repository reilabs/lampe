-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
import «Lampe».Basic

def exampleModule := noir! {
  fn add1(n) {
    n + 1
  }

  fn adder(n, k) {
    if n == 0 then k else {
      let n = n - 1;
      k + adder(n, k)
    }
  }

  fn lt_fallback(x, y) {
      let num_bytes = ((as_u32(field::modulus_num_bits()) + 7) / 8);
      let x_bytes = field::Field::to_le_bytes(x, num_bytes);
      let y_bytes = field::Field::to_le_bytes(y, num_bytes);
      let mut x_is_lt = false;
      let mut done = false;
      for i in 0 .. num_bytes {
          if (!done) then {
              let x_byte = as_u8(x_bytes[((num_bytes - 1) - i)]);
              let y_byte = as_u8(y_bytes[((num_bytes - 1) - i)]);
              let bytes_match = (x_byte == y_byte);
              if (!bytes_match) then {
                  x_is_lt = (x_byte < y_byte);
                  done = true;
              }
          }
      };
      x_is_lt
  }
}

#reduce exampleModule.decls[2]
