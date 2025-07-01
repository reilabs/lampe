use super::sgn0;

// NOTE: hacky workaround
pub fn to_le_bits(self: Field) -> [u1; 256] {
    let mut val = self;
    let mut bits: [u1; 256] = [0; 256];

    for i in 0..256 {
        bits[i] = sgn0(val);
        if bits[i] == 0 {
            val = val / 2;
        } else {
            val = (val - 1) / 2;
        }
    }

    bits
}
