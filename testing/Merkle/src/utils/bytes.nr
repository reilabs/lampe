use crate::utils::bits::to_le_bits;

// NOTE: hacky workaround
pub fn to_le_bytes(self: Field) -> [u8; 32] {
    let bits = to_le_bits(self);
    let mut bytes: [u8; 32] = [0; 32];

    for i in 0..32 {
        bytes[i] = (bits[8 * i] as u8)
            + 2 * (bits[8 * i + 1] as u8)
            + 4 * (bits[8 * i + 2] as u8)
            + 8 * (bits[8 * i + 3] as u8)
            + 16 * (bits[8 * i + 4] as u8)
            + 32 * (bits[8 * i + 5] as u8)
            + 64 * (bits[8 * i + 6] as u8)
            + 128 * (bits[8 * i + 7] as u8);
    }

    bytes
}

// NOTE: adapted from stdlib
pub fn from_le_bytes(bytes: [u8; 32]) -> Field {
    let mut v = 1;
    let mut result = 0;

    for i in 0..32 {
        result += (bytes[i] as Field) * v;
        v = v * 256;
    }
    result
}
