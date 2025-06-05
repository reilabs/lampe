use super::utils::bytes::to_le_bytes;
use crate::utils::bytes::from_le_bytes;
use crate::utils::{sbox, as_array};

pub fn bar(a: Field) -> Field {
    let bytes: [u8; 32] = to_le_bytes(a);
    let mut new_left: [u8; 16] = [0; 16];
    let mut new_right: [u8; 16] = [0; 16];

    for i in 0..16 {
        new_left[i] = sbox(bytes[i]);
    }
    for i in 0..16 {
        new_right[i] = sbox(bytes[16 + i]);
    }

    let mut new_bytes = new_right.as_slice();

    for elem in new_left {
        new_bytes = new_bytes.push_back(elem);
    }

    let new_bytes_array: [u8; 32] = as_array(new_bytes);

    from_le_bytes(new_bytes_array)
}
