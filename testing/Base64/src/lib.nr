use noir_base64::BASE64_ENCODER;
use noir_base64::BASE64_NO_PAD_ENCODER;

/// Encode with padding -exercises the const-generic arithmetic
/// where `UsePadding = 1` is substituted into the return type formula.
pub fn encode_with_padding<let N: u32>(input: [u8; N]) -> [u8; ((N * 8) / 6) + (((N % 3) % 2) * 3) + (((N % 3) / 2) * 2)] {
    BASE64_ENCODER::encode(input)
}

/// Encode without padding -exercises the `UsePadding = 0` case.
pub fn encode_no_padding<let N: u32>(input: [u8; N]) -> [u8; ((N * 8) / 6) + ((N % 3) % 2) + ((N % 3) / 2)] {
    BASE64_NO_PAD_ENCODER::encode(input)
}
