import Lampe

open Lampe

namespace Extracted

nr_struct_def Skyscraper<> {
    state : [Field; 2]
}

nr_def «SIGMA»<>() -> Field {
    9915499612839321149637521777990102151350674507940716049588462388200839649614 : Field
}

nr_def «RC»<>() -> [Field; 8] {
    [-4058822530962036113558957735524994411356374024839875405476791844324326516925 : Field, 5852100059362614845584985098022261541909346143980691326489891671321030921585 : Field, -4840154698573742532565501789862255731956493498174317200418381990571919688651 : Field, 71577923540621522166602308362662170286605786204339342029375621502658138039 : Field, 1630526119629192105940988602003704216811347521589219909349181656165466494167 : Field, 7807402158218786806372091124904574238561123446618083586948014838053032654983 : Field, -8558681900379240296346816806663462402801546068866479372657894196934284905006 : Field, -4916733727805245440019875123169648108733681133486378553671899463457684353318 : Field]
}

nr_def «Skyscraper»::«permute»<>(self : &Skyscraper<>) -> Unit {
    (*(self) as Skyscraper<>).state = (@permute<> as λ([Field; 2]) → [Field; 2])((#readRef(self) : Skyscraper<> as Skyscraper<>).state);
}

nr_def «square»<>(a : Field) -> Field {
    #fMul(#fMul(a, a) : Field, (@SIGMA<> as λ() → Field)()) : Field;
}

nr_def «rl»<>(u : u8) -> u8 {
    let top_bit = #uShr(u, 7 : u8) : u8;
    #uOr(#uShl(u, 1 : u8) : u8, top_bit) : u8;
}

nr_def «rotate_left»<>(u : u8, N : u8) -> u8 {
    let mut result = u;
    for _? in 0 : u8 .. N {
            result = (@rl<> as λ(u8) → u8)(result);
    };
    result;
}

nr_def «compress»<>(l : Field, r : Field) -> Field {
    let x = (@permute<> as λ([Field; 2]) → [Field; 2])([l, r]);
    #fAdd(#arrayIndex(x, #cast(0 : Field) : u32) : Field, l) : Field;
}

nr_def «sgn0»<>(self : Field) -> u1 {
    #cast(self) : u1;
}

nr_def «Skyscraper»::«new»<>(iv : [u8; 32]) -> Skyscraper<> {
    let felt = (@std::field::Field::from_le_bytes<32 : 32> as λ([u8; 32]) → Field)(iv);
    Skyscraper<> { [0 : Field, felt] };
}

nr_def «sbox»<>(v : u8) -> u8 {
    let x1 = #uNot(v) : u8;
    let x2 = (@rotate_left<> as λ(u8, u8) → u8)(x1, 1 : u8);
    let x3 = (@rotate_left<> as λ(u8, u8) → u8)(v, 2 : u8);
    let x4 = (@rotate_left<> as λ(u8, u8) → u8)(v, 3 : u8);
    let x5 = #uAnd(#uAnd(x2, x3) : u8, x4) : u8;
    let x6 = (@rotate_left<> as λ(u8, u8) → u8)(x5, 1 : u8);
    #uXor(v, x6) : u8;
}

nr_def «to_le_bits»<>(self : Field) -> [u1; 256] {
    let mut val = self;
    let mut bits = [0 : u1 ; 256];
    for i in 0 : u32 .. 256 : u32 {
            bits[#cast(i) : u32] = (@sgn0<> as λ(Field) → u1)(val);
        if #uEq(#arrayIndex(bits, #cast(i) : u32) : u1, 0 : u1) : bool {
                val = #fDiv(val, 2 : Field) : Field;
        } else {
                val = #fDiv(#fSub(val, 1 : Field) : Field, 2 : Field) : Field;
        };
    };
    bits;
}

nr_def «permute»<>(s : [Field; 2]) -> [Field; 2] {
    let π0 = `(#arrayIndex(s, #cast(0 : Field) : u32) : Field, #arrayIndex(s, #cast(1 : Field) : u32) : Field);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(0 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@bar<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(1 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@bar<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(2 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(3 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(4 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@bar<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(5 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@bar<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(6 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, #arrayIndex((@RC<> as λ() → [Field; 8])(), #cast(7 : Field) : u32) : Field) : Field, l);
    let l = π0.0;
    let r = π0.1;
    let π0 = `(#fAdd(r, (@square<> as λ(Field) → Field)(l)) : Field, l);
    let l = π0.0;
    let r = π0.1;
    [l, r];
}

nr_def «main»<>(a : Field) -> Field {
    a;
}

nr_def «as_array»<>(self : [u8]) -> [u8; 32] {
    let mut array = [0 : u8 ; 32];
    for i in 0 : u32 .. 32 : u32 {
            array[#cast(i) : u32] = #sliceIndex(self, #cast(i) : u32) : u8;
    };
    array;
}

nr_def «bar»<>(a : Field) -> Field {
    let bytes = (@to_le_bytes<> as λ(Field) → [u8; 32])(a);
    let mut new_left = [0 : u8 ; 16];
    let mut new_right = [0 : u8 ; 16];
    for i in 0 : u32 .. 16 : u32 {
            new_left[#cast(i) : u32] = (@sbox<> as λ(u8) → u8)(#arrayIndex(bytes, #cast(i) : u32) : u8);
    };
    for i in 0 : u32 .. 16 : u32 {
            new_right[#cast(i) : u32] = (@sbox<> as λ(u8) → u8)(#arrayIndex(bytes, #cast(#uAdd(16 : u32, i) : u32) : u32) : u8);
    };
    let mut new_bytes = #arrayAsSlice(new_right) : [u8];
        let ζi0 = new_left;
        for ζi1 in 0 : u32 .. #arrayLen(ζi0) : u32 {
                let elem = #arrayIndex(ζi0, #cast(ζi1) : u32) : u8;
                new_bytes = #slicePushBack(new_bytes, elem) : [u8];
        };
    let new_bytes_array = (@as_array<> as λ([u8]) → [u8; 32])(new_bytes);
    (@from_le_bytes<> as λ([u8; 32]) → Field)(new_bytes_array);
}

nr_def «to_le_bytes»<>(self : Field) -> [u8; 32] {
    let bits = (@to_le_bits<> as λ(Field) → [u1; 256])(self);
    let mut bytes = [0 : u8 ; 32];
    for i in 0 : u32 .. 32 : u32 {
            bytes[#cast(i) : u32] = #uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#cast(#arrayIndex(bits, #cast(#uMul(8 : u32, i) : u32) : u32) : u1) : u8, #uMul(2 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 1 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(4 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 2 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(8 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 3 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(16 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 4 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(32 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 5 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(64 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 6 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(128 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 7 : u32) : u32) : u32) : u1) : u8) : u8) : u8;
    };
    bytes;
}

nr_def «from_le_bytes»<>(bytes : [u8; 32]) -> Field {
    let mut v = 1 : Field;
    let mut result = 0 : Field;
    for i in 0 : u32 .. 32 : u32 {
            result = #fAdd(result, #fMul(#cast(#arrayIndex(bytes, #cast(i) : u32) : u8) : Field, v) : Field) : Field;
        v = #fMul(v, 256 : Field) : Field;
    };
    result;
}


def env := Lampe.Env.mk [«SIGMA», «sgn0», «to_le_bytes», «Skyscraper::new», «square», «RC», «Skyscraper::permute», «to_le_bits», «permute», «sbox», «from_le_bytes», «compress», «main», «bar», «rotate_left», «rl», «as_array»] []
