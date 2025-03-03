import Lampe

open Lampe

namespace Extracted

nr_struct_def Skyscraper<> {
    state : [Field; 2]
}

-- NOTE: This is not how things are literally extracted, workaround for not dealing with a
-- particular characteristic by avoiding using negatives
nr_def «RC»<>() -> [Field; 8] {
    [17829420340877239108687448009732280677191990375576158938221412342251481978692 : Field,
    5852100059362614845584985098022261541909346143980691326489891671321030921585 : Field,
    17048088173265532689680903955395019356591870902241717143279822196003888806966 : Field,
    71577923540621522166602308362662170286605786204339342029375621502658138039 : Field,
    1630526119629192105940988602003704216811347521589219909349181656165466494167 : Field,
    7807402158218786806372091124904574238561123446618083586948014838053032654983 : Field,
    13329560971460034925899588938593812685746818331549554971040309989641523590611 : Field,
    16971509144034029782226530622087626979814683266929655790026304723118124142299 : Field]
}

nr_def «SIGMA»<>() -> Field {
    9915499612839321149637521777990102151350674507940716049588462388200839649614 : Field
}

nr_def «to_le_bytes»<>(self : Field) -> [u8; 32] {
    let bits = (@to_le_bits<> as λ(Field) → [u1; 256])(self);
    let mut bytes = [0 : u8 ; 32];
    for i in 0 : u32 .. 32 : u32 {
            bytes[#cast(i) : u32] =
            #uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#uAdd(#cast(#arrayIndex(bits, #cast(#uMul(8 : u32,
            i) : u32) : u32) : u1) : u8, #uMul(2 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 :
            u32, i) : u32, 1 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(4 : u8,
            #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 2 : u32) : u32) : u32) :
            u1) : u8) : u8) : u8, #uMul(8 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32,
            i) : u32, 3 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(16 : u8,
            #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 4 : u32) : u32) : u32) :
            u1) : u8) : u8) : u8, #uMul(32 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32,
            i) : u32, 5 : u32) : u32) : u32) : u1) : u8) : u8) : u8, #uMul(64 : u8,
            #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32, i) : u32, 6 : u32) : u32) : u32) :
            u1) : u8) : u8) : u8, #uMul(128 : u8, #cast(#arrayIndex(bits, #cast(#uAdd(#uMul(8 : u32,
            i) : u32, 7 : u32) : u32) : u32) : u1) : u8) : u8) : u8;
    }
    ;
    bytes;
}

nr_def «compress»<>(l : Field, r : Field) -> Field {
    let x = (@permute<> as λ([Field; 2]) → [Field; 2])([l, r]);
    #fAdd(#arrayIndex(x, #cast(0 : Field) : u32) : Field, l) : Field;
}

nr_def «sbox»<>(v : u8) -> u8 {
    #uXor(v, (@rotate_left<> as λ(u8, u8) → u8)(#uAnd(#uAnd((@rotate_left<> as λ(u8, u8) → u8)(#uNot(v) : u8, 1 : u8), (@rotate_left<> as λ(u8, u8) → u8)(v, 2 : u8)) : u8, (@rotate_left<> as λ(u8, u8) → u8)(v, 3 : u8)) : u8, 1 : u8)) : u8;
}

nr_def «from_le_bytes»<>(bytes : [u8; 32]) -> Field {
    let mut v = 1 : Field;
    let mut result = 0 : Field;
    for i in 0 : u32 .. 32 : u32 {
            result = #fAdd(result, #fMul(#cast(#arrayIndex(bytes, #cast(i) : u32) : u8) : Field, v) : Field) : Field;
        v = #fMul(v, 256 : Field) : Field;
    }
    ;
    result;
}

nr_def «rotate_left»<>(u : u8, N : u8) -> u8 {
    let mut result = u;
    for _? in 0 : u8 .. N {
            result = (@rl<> as λ(u8) → u8)(result);
    }
    ;
    result;
}

nr_def «Skyscraper»::«new»<>(iv : [u8; 32]) -> Skyscraper<> {
    let felt = (@std::field::Field::from_le_bytes<32> as λ([u8; 32]) → Field)(iv);
    Skyscraper<> { [0 : Field, felt] };
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
    }
    ;
    bits;
}

nr_def «bar»<>(a : Field) -> Field {
    let bytes = (@to_le_bytes<> as λ(Field) → [u8; 32])(a);
    let mut new_left = [0 : u8 ; 16];
    let mut new_right = [0 : u8 ; 16];
    for i in 0 : u32 .. 16 : u32 {
            new_left[#cast(i) : u32] = (@sbox<> as λ(u8) → u8)(#arrayIndex(bytes, #cast(i) : u32) : u8);
    }
    ;
    for i in 0 : u32 .. 16 : u32 {
            new_right[#cast(i) : u32] = (@sbox<> as λ(u8) → u8)(#arrayIndex(bytes, #cast(#uAdd(16 : u32, i) : u32) : u32) : u8);
    }
    ;
    let mut new_bytes = (@std::array::as_slice<u8, 16> as λ([u8; 16]) → [u8])(new_right);
        let ζi0 = new_left;
        for ζi1 in 0 : u32 .. #arrayLen(ζi0) : u32 {
                let elem = #arrayIndex(ζi0, #cast(ζi1) : u32) : u8;
                new_bytes = #slicePushBack(new_bytes, elem) : [u8];
        }
        ;
    let new_bytes_array = (@as_array<> as λ([u8]) → [u8; 32])(new_bytes);
    (@from_le_bytes<> as λ([u8; 32]) → Field)(new_bytes_array);
}

nr_def «rl»<>(u : u8) -> u8 {
    let top_bit = #uShr(u, 7 : u8) : u8;
    #uOr(#uShl(u, 1 : u8) : u8, top_bit) : u8;
}

nr_def «sgn0»<>(self : Field) -> u1 {
    #cast(self) : u1;
}

nr_def «Skyscraper»::«permute»<>(self : &Skyscraper<>) -> Unit {
    (*(self) as Skyscraper<>).state = (@permute<> as λ([Field; 2]) → [Field; 2])((#readRef(self) : Skyscraper<> as Skyscraper<>).state);
}

-- NOTE: Not extracted exactly like this, had to split things up to get the right assumptions
-- appearing
nr_def «square»<>(a : Field) -> Field {
    let b = #fMul(a, a) : Field;
    #fMul(b, (@SIGMA<> as λ() → Field)()) : Field;
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

nr_def «as_array»<>(self : [u8]) -> [u8; 32] {
    let mut array = [0 : u8 ; 32];
    for i in 0 : u32 .. 32 : u32 {
            array[#cast(i) : u32] = #sliceIndex(self, #cast(i) : u32) : u8;
    }
    ;
    array;
}


def env := Lampe.Env.mk [(«from_le_bytes».name, «from_le_bytes».fn), («sgn0».name, «sgn0».fn), («rl».name, «rl».fn), («RC».name, «RC».fn), («sbox».name, «sbox».fn), («permute».name, «permute».fn), («Skyscraper::permute».name, «Skyscraper::permute».fn), («SIGMA».name, «SIGMA».fn), («compress».name, «compress».fn), («Skyscraper::new».name, «Skyscraper::new».fn), («as_array».name, «as_array».fn), («bar».name, «bar».fn), («to_le_bytes».name, «to_le_bytes».fn), («rotate_left».name, «rotate_left».fn), («square».name, «square».fn), («to_le_bits».name, «to_le_bits».fn)] []
