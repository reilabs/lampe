-- Generated by lampe

import «Merkle-0.0.0».Extracted.GeneratedTypes
import Lampe

open Lampe

namespace «Merkle-0.0.0»
namespace Extracted

nr_def «mtree_recover»<H, @N : u32>(idx : [bool; N], p : [Field; N], item : Field) -> Field {
    let mut curr_h = item;
    for i in 0 : u32 .. u@N {
            let dir = #arrayIndex(idx, #cast(i) : u32) : bool;
        let sibling_root = #arrayIndex(p, #cast(i) : u32) : Field;
        if dir {
                curr_h = ((H as hasher::BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(sibling_root, curr_h);
            skip;
        } else {
                curr_h = ((H as hasher::BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(curr_h, sibling_root);
            skip;
        };
    };
    curr_h;
}

nr_def «main»<>(root : Field, proof : [Field; 32], item : Field, idx : [bool; 32]) -> Unit {
    let calculated_root = (@mtree_recover<skyscraper::Skyscraper<>, 32 : u32> as λ([bool; 32], [Field; 32], Field) → Field)(idx, proof, item);
    (@witness::weird_assert_eq<> as λ(Field, Field) → Unit)(root, calculated_root);
}


def Main.env := Lampe.Env.mk [«main», «mtree_recover»] []