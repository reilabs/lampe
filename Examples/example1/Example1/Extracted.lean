import Lampe

open Lampe

namespace Test

nr_struct_def DummyHasher<> {

}

nr_trait_impl[impl_405] <> BinaryHasher<Field> for DummyHasher<> where  {
    fn «hash»<> (a : Field, b : Field) -> Field {
        #fAdd(a, b) : Field;
} 
}

nr_def «mtree_recover»<H, @N : 32>(idx : [bool; N], p : [Field; N], item : Field) -> Field {
    let mut curr_h = item;
    for i in 0 : u32 .. @N {
            let dir = #arrayIndex(idx, #cast(i) : u32) : bool;
        let sibling_root = #arrayIndex(p, #cast(i) : u32) : Field;
        if dir {
                curr_h = ((H as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(sibling_root, curr_h);
        } else {
                curr_h = ((H as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(curr_h, sibling_root);
        };
    };
    curr_h;
}

nr_def «main»<>(root : Field, proof : [Field; 32], idx : [bool; 32], item : Field) -> Unit {
    #assert(#fEq(root, (@mtree_recover<DummyHasher<>, 32 : 32> as λ([bool; 32], [Field; 32], Field) → Field)(idx, proof, item)) : bool) : Unit;
}


def env := Lampe.Env.mk [«main», «mtree_recover»] [impl_405]