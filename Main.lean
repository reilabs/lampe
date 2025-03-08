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

nr_def «test_main»<>() -> Unit {
    (@main<> as λ(Field, Field) → Unit)(1 : Field, 2 : Field);
}

nr_def «main»<>(x : Field, y : Field) -> Unit {
    #assert(#fNeq(x, y) : bool) : Unit;
}

nr_def «mtree_recover»<H, @N : 32>(idx : [bool; N], p : [Field; N], item : Field) -> Field {
    let mut curr_h = item;
    for i in 0 : u32 .. @N {
            let dir = #arrayIndex(idx, #cast(i) : u32) : bool;
        let sibling_root = #arrayIndex(p, #cast(i) : u32) : Field;
        if dir {
                curr_h = ((_ as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(sibling_root, curr_h);
        } else {
                curr_h = ((_ as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(curr_h, sibling_root);
        };
    };
    curr_h;
}


def env := Lampe.Env.mk [(«main».name, «main».fn), («mtree_recover».name, «mtree_recover».fn), («test_main».name, «test_main».fn)] [impl_405]