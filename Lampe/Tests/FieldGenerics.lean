import Lampe

open Lampe

nr_def «A»<>() -> Field {
    4294967297 : Field
}

nr_def «B»<>() -> u32 {
    19 : u32
}

nr_def «foo»<@A : type_fp>() -> Field {
    f@A
}

nr_def «foo2»<@B : type_u 32>() -> u32 {
    u@B
}

nr_def «test»<>() -> Unit {
    -- let a = (@foo<4294967297 : type_fp> as λ() → Field)();
    -- let b = (@foo2<19 : type_u 32> as λ() → u32)();
}

