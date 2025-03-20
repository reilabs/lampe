import Lampe

open Lampe

nr_def «A»<>() -> Field {
    4294967297 : Field
}

nr_def «foo»<@A : type_fp>() -> Field {
    f@A
}

nr_def «test»<>() -> Field {
    let a = (@foo<4294967297 : type_fp> as λ() → Field)();
    a
}

