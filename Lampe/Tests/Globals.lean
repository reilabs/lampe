import Lampe

open Lampe

nr_def «FOOS»<>() -> [Field; 2] {
    [(@FOO<> as λ() → Field)(), #fAdd((@FOO<> as λ() → Field)(), 1 : Field) : Field]
}

nr_def «FOO»<>() -> Field {
    42 : Field
}
