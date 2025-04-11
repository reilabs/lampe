import Lampe

open Lampe

nr_def foo<>() -> Unit {
    let a = 3 : Field;
}

nr_def bar<>() -> Unit {
    let mut a = 3 : Field;
}

nr_def baz<>() -> Field {
    let mut a = 3 : Field;
    a
}

