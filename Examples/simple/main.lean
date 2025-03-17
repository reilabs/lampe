nr_def «asdf»<>() -> Unit {
    #assert(#fEq((@main<> as λ(Field, Field) → Field)(1 : Field, 2 : Field), 5 : Field) : bool) : Unit;
}

nr_def «main»<>(x : Field, y : Field) -> Field {
    #fAdd((@other::bar<> as λ(Field) → Field)(x), (@other::foo<> as λ(Field) → Field)(y)) : Field;
}


def env := Lampe.Env.mk [«asdf», «main»] []