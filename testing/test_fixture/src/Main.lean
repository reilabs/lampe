nr_def «test_main»<>() -> Unit {
    (@main<> as λ(Field, Field) → Unit)(1 : Field, 2 : Field);
}

nr_def «main»<>(x : Field, y : Field) -> Unit {
    #assert(#fNeq(x, y) : bool) : Unit;
}


def env := Lampe.Env.mk [(«test_main».name, «test_main».fn), («main».name, «main».fn)] []