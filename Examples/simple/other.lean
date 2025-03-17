nr_def «other»::«foo»<>(a : Field) -> Field {
    #fAdd(a, 1 : Field) : Field;
}

nr_def «other»::«bar»<>(a : Field) -> Field {
    #fMul(a, 2 : Field) : Field;
}


def env := Lampe.Env.mk [«other::foo», «other::bar»] []