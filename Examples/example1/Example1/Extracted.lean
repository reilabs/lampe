import Lampe

open Lampe

namespace Test

nr_def «main»<>(x : Field, y : Field) -> Field {
    #fAdd(x, y) : Field;
}


def env := Lampe.Env.mk [(«main».name, «main».fn)] []
