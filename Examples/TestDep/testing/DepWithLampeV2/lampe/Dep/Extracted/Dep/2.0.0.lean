-- Generated by lampe

import Lampe

open Lampe

namespace Dep
namespace «2.0.0»
namespace Extracted
namespace Dep
namespace «2.0.0»

nr_def «not_equal»<>(x : Field, y : Field) -> bool {
    #fNeq(x, y) : bool;
}

nr_def «test_not_equal»<>() -> Unit {
    #assert((@not_equal<> as λ(Field, Field) → bool)(1 : Field, 2 : Field)) : Unit;
    skip;
}


def env := Lampe.Env.mk [«test_not_equal», «not_equal»] []