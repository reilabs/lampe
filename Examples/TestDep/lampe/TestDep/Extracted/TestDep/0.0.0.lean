-- Generated by lampe

import Lampe

open Lampe

namespace TestDep
namespace «0.0.0»
namespace Extracted
namespace TestDep
namespace «0.0.0»

nr_def «main»<>(x : Field, y : Field) -> Unit {
    #assert(#fNeq(x, y) : bool) : Unit;
    skip;
}

nr_def «test_main»<>() -> Unit {
    (@main<> as λ(Field, Field) → Unit)(1 : Field, 2 : Field);
}


def env := Lampe.Env.mk [«test_main», «main»] []