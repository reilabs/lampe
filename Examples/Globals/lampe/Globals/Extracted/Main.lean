-- Generated by lampe

import Globals.Extracted.Types
import Lampe

open Lampe

namespace Extracted

nr_def «FOO»<>() -> Field {
    42 : Field
}

nr_def «FOOS»<>() -> [Field; 2] {
    [(@FOO<> as λ() → Field)(), #fAdd((@FOO<> as λ() → Field)(), 1 : Field) : Field]
}

nr_def «main»<>() -> Field {
    #arrayIndex((@FOOS<> as λ() → [Field; 2])(), #cast(1 : Field) : u32) : Field;
}


def Main.env := Lampe.Env.mk [«main», «FOO», «FOOS»] []