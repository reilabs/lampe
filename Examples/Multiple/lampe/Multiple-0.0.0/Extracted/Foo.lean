-- Generated by lampe

import «Multiple-0.0.0».Extracted.GeneratedTypes
import Lampe

open Lampe

namespace «Multiple-0.0.0»
namespace Extracted

nr_def «foo»::«foo»<>(x : Field) -> Field {
    #fAdd(x, 1 : Field) : Field;
}


def Foo.env := Lampe.Env.mk [«foo::foo»] []