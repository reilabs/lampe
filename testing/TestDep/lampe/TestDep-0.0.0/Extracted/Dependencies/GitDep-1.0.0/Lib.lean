-- Generated by lampe

import «TestDep-0.0.0».Extracted.Dependencies.«GitDep-1.0.0».GeneratedTypes
import Lampe

open Lampe

namespace «TestDep-0.0.0»
namespace Extracted
namespace Dependencies
namespace «GitDep-1.0.0»

nr_def «not_equal»<>(x : Field, y : Field) -> bool {
    #fNeq(x, y) : bool;
}

nr_def «hello»<>() -> str<16> {
    "hello-git-dep-v1"
}

nr_def «hello_git_dep_v1»<>() -> str<16> {
    "hello-git-dep-v1"
}

nr_def «test_not_equal»<>() -> Unit {
    #assert((@not_equal<> as λ(Field, Field) → bool)(1 : Field, 2 : Field)) : Unit;
}


def Lib.env := Lampe.Env.mk [«hello_git_dep_v1», «hello», «not_equal», «test_not_equal»] []