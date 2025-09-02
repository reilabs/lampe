import Lean
import Lampe

open Lean Elab Term

open Lampe

noir_def foo<I: Type>(x: I) → I := {
  x
}

noir_trait_def Trait1<> [] := {
  method function<>(Self) → Self;
}

noir_trait_def Trait2<> [] := {
  method other_function<>(Self) → Self;
}

noir_trait_impl[trait1Field]<> Trait1<> for Field where [] := {
  noir_def function<>(x: Field) → Field := {
    (#_fAdd returning Field)(x, x)
  }
}

noir_trait_impl[trait2u8]<> Trait2<> for u8 where [] := {
  noir_def other_function<>(_x: u8) → u8 := {
    3: u8
  }
}

noir_trait_impl[trait1u8]<> Trait1<> for u8 where [] := {
  noir_def function<>(x: u8) → u8 := {
    (#_uAdd returning u8)(x, x)
  }
}

noir_def both_trait_call<>(x: Field, y: u8) → Field := {
  let z = ((u8 as Trait1<>)::function<> as λ(u8) -> u8)(y);
  let _t = (foo<u8> as λ(u8) → u8)(z);
  let w = ((Field as Trait1<>)::function<> as λ(Field) → Field)(x);
  (foo<Field> as λ(Field) → Field)(w)
}

def traitEnv : Env := ⟨[], [trait1Field]⟩
def funcEnv : Env := ⟨[foo], []⟩
def traitEnv2 : Env := ⟨[], [trait2u8]⟩
def emptyEnv : Env := ⟨[], []⟩
def finalEnv : Env := ⟨[both_trait_call], [trait1u8]⟩
def containerEnv : Env := finalEnv

def compoundEnv : Env := funcEnv ++ traitEnv ++ emptyEnv ++ containerEnv ++ traitEnv2

example {p} {fieldArg : Fp p}:
    STHoare p compoundEnv ⟦⟧ (both_trait_call.fn.body _ h![] |>.body h![fieldArg, u8Arg])
    fun v => v = 2 * fieldArg := by
  simp only [both_trait_call]
  steps
  step_as (⟦⟧) (fun v => v = (2 * u8Arg : U 8))
  · try_all_traits [] compoundEnv
    steps
    subst_vars
    bv_decide

  steps
  step_as (⟦z = 2 * u8Arg⟧) (fun v => v = (2 * u8Arg : U 8))
  · assumption
  · enter_decl
    steps
    subst_vars
    rfl

  steps
  step_as (⟦z = 2 * u8Arg⟧) (fun v => v = (2 * fieldArg : Fp p))
  · assumption
  · try_all_traits [] compoundEnv
    steps
    subst_vars
    ring

  steps
  step_as (⟦w = 2 * fieldArg⟧) (fun v => v = 2 * fieldArg)
  . assumption
  . subst_vars
    rfl
  . enter_decl
    steps
    subst_vars
    rfl
