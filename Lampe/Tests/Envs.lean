import Lean
import Lampe

open Lean Elab Term

open Lampe

nr_def foo<I>(x : I) -> I {
    x
}

nr_trait_impl[trait1Field] <> Trait1<> for Field where {
    fn function<>(x : Field) -> Field {
      #fAdd(x, x) : Field
    };
}

nr_trait_impl[trait2u8] <> Trait2<> for u8 where {
    fn other_function<>(_x : u8) -> u8 {
      3 : u8
    };
}

nr_trait_impl[trait1u8] <> Trait1<> for u8 where {
  fn function<>(x : u8) -> u8 {
    #uAdd(x, x) : u8
  }
}

nr_def both_trait_call<> (x : Field, y : u8) -> Field {
  let z = ((u8 as Trait1<>)::function<> as λ(u8) → u8)(y);
  let _t = (@foo<u8> as λ(u8) → u8)(z);
  let w = ((Field as Trait1<>)::function<> as λ(Field) → Field)(x);
  (@foo<Field> as λ(Field) → Field)(w)
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
  enter_block_as (⟦⟧) (fun v => v = 2 * u8Arg)
  · try_all_traits [] compoundEnv
    steps
    subst_vars
    rename_i a
    cases a
    subst_vars; bv_decide

  steps
  enter_block_as (⟦z = 2 * u8Arg⟧) (fun v => v = 2 * u8Arg)
  · assumption
  · enter_decl
    steps
    subst_vars
    rfl

  steps
  enter_block_as (⟦z = 2 * u8Arg⟧) (fun v => v = 2 * fieldArg)
  · assumption
  · try_all_traits [] compoundEnv
    steps
    subst_vars
    ring

  steps
  enter_block_as (⟦z = 2 * u8Arg⟧) (fun v => v = 2 * fieldArg)
  · assumption
  · enter_decl
    steps
    subst_vars
    rfl

  steps
  subst_vars
  rfl
