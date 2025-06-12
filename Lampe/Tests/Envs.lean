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

nr_def simple_trait_call<I> (x : I) -> I {
  let y = ((I as Trait1<>)::function<> as λ(I) → I)(x);
  (@foo<I> as λ(I) → I)(y)
}

nr_def other_trait_call<> (x : u8) -> u8 {
  let y = ((u8 as Trait2<>)::other_function<> as λ(u8) → u8)(x);
  (@foo<u8> as λ(u8) → u8)(y)
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

def compoundEnv : Env := funcEnv ++ traitEnv ++ emptyEnv ++ traitEnv2 ++ finalEnv
def simpleEnv : Env := ⟨[foo, both_trait_call], [trait1Field, trait2u8, trait1u8]⟩
def newEnv := simpleEnv

set_option trace.Lampe.Traits true

example {p} {arg : Tp.denote p Tp.field} :
    STHoare p compoundEnv ⟦⟧ (simple_trait_call.fn.body _ h![.field] |>.body h![arg])
    fun v => v = 2 * arg := by
  simp only [simple_trait_call]
  steps

  enter_block_as (⟦⟧) (fun v => v = 2 * arg)
  · try_all_traits [] simpleEnv -- enter_trait [] simpleEnv
    steps
    subst_vars
    ring

  steps
  enter_block_as (⟦y = 2 * arg⟧) (fun v => v = 2 * arg)
  · assumption
  · enter_decl
    steps
    subst_vars
    rfl

  steps
  subst_vars
  rfl

example {p} :
    STHoare p compoundEnv ⟦⟧ (other_trait_call.fn.body _ h![] |>.body h![arg])
    fun v => v = (3 : U 8) := by
  simp only [other_trait_call]
  steps
  enter_block_as (⟦⟧) (fun v => v = (3 : U 8))
  · try_all_traits [] compoundEnv -- enter_trait [] simpleEnv
    steps
    subst_vars; rfl

  steps
  enter_block_as (⟦y = 3⟧) (fun v => v = 3)
  · assumption
  · enter_decl
    steps
    subst_vars
    rfl

  steps
  subst_vars
  rfl

example {p} {fieldArg : Fp p}:
    STHoare p compoundEnv ⟦⟧ (both_trait_call.fn.body _ h![] |>.body h![fieldArg, u8Arg])
    fun v => v = 2 * fieldArg := by
  simp only [both_trait_call]
  steps
  enter_block_as (⟦⟧) (fun v => v = 2 * u8Arg)
  · try_all_traits [] compoundEnv -- enter_trait [] simpleEnv
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
  · try_all_traits [] compoundEnv -- enter_trait [] simpleEnv
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
