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

noir_trait_def Trait3<> [] := {
  method other_function<>(Self) → Field;
}

noir_trait_impl[trait3All]<A: Type> Trait3<> for A where [A: Trait1<>] := {
  noir_def other_function<>(_x: A) → Field := {
    5: Field
  }
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

noir_def all_trait_call<>(x: Field, y: u8) → Field := {
  let z = ((u8 as Trait1<>)::function<> as λ(u8) -> u8)(y);
  let _t = (foo<u8> as λ(u8) → u8)(z);
  let w = ((Field as Trait1<>)::function<> as λ(Field) → Field)(x);
  let z = ((Field as Trait3<>)::other_function<> as λ(Field) → Field)(x);
  (foo<Field> as λ(Field) → Field)(w)
}

def traitEnv : Env := ⟨[], [trait1Field]⟩
def funcEnv : Env := ⟨[foo], []⟩
def traitEnv2 : Env := ⟨[], [trait2u8]⟩
def emptyEnv : Env := ⟨[], []⟩
def finalEnv : Env := ⟨[all_trait_call], [trait3All, trait1u8]⟩
def containerEnv : Env := finalEnv

def compoundEnv : Env := funcEnv ++ traitEnv ++ emptyEnv ++ containerEnv ++ traitEnv2

example : STHoare p compoundEnv ⟦⟧ (Trait3.other_function h![] .field h![] h![] h![v]) (fun x: Fp p => x = 5) := by
  resolve_trait
  steps
  assumption

-- The `all_trait_call`-via-`compoundEnv` example was disabled when bumping to v4.29.1:
-- the multi-step `Env.append` chain combined with the new transparency rules
-- (leanprover/lean4#12179 + #12572) causes the elaborator's `whnf` of
-- `STHoare p compoundEnv ⟦⟧ (all_trait_call.call h![] …)` to diverge even with a 20×
-- heartbeat bump. Restore once v4.30+ ships PR #13363's matcher allowlist.
