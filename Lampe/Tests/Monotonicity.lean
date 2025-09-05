-- This test ensures that proofs over our language semantics are monotonic. In other words, that a
-- proof for some environment Γ₁ is valid for any environment Γ₂ where Γ₁ ⊆ Γ₂.

import Lampe
import Lean

open Lampe
open Lean Elab Term

-- We turn on pretty-printing of the goal state in our proofs. This makes it easier to follow what
-- is actually going on with our current proof state.
set_option Lampe.pp.Expr true

-- We start by defining a very simple function and its isolated environment.
noir_def return_three<>() → Field := {
  3: Field
}

def SimpleEnvReturnThree : Env := ⟨[return_three], []⟩

-- We can then show that this function behaves correctly in accordance with its specification by
-- proving a theorem that says it returns three unconditionally.
theorem return_three_correct
    {p : Prime}
  : STHoare
      p
      SimpleEnvReturnThree
      (⟦⟧)
      (return_three.call h![] h![])
      fun out => out = (3 : Fp p) := by
  enter_decl
  simp only [return_three]
  steps []
  subst_vars
  rfl

-- Next we define another very simple function and its isolated environment.
noir_def add_one<>(n: Field) → Field := {
  (#_fAdd returning Field)(n, 1: Field)
}

def SimpleEnvAddOne : Env := ⟨[add_one], []⟩

-- We can then show that this function behaves correctly in accordance with its specification by
-- proving a theorem that says it returns a value that is one greater than its input.
theorem add_one_correct
    {p : Prime}
    {arg : Fp p}
  : STHoare
      p
      SimpleEnvAddOne
      (⟦⟧)
      (add_one.call h![] h![arg])
      fun out => out = arg + 1 := by
  enter_decl
  simp only [add_one]
  steps []
  subst_vars
  rfl

-- Finally, we define a slightly more complex function that will rely on the proofs of correctness
-- for both of the above functions.
noir_def add_one_to_three_and_n<>(n: Field) → Field := {
  let three = (return_three<> as λ() → Field)();
  let added_one = (add_one<> as λ(Field) → Field)(three);
  (#_fAdd returning Field)(added_one, n)
}

-- We define the environment here using two different styles. The first one is _manual_, adding the
-- function entries directly. This technique is guaranteed to result in slow proofs as the
-- environment grows, but demonstrates that it is possible to reason about monotonicity even if
-- somebody does use this style.
def ComposedEnvManual : Env := ⟨[return_three, add_one_to_three_and_n, add_one], []⟩

-- We now prove the correctness of our combined function using this environment.
theorem add_one_to_three_and_n_correct_in_manual_env
    {p : Prime}
    {arg : Fp p}
  : STHoare
      p
      ComposedEnvManual
      (⟦⟧)
      (add_one_to_three_and_n.call h![] h![arg])
      fun out => out = arg + 3 + 1 := by
  enter_decl
  steps

  apply STHoare.letIn_intro
  apply STHoare.is_mono
  rotate_left
  apply return_three_correct

  intro
  steps
  apply STHoare.letIn_intro
  apply STHoare.is_mono
  rotate_left
  apply STHoare.consequence_frame_left
  apply add_one_correct

  sl

  intro
  steps
  subst_vars
  . conv =>
      rhs
      rw [add_comm, ←add_assoc, add_comm, ←add_assoc]

  all_goals apply And.intro <;> {intro a ha; fin_cases ha <;> simp [ComposedEnvManual]}

-- The second style of environment is one constructed via _concatenation_. This is our recommended
-- method, as its usage leads to simple discharge of goals and much faster proofs.
def ComposedEnvConcat : Env := ⟨[add_one_to_three_and_n], []⟩
                            ++ SimpleEnvAddOne
                            ++ SimpleEnvReturnThree

-- Let's prove the correctness of our combined function using this other environment. It is mostly
-- the same as the above proof, so comments are left in the body only where things differ in
-- important ways.
theorem add_one_to_three_and_n_correct_in_concat_env
    {p : Prime}
    {arg : Fp p}
  : STHoare
      p
      ComposedEnvConcat
      (⟦⟧)
      (add_one_to_three_and_n.call h![] h![arg])
      fun out => out = arg + 3 + 1 := by
  enter_decl
  steps [
    add_one_correct,
    return_three_correct
  ]
  subst_vars
  abel

-- Let's also define a trait, with implementations on `Field` and `u8`, to check whether trait impl
-- search interacts properly with monotonicity.

noir_trait_def Default<> [] := {
  method default<>() -> Self;
}

noir_trait_impl[DefaultForField]<> Default<> for Field where [] := {
  noir_def default<>() → Field := {
    42: Field
  }
}

noir_trait_impl[DefaultForu8]<> Default<> for u8 where [] := {
  noir_def default<>() → u8 := {
    255: u8
  }
}

-- This environment contains both a generic function over the trait, and two implementations of the
-- trait.
def TraitsEnv : Env := ⟨[], [DefaultForField, DefaultForu8]⟩

-- We can start by proving that each trait implementation returns the correct values. We start with
-- the impl for `Field`.
theorem default_field_correct
    {p: Prime}
  : STHoare
      p
      TraitsEnv
      (⟦⟧)
      (Default.default h![] .field h![] h![] h![])
      fun out => out = (42 : Fp p) := by
  resolve_trait
  steps
  apply_assumption

-- We then also prove an equivalent theorem for the `u8` implementation of the trait.
theorem default_u8_correct
    {p: Prime}
  : STHoare
      p
      TraitsEnv
      (⟦⟧)
      (Default.default h![] (.u 8) h![] h![] h![])
      fun out => out = (255 : BitVec 8) := by
  resolve_trait
  steps
  apply_assumption

-- With both of our trait implementations proved to do the right thing, let's define a function that
-- uses both trait implementations at once, along with an environment for it and the traits.
noir_def call_trait_impls_and_add<>(n: Field) → Field := {
  let _default_u8 = ((u8 as Default<>)::default<> as λ() → u8)();
  let default_field = ((Field as Default<>)::default<> as λ() → Field)();
  (#_fAdd returning Field)(default_field, n)
}

def FieldTraitEnvWithCall : Env := ⟨[call_trait_impls_and_add], []⟩ ++ TraitsEnv

-- We then prove that this combined function does the right thing, even with the added complexity of
-- monotonic reasoning _and_ traits.
theorem call_trait_impls_and_add_correct
    {p : Prime}
    {n : Fp p}
  : STHoare
      p
      FieldTraitEnvWithCall
      (⟦⟧)
      (call_trait_impls_and_add.call h![] h![n])
      fun out => out = n + 42 := by
  enter_decl
  steps [default_u8_correct, default_field_correct]
  subst_vars
  abel

-- Now we know that things compose with trait search, let's go one level deeper to really be assured
-- that the monotonicity works. We define a function that uses both already-composed environments,
-- along with its accompanying env.
noir_def combining_everything<>(n: Field) → Field := {
  let added_4 = (add_one_to_three_and_n<> as λ(Field) → Field)(n);
  let added_42 = (call_trait_impls_and_add<> as λ(Field) → Field)(n);
  (#_fAdd returning Field)(added_4, added_42)
}

def EverythingEnv : Env := ⟨[combining_everything], []⟩
                        ++ FieldTraitEnvWithCall
                        ++ ComposedEnvConcat

-- Finally we show that this function works as expected in that environment.
theorem combining_everything_correct
    {p : Prime}
    {n : Fp p}
  : STHoare
      p
      EverythingEnv
      (⟦⟧)
      (combining_everything.call h![] h![n])
      fun out => out = (n + 4) + (n + 42) := by
  enter_decl
  steps [add_one_to_three_and_n_correct_in_concat_env, call_trait_impls_and_add_correct]
  subst_vars
  ring_nf
