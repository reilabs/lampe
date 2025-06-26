import Lampe.Ast

namespace Lampe

/--
A representation of the code (both functions and traits) that are in scope for any given portion of
our representation of a Noir program.

The well-formedness of environments comes from the **Noir compiler**, and Lampe does no additional
consistency checking. We know that the Noir compiler will not admit ambiguity with regards to
in-scope items (functions or traits), and hence this is safe.
-/
structure Env where
  -- All non-trait functions in scope.
  functions : List FunctionDecl

  -- All trait implementations in scope, pairing the name with the implementation details.
  traits : List (Ident × TraitImpl)

namespace Env

-- True if the contents of Γᵢ all exist within Γₒ.
def contains (Γₒ : Env) (Γᵢ : Env) : Prop :=
  (Γᵢ.functions ⊆ Γₒ.functions) ∧ (Γᵢ.traits ⊆ Γₒ.traits)

-- Appends the contents of Γₗ and Γᵣ.
def append (Γₗ : Env) (Γᵣ : Env) : Env :=
  ⟨Γₗ.functions ++ Γᵣ.functions, Γₗ.traits ++ Γᵣ.traits⟩

end Env

instance : Append Env where
  append := Env.append

instance : HasSubset Env where
  Subset left right := right.contains left

-- The following namespace contains lemmas that are necessary to reason about the composition of
-- our environments when using proofs across multiple libraries.
--
-- Note that they are all tagged with `@[simp]` to be made available to the simplifier for ease of
-- use.
namespace Env

@[simp]
lemma functions_append {Γₗ Γᵣ : Env} : (Γₗ ++ Γᵣ).functions = Γₗ.functions ++ Γᵣ.functions := by
  rfl

@[simp]
lemma traits_append {Γₗ Γᵣ : Env} : (Γₗ ++ Γᵣ).traits = Γₗ.traits ++ Γᵣ.traits := by
  rfl

@[trans]
lemma subset_trans {Γ₁ Γ₂ Γ₃ : Env} : Γ₁ ⊆ Γ₂ → Γ₂ ⊆ Γ₃ → Γ₁ ⊆ Γ₃ := by
  rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  constructor
  . trans Γ₂.functions
    repeat assumption
  . trans Γ₂.traits
    repeat assumption

@[simp]
lemma subset_refl {Γ : Env} : Γ ⊆ Γ := by
  constructor <;> simp

@[simp]
lemma subset_append_left {Γₗ Γᵣ : Env} : Γₗ ⊆ Γₗ ++ Γᵣ := by
  constructor <;> simp

@[simp]
lemma subset_append_right {Γₗ Γᵣ : Env} : Γᵣ ⊆ Γₗ ++ Γᵣ := by
  constructor <;> simp

@[simp]
lemma subset_append_of_subset_left {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γₗ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  rintro ⟨h₁, h₂⟩
  constructor
  . simp [h₁]
  . simp [h₂]

@[simp]
lemma subset_append_of_subset_right {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γᵣ → Γᵢ ⊆ Γₗ ++ Γᵣ := by
  rintro ⟨h₁, h₂⟩
  constructor
  . simp [h₁]
  . simp [h₂]

@[simp]
lemma append_subset_iff {Γ₁ Γ₂ Γ₃ : Env} : Γ₁ ++ Γ₂ ⊆ Γ₃ ↔ Γ₁ ⊆ Γ₃ ∧ Γ₂ ⊆ Γ₃ := by
  constructor
  . intro h
    constructor
    . have := @subset_append_left Γ₁ Γ₂
      apply subset_trans this h
    . have := @subset_append_right Γ₁ Γ₂
      apply subset_trans this h
  . rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    simp only [HAppend.hAppend, Append.append, Env.append]
    simp only [List.append_eq]
    constructor <;> simp_all

@[simp]
lemma subset_mono_left {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γₗ → Γᵢ ++ Γᵣ ⊆ Γₗ ++ Γᵣ := by
  intro h
  apply append_subset_iff.mpr
  constructor
  . have := @subset_append_left Γₗ Γᵣ
    apply subset_trans h this
  . apply subset_append_right

@[simp]
lemma subset_mono_right {Γᵢ Γₗ Γᵣ : Env} : Γᵢ ⊆ Γᵣ → Γᵣ ++ Γᵢ ⊆ Γₗ ++ Γᵣ := by
  intro h
  apply append_subset_iff.mpr
  constructor
  . apply subset_append_right
  . have := @subset_append_right Γₗ Γᵣ
    apply subset_trans h this

end Env

end Lampe
