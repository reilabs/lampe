import Stdlib.Collections.BoundedVec.Methods
import Stdlib.Cmp
import Stdlib.Convert

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.14»

/-!
Trait-method specs for `BoundedVec`.

These are public-facing entry points (e.g. `Eq::eq`, `From::from`) whose implementations live in
the extracted stdlib. We provide a first version of their specs here; proofs are TODO.
-/

theorem eq_trait_spec {p T MaxLen self other}
    {t_eq : «std-1.0.0-beta.14::cmp::Eq».hasImpl env h![] T}
    {t_eq_f :
      ∀ a b,
        STHoare p env ⟦⟧ (Lampe.Stdlib.Cmp.Eq.eq h![] T h![] h![] h![a, b])
          (fun r : Bool => ⟦r ↔ a = b⟧)} :
    STHoare p env ⟦⟧
      (Lampe.Stdlib.Cmp.Eq.eq h![] (bvTp T MaxLen) h![] h![] h![self, other])
      (fun r : Bool => ⟦r ↔ (len self = len other ∧ storage self = storage other)⟧) := by
  resolve_trait
  -- The extracted implementation is:
  -- `if self.1 == other.1 then (self.0 == other.0) else false`.
  steps
  by_cases hlen : self.2.1 = other.2.1
  ·
    -- length matches: reduce to array equality on storage.
    apply STHoare.ite_intro_of_true (by
      show decide (Builtin.indexTpl self Member.head.tail = Builtin.indexTpl other Member.head.tail) = true
      change decide (self.2.1 = other.2.1) = true
      simp [hlen])
    steps [Lampe.Stdlib.Cmp.Eq.array_eq_pure_spec (T := T) (N := MaxLen) (a := storage self) (b := storage other)
      (t_eq := t_eq) (t_eq_f := t_eq_f)]
    rename_i v hv
    refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, h⟩ => ?_⟩
    · exact hlen
    · exact (hv.mp h)
    · exact hv.mpr h
  ·
    -- length mismatch: return `false`.
    apply STHoare.ite_intro_of_false (by
      show decide (Builtin.indexTpl self Member.head.tail = Builtin.indexTpl other Member.head.tail) = false
      change decide (self.2.1 = other.2.1) = false
      simp [hlen])
    steps
    rename_i v hv
    refine ⟨fun h => ?_, fun ⟨h, _⟩ => ?_⟩
    · exact absurd h (by simp [hv])
    · exact absurd h hlen

theorem from_trait_spec {p T MaxLen Len array}
    (hbounded : Len.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      (Lampe.Stdlib.Convert.«from» h![T.array Len] (bvTp T MaxLen) h![] h![] h![array])
      (fun r => wellFormed r ∧ embed r = array.toList) := by
  resolve_trait
  -- The extracted impl delegates to `BoundedVec::from_array`.
  steps [from_array_spec (p := p) (T := T) (MaxLen := MaxLen) (Len := Len) (array := array) hbounded]
  rename_i r hpost
  rcases hpost with ⟨hwf, hembed⟩
  exact ⟨hwf, by simp [hembed]⟩

end Lampe.Stdlib.Collections.BoundedVec
