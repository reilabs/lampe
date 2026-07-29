import Stdlib.Collections.BoundedVec.Methods
import Stdlib.Cmp
import Stdlib.Convert

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.25»

/-!
Trait-method specs for `BoundedVec`.

These are public-facing entry points (e.g. `Eq::eq`, `From::from`) whose implementations live in
the extracted stdlib. We provide a first version of their specs here; proofs are TODO.
-/

theorem eq_trait_spec {p T MaxLen self other}
    {t_eq : «std-1.0.0-beta.25::cmp::Eq».hasImpl env h![] T}
    {t_eq_f :
      ∀ a b,
        STHoare p env ⟦⟧ (Lampe.Stdlib.Cmp.Eq.eq h![] T h![] h![] h![a, b])
          (fun r : Bool => ⟦r ↔ a = b⟧)} :
    STHoare p env ⟦⟧
      (Lampe.Stdlib.Cmp.Eq.eq h![] (bvTp T MaxLen) h![] h![] h![self, other])
      (fun r : Bool => ⟦r ↔ (len self = len other ∧ embed self = embed other)⟧) := by
  resolve_trait
  -- The extracted implementation compares lengths, then (in the constrained branch —
  -- `is_unconstrained` is modelled as `false`) compares the first `len` elements through a
  -- mutable `eq` accumulator. Note it only inspects *active* elements, so the spec is stated
  -- in terms of `embed`, not the whole `storage`.
  steps
  by_cases hlen : self.2.1 = other.2.1
  ·
    -- length matches: run the element-comparison loop.
    apply STHoare.ite_intro_of_true (by
      show decide (Builtin.indexTpl self Member.head.tail = Builtin.indexTpl other Member.head.tail) = true
      change decide (self.2.1 = other.2.1) = true
      simp [hlen])
    steps
    · exact ()
    apply STHoare.ite_intro_of_false (by rfl)
    steps
    loop_inv nat fun i _ _ => ∃∃v, [eq ↦ ⟨.bool, v⟩] ⋆
      (v = ((embed self).take i = (embed other).take i))
    · sl
      simp
    · simp
    · intro i _ ihi
      steps
      apply STHoare.ite_intro
      · intro hlt
        steps [t_eq_f]
        rotate_left
        · exact ()
        rename (_ = true) = _ => hinv
        rename _ ↔ _ => helem
        simp only [decide_eq_true_eq] at hlt
        have hi32 : i < 4294967296 := lt_trans ihi (BitVec.isLt MaxLen)
        have hlt' : i < (len self).toNat := by
          simpa [BitVec.lt_def, Nat.mod_eq_of_lt hi32] using hlt
        have hlenN : (len other).toNat = (len self).toNat := by
          show (other.2.1).toNat = (self.2.1).toNat
          rw [hlen]
        have hi_self : i < (embed self).length := by
          rw [embed_length_eq_min_len_toNat]; exact lt_min hlt' ihi
        have hi_other : i < (embed other).length := by
          rw [embed_length_eq_min_len_toNat, hlenN]; exact lt_min hlt' ihi
        simp only [Lens.modify, Option.get_some, Bool.and_eq_true, eq_iff_iff] at hinv ⊢
        rw [List.take_add_one, List.take_add_one,
          List.getElem?_eq_getElem hi_self, List.getElem?_eq_getElem hi_other]
        simp only [Option.toList_some]
        rw [←List.concat_eq_append, ←List.concat_eq_append, List.concat_inj]
        have helem' : op_rhs_0 = true ↔ (embed self)[i]'hi_self = (embed other)[i]'hi_other := by
          simpa [embed, active, storage, List.getElem_take, List.Vector.get_eq_get_toList,
            Builtin.CastTp.cast, Nat.mod_eq_of_lt hi32] using helem
        exact and_congr hinv helem'
      · intro hge
        steps
        rename (_ = true) = _ => hinv
        simp only [decide_eq_false_iff_not, BitVec.not_lt] at hge
        have hi32 : i < 4294967296 := lt_trans ihi (BitVec.isLt MaxLen)
        have hge' : (len self).toNat ≤ i := by
          simpa [BitVec.le_def, Nat.mod_eq_of_lt hi32] using hge
        have hlenN : (len other).toNat = (len self).toNat := by
          show (other.2.1).toNat = (self.2.1).toNat
          rw [hlen]
        have h1 : (embed self).length ≤ i := by
          rw [embed_length_eq_min_len_toNat]; exact le_trans (Nat.min_le_left _ _) hge'
        have h2 : (embed other).length ≤ i := by
          rw [embed_length_eq_min_len_toNat, hlenN]; exact le_trans (Nat.min_le_left _ _) hge'
        rw [List.take_of_length_le h1, List.take_of_length_le h2] at hinv
        rw [List.take_of_length_le (Nat.le_succ_of_le h1), List.take_of_length_le (Nat.le_succ_of_le h2)]
        exact hinv
    steps
    rename_i v hv
    rename (_ = true) = _ => hfin
    have h1 : (embed self).length ≤ MaxLen.toNat := by
      rw [embed_length_eq_min_len_toNat]; exact Nat.min_le_right _ _
    have h2 : (embed other).length ≤ MaxLen.toNat := by
      rw [embed_length_eq_min_len_toNat]; exact Nat.min_le_right _ _
    rw [List.take_of_length_le h1, List.take_of_length_le h2] at hfin
    subst hv
    rw [hfin]
    exact ⟨fun h => ⟨hlen, h⟩, fun ⟨_, h⟩ => h⟩
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
