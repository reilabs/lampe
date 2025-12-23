import Lampe

/-!
# BitVec Extensions

Mathlib-style extensions for BitVec operations.
-/

open Lampe

instance : Std.Total (fun (x1 : U s) x2 => ¬x1 < x2) := { total := by simp [BitVec.le_total] }

instance : Std.Antisymm (fun (x1 : U s) x2 => ¬x1 < x2) where
  antisymm _ _ _ _ := by
    simp_all only [BitVec.not_lt]
    apply BitVec.le_antisymm <;> assumption

instance : Std.Irrefl (fun (x1 : U s) x2 => x1 < x2) where
  irrefl _ := BitVec.lt_irrefl _

lemma U.cases_one (i : U 1) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

@[simp]
theorem BitVec.toFin_ofFin_comp (n : ℕ) :
    (fun (i : BitVec n) => i.toFin) ∘ BitVec.ofFin = id := by
  funext x
  simp [BitVec.toFin_ofFin]

@[simp]
theorem BitVec.ofFin_toFin_comp (n : ℕ) :
    BitVec.ofFin ∘ (fun (i : BitVec n) => i.toFin) = id := by
  funext x
  rfl

theorem List.Vector.map_toFin_map_ofFin {n d : ℕ} (v : List.Vector (Fin (2^n)) d) :
    List.Vector.map (fun i => i.toFin) (List.Vector.map BitVec.ofFin v) = v := by
  apply List.Vector.eq
  simp only [List.Vector.toList_map, List.map_map, BitVec.toFin_ofFin_comp, List.map_id]

lemma U32.index_toNat (len i : ℕ) (hlen : len < 2^32) (hi : i < 2^32) (hi_lt : i < len) :
    (({ toFin := ⟨len, hlen⟩ } : U 32) - 1 - (BitVec.ofNatLT i hi)).toNat = len - 1 - i := by
  have h1 : ({ toFin := ⟨len, hlen⟩ } : U 32).toNat = len := by simp
  have h2 : (BitVec.ofNatLT i hi : U 32).toNat = i := by simp
  have h3 : (1 : U 32).toNat = 1 := by decide
  simp only [BitVec.toNat_sub, h1, h2, h3, Nat.reducePow]
  omega
