import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.12»

/-!
Core semantic interface for Noir `collections::bounded_vec::BoundedVec`.

We keep:
- the concrete representation projections (`storage`, `len`)
- the semantic view (`embed`)

This file intentionally contains no Hoare triples and no "constructor-style" update helpers
(`withLen`, `withStorageAt`, `pushed`, `popped`, ...).
-/

abbrev Repr (p : Prime) (T : Tp) (MaxLen : U 32) : Type :=
  Tp.denoteArgs p [T.array MaxLen, .u 32]

def storage {p T MaxLen} (v : Repr p T MaxLen) : List.Vector (T.denote p) MaxLen.toNat :=
  Builtin.indexTpl v Builtin.Member.head

def len {p T MaxLen} (v : Repr p T MaxLen) : U 32 :=
  Builtin.indexTpl v Builtin.Member.head.tail

def active {p T MaxLen} (v : Repr p T MaxLen) : List (T.denote p) :=
  (storage v).toList.take (len v).toNat

def embed {p T MaxLen} (v : Repr p T MaxLen) : List (T.denote p) :=
  active v

def bounded {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  (len v).toNat ≤ MaxLen.toNat

lemma embed_length_eq_len_toNat {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) :
    (embed v).length = (len v).toNat := by
  simp [embed, active, List.length_take, List.Vector.toList_length, Nat.min_eq_left hb]

lemma embed_length_le_MaxLen {p T MaxLen} (v : Repr p T MaxLen) :
    (embed v).length ≤ MaxLen.toNat := by
  -- `embed` is always a `take` of a list of length `MaxLen`.
  simp [embed, active, List.length_take, storage, List.Vector.toList_length, Nat.min_le_right]

/-- If `len v = 0`, then the embedded list is empty (assuming the representation is bounded). -/
lemma embed_nil_of_len_zero {p T MaxLen} {v : Repr p T MaxLen}
    (hlen : len v = 0) :
    embed v = ([] : List (T.denote p)) := by
  simp [embed, active, hlen]

lemma embed_getElem_toList {p T MaxLen} {self : Repr p T MaxLen} (i : Nat)
    (hxs : i < (embed self).length) (hstorage : i < (storage self).toList.length) :
    (embed self)[i]'hxs = (storage self).toList[i]'hstorage := by
  -- `embed self` is `take (len self)` of `storage.toList`.
  have hxs' : i < (len self).toNat := by
    -- `length (take n l) = min n l.length`
    have : (embed self).length = Nat.min (len self).toNat (storage self).toList.length := by
      simp [embed, active, List.length_take]
    have hmin : i < Nat.min (len self).toNat (storage self).toList.length := by
      simpa [this] using hxs
    exact Nat.lt_of_lt_of_le hmin (Nat.min_le_left _ _)
  simp [embed, active, List.getElem_take, hxs', hstorage]

abbrev bvTp (T : Tp) (MaxLen : U 32) : Tp :=
  «std-1.0.0-beta.12::collections::bounded_vec::BoundedVec».tp h![T, MaxLen]

def BV {p : Prime} {T : Tp} {MaxLen : U 32} (selfRef : Ref) (xs : List (Tp.denote p T)) : SLP (State p) :=
  ∃∃ v : Repr p T MaxLen, [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆ ⟦bounded v ∧ embed v = xs⟧

/-! ### List/`embed` helper lemmas (non-Hoare) -/

theorem List.take_set {α : Type _} (l : List α) (n i : Nat) (a : α) :
    List.take n (l.set i a) = (List.take n l).set i a := by
  induction l generalizing n i with
  | nil =>
    cases n <;> cases i <;> simp [List.take, List.set]
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      cases i with
      | zero =>
        simp [List.take, List.set]
      | succ i =>
        simp [List.take, List.set, ih]

theorem List.take_succ_set_eq_take_append {α : Type _} (l : List α) (n : Nat) (a : α)
    (hn : n < l.length) :
    List.take (n + 1) (l.set n a) = List.take n l ++ [a] := by
  induction l generalizing n with
  | nil =>
    cases hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.take, List.set]
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simpa [List.take, List.set] using (ih (n := n) hn')

theorem List.take_succ_eq_take_append_get {α : Type _} (l : List α) (n : Nat)
    (hn : n < l.length) :
    List.take (n + 1) l = List.take n l ++ [l[n]'hn] := by
  induction l generalizing n with
  | nil => cases hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp [List.take]
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simpa [List.take] using (ih (n := n) hn')

theorem BitVec.toNat_add_one_of_lt {x : U 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  have hx' : x.toNat + 1 < 4294967296 := by linarith [hx]
  rw [Nat.mod_eq_of_lt hx']

theorem BitVec.toNat_add_of_lt {x y : U 32} (hxy : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  have hxy' : x.toNat + y.toNat < 4294967296 := by linarith [hxy]
  rw [Nat.mod_eq_of_lt hxy']

lemma bitvec_ofNat_eq_of_toNat_eq {i : Nat} {x : U 32} (h : i = x.toNat) :
    BitVec.ofNat 32 i = x := by
  simpa [h] using (BitVec.ofNat_toNat (x := x))

@[simp] lemma bitvec_ofNatLT_eq_ofNat {i : Nat} (h : i < 2 ^ 32) :
    BitVec.ofNatLT i h = BitVec.ofNat 32 i := by
  simpa using (BitVec.ofNatLT_eq_ofNat (w := 32) (n := i) h)

lemma lt_two_pow_of_lt_maxLen {i : Nat} {MaxLen : U 32} (hhi : i < MaxLen.toNat) :
    i < 2 ^ 32 := by
  have hmax : MaxLen.toNat < 2 ^ 32 := by
    simpa using
      (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  exact lt_trans hhi hmax

lemma nat_lt_of_bv_lt {i : Nat} {x : U 32}
    (hhi : i < 2 ^ 32) (hcond : (BitVec.ofNat 32 i) < x) : i < x.toNat := by
  have hcond' : (BitVec.ofNat 32 i).toNat < x.toNat := by
    simpa [BitVec.lt_def] using hcond
  have hhi' : i < 4294967296 := by
    simpa using hhi
  have hcond'' : i % 4294967296 < x.toNat := by
    simpa [BitVec.toNat_ofNat] using hcond'
  simpa [Nat.mod_eq_of_lt hhi'] using hcond''

lemma nat_le_of_bv_le {i : Nat} {x : U 32}
    (hhi : i < 2 ^ 32) (hcond : x ≤ BitVec.ofNat 32 i) : x.toNat ≤ i := by
  have hcond' : x.toNat ≤ (BitVec.ofNat 32 i).toNat := by
    simpa [BitVec.le_def] using hcond
  have hhi' : i < 4294967296 := by
    simpa using hhi
  have hcond'' : x.toNat ≤ i % 4294967296 := by
    simpa [BitVec.toNat_ofNat] using hcond'
  simpa [Nat.mod_eq_of_lt hhi'] using hcond''

lemma decide_ofNat_eq_toNat {i : Nat} {x : U 32} (pf : i < 2 ^ 32) :
    decide (BitVec.ofNat 32 i = x) = decide (i = x.toNat) := by
  by_cases hxi : i = x.toNat
  ·
    have hbx : BitVec.ofNat 32 i = x := by
      simpa using (bitvec_ofNat_eq_of_toNat_eq (i := i) (x := x) hxi)
    simp [hxi, hbx]
  ·
    have pf' : i < 4294967296 := by simpa using pf
    have hbx : BitVec.ofNat 32 i ≠ x := by
      intro hbx
      have hbx_toNat : (BitVec.ofNat 32 i).toNat = x.toNat := by
        simpa using congrArg BitVec.toNat hbx
      have hmod : i % 4294967296 = i := Nat.mod_eq_of_lt pf'
      have : i = x.toNat := by
        have hbx_toNat' : i % 4294967296 = x.toNat := by
          simpa [BitVec.toNat_ofNat] using hbx_toNat
        simpa [hmod] using hbx_toNat'
      exact hxi this
    simp [hxi, hbx]

lemma decide_lt_succ_eq {a b : Nat} :
    decide (a < b + 1) = (decide (a < b) || decide (a = b)) := by
  by_cases h1 : a < b
  ·
    have h2 : a < b + 1 := Nat.lt_trans h1 (Nat.lt_succ_self b)
    simp [h1, h2, Nat.ne_of_lt h1]
  ·
    have h1' : a = b ∨ b < a := Nat.eq_or_lt_of_not_lt h1
    cases h1' with
    | inl hEq =>
        have h2 : a < b + 1 := by simpa [hEq] using Nat.lt_succ_self b
        simp [h1, hEq, h2]
    | inr hGt =>
        have h2 : ¬ a < b + 1 := by
          have hle : b + 1 ≤ a := Nat.succ_le_iff.mpr hGt
          exact Nat.not_lt_of_ge hle
        simp [h1, h2, Nat.ne_of_gt hGt]

lemma decide_lt_succ_eq_bv {i : Nat} {x : U 32} (pf : i < 2 ^ 32) :
    decide (x.toNat < i + 1) =
      (decide (x.toNat < i) || decide (BitVec.ofNat 32 i = x)) := by
  have h := decide_lt_succ_eq (a := x.toNat) (b := i)
  have h' : decide (x.toNat = i) = decide (BitVec.ofNat 32 i = x) := by
    simpa [eq_comm] using (decide_ofNat_eq_toNat (i := i) (x := x) pf).symm
  simpa [h'] using h

theorem vector_set_proof_irrel {n : Nat} {α : Type _} (v : List.Vector α n) (i : Nat)
    (h1 h2 : i < n) (x : α) :
    List.Vector.set v ⟨i, h1⟩ x = List.Vector.set v ⟨i, h2⟩ x := by
  have : (⟨i, h1⟩ : Fin n) = ⟨i, h2⟩ := by apply Fin.ext; rfl
  simp [this]

theorem vector_get_proof_irrel {n : Nat} {α : Type _} (v : List.Vector α n) (i : Nat)
    (h1 h2 : i < n) :
    List.Vector.get v ⟨i, h1⟩ = List.Vector.get v ⟨i, h2⟩ := by
  have : (⟨i, h1⟩ : Fin n) = ⟨i, h2⟩ := by apply Fin.ext; rfl
  simp [this]

lemma embed_eq_set_of_storage_set {p T MaxLen} {v v' : Repr p T MaxLen}
    (i : Nat) (hi : i < MaxLen.toNat) (a : T.denote p)
    (hlen : len v' = len v)
    (hstorage : storage v' = (storage v).set ⟨i, hi⟩ a) :
    embed v' = (embed v).set i a := by
  calc
    embed v' = List.take (len v').toNat (storage v').toList := by
      simp [embed, active]
    _ = List.take (len v).toNat (storage v').toList := by
      simp [hlen]
    _ = List.take (len v).toNat ((storage v).set ⟨i, hi⟩ a).toList := by
      simp [hstorage]
    _ = List.take (len v).toNat ((storage v).toList.set i a) := by
      simp [List.Vector.toList_set]
    _ = (List.take (len v).toNat (storage v).toList).set i a := by
      simp [List.take_set (l := (storage v).toList) (n := (len v).toNat) (i := i) (a := a)]
    _ = (embed v).set i a := by
      simp [embed, active]

lemma embed_eq_append_of_storage_set_at_len {p T MaxLen} {v v' : Repr p T MaxLen}
    (a : T.denote p)
    (hb : bounded v)
    (hpush : (len v).toNat < MaxLen.toNat)
    (hlen : len v' = len v + 1)
    (hstorage : storage v' = (storage v).set ⟨(len v).toNat, hpush⟩ a) :
    embed v' = embed v ++ [a] := by
  have hmax : MaxLen.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  have hx32 : (len v).toNat + 1 < 2 ^ 32 := by
    exact lt_of_le_of_lt (Nat.succ_le_of_lt hpush) hmax
  have htoNat_v' : (len v').toNat = (len v).toNat + 1 := by
    have h1 : (len v').toNat = (len v + 1).toNat := by
      simpa [hlen]
    calc
      (len v').toNat = (len v + 1).toNat := h1
      _ = (len v).toNat + 1 := by
        simpa using (BitVec.toNat_add_one_of_lt (x := len v) hx32)
  have hstor_len : (len v).toNat < (storage v).toList.length := by
    simpa [storage, List.Vector.toList_length] using hpush
  have hstorage_toList :
      (storage v').toList = (storage v).toList.set (len v).toNat a := by
    simpa [hstorage, List.Vector.toList_set]
  calc
    embed v' = List.take (len v').toNat (storage v').toList := by
      simp [embed, active]
    _ = List.take ((len v).toNat + 1) ((storage v).toList.set (len v).toNat a) := by
      simp [htoNat_v', hstorage_toList]
    _ = List.take (len v).toNat (storage v).toList ++ [a] := by
      simpa using
        (List.take_succ_set_eq_take_append (l := (storage v).toList) (n := (len v).toNat) (a := a)
          (hn := hstor_len))
    _ = embed v ++ [a] := by
      simp [embed, active]

/-! ### `pop`-style semantic lemmas (non-Hoare) -/

lemma toNat_len_sub_one {p T MaxLen} {v : Repr p T MaxLen}
    (hnonzero : (0 : U 32) < len v) :
    (len v - 1).toNat = (len v).toNat - 1 := by
  have h1le : (1 : U 32) ≤ len v := by
    rw [BitVec.le_def]
    have : 0 < (len v).toNat := by
      rw [BitVec.lt_def] at hnonzero
      simpa using hnonzero
    exact Nat.succ_le_of_lt this
  simpa using (BitVec.toNat_sub_of_le (x := len v) (y := (1 : U 32)) h1le)

lemma embed_dropLast_eq_take_pred {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ []) :
    (embed v).dropLast = List.take ((len v).toNat - 1) (storage v).toList := by
  have hlenE : (embed v).length = (len v).toNat := embed_length_eq_len_toNat (v := v) hb
  calc
    (embed v).dropLast = List.take ((embed v).length - 1) (embed v) := by
      simp [List.dropLast_eq_take]
    _ = List.take ((len v).toNat - 1) (embed v) := by
      simp [hlenE]
    _ = List.take ((len v).toNat - 1) (List.take (len v).toNat (storage v).toList) := by
      simp [embed, active]
    _ = List.take (Nat.min ((len v).toNat - 1) (len v).toNat) (storage v).toList := by
      simp [List.take_take]
    _ = List.take ((len v).toNat - 1) (storage v).toList := by
      have : (len v).toNat - 1 ≤ (len v).toNat := Nat.sub_le _ _
      simp [Nat.min_eq_left this]

lemma embed_getLast_eq_storage_get {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ [])
    (hnonzero : (0 : U 32) < len v) (hlast : (len v - 1).toNat < MaxLen.toNat) :
    (embed v).getLast hnonempty = (storage v)[(len v - 1).toNat]'hlast := by
  have hlenE : (embed v).length = (len v).toNat := embed_length_eq_len_toNat (v := v) hb
  have htoNat_sub : (len v - 1).toNat = (len v).toNat - 1 := toNat_len_sub_one (v := v) hnonzero
  have hpos_len : 0 < (len v).toNat := by
    rw [BitVec.lt_def] at hnonzero
    simpa using hnonzero
  have hidx_lt_len : (len v - 1).toNat < (embed v).length := by
    have hpred : (len v).toNat - 1 < (len v).toNat :=
      Nat.pred_lt (Nat.ne_of_gt hpos_len)
    have : (len v - 1).toNat < (len v).toNat := by
      -- avoid expanding `BitVec.toNat` subtraction into modular arithmetic
      rw [htoNat_sub]
      exact hpred
    simpa [hlenE] using this
  have hstorageLen : (len v - 1).toNat < (storage v).toList.length := by
    simpa [storage, List.Vector.toList_length] using hlast
  have hget :
      (embed v)[(len v - 1).toNat]'hidx_lt_len =
        (storage v).toList[(len v - 1).toNat]'hstorageLen := by
    simpa using
      (embed_getElem_toList (self := v) (i := (len v - 1).toNat)
        (hxs := hidx_lt_len) (hstorage := hstorageLen))
  have hlenIdx : (embed v).length - 1 = (len v - 1).toNat := by
    calc
      (embed v).length - 1 = (len v).toNat - 1 := by simp [hlenE]
      _ = (len v - 1).toNat := by simpa using (Eq.symm htoNat_sub)
  have hlastEq :
      (embed v).getLast hnonempty = (embed v)[(len v - 1).toNat]'hidx_lt_len := by
    simpa [hlenIdx] using (List.getLast_eq_getElem (l := embed v) hnonempty)
  calc
    (embed v).getLast hnonempty
        = (embed v)[(len v - 1).toNat]'hidx_lt_len := by
          simpa using hlastEq
    _ = (storage v).toList[(len v - 1).toNat]'hstorageLen := by
          simpa using hget
    _ = (storage v)[(len v - 1).toNat]'hlast := by
          simp [List.Vector.getElem_def, storage]

lemma embed_eq_dropLast_of_pop_update {p T MaxLen} {v v' : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ [])
    (hnonzero : (0 : U 32) < len v)
    (hlen : len v' = len v - 1)
    (hlast : (len v - 1).toNat < MaxLen.toNat)
    (hstorage : storage v' = (storage v).set ⟨(len v - 1).toNat, hlast⟩ (Tp.zero p T)) :
    embed v' = (embed v).dropLast := by
  have htoNat_sub : (len v - 1).toNat = (len v).toNat - 1 := toNat_len_sub_one (v := v) hnonzero
  have hdrop : (embed v).dropLast = List.take ((len v).toNat - 1) (storage v).toList :=
    embed_dropLast_eq_take_pred (v := v) hb hnonempty
  -- `embed v'` is `take (len-1)` of the updated storage; setting at index `len-1` is not observed.
  have hset_noop :
      (List.take (len v').toNat (storage v).toList).set (len v - 1).toNat (Tp.zero p T) =
        List.take (len v').toNat (storage v).toList := by
    apply List.set_eq_of_length_le
    have ht : (List.take (len v').toNat (storage v).toList).length ≤ (len v').toNat := by
      simpa using (List.length_take_le (n := (len v').toNat) (l := (storage v).toList))
    -- `len v' = len v - 1` so the index is exactly `len v'`
    simpa [hlen] using ht
  calc
    embed v' = List.take (len v').toNat (storage v').toList := by
      simp [embed, active]
    _ = List.take (len v').toNat ((storage v).toList.set (len v - 1).toNat (Tp.zero p T)) := by
      simp [hstorage, List.Vector.toList_set]
    _ = (List.take (len v').toNat (storage v).toList).set (len v - 1).toNat (Tp.zero p T) := by
      simpa using
        (List.take_set (l := (storage v).toList) (n := (len v').toNat)
          (i := (len v - 1).toNat) (a := Tp.zero p T))
    _ = List.take (len v').toNat (storage v).toList := hset_noop
    _ = List.take ((len v).toNat - 1) (storage v).toList := by
      have hv : (len v').toNat = (len v - 1).toNat := by simpa [hlen]
      rw [hv, htoNat_sub]
    _ = (embed v).dropLast := by
      simpa [hdrop]

end Lampe.Stdlib.Collections.BoundedVec
