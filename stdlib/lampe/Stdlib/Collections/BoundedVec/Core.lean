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

abbrev bvTp (T : Tp) (MaxLen : U 32) : Tp :=
  «std-1.0.0-beta.12::collections::bounded_vec::BoundedVec».tp h![T, MaxLen]

abbrev Repr (p : Prime) (T : Tp) (MaxLen : U 32) : Type :=
  Tp.denote p (bvTp T MaxLen)

def storage {p T MaxLen} (v : Repr p T MaxLen) : List.Vector (T.denote p) MaxLen.toNat :=
  Builtin.indexTpl v Builtin.Member.head

def len {p T MaxLen} (v : Repr p T MaxLen) : U 32 :=
  Builtin.indexTpl v Builtin.Member.head.tail

abbrev lenLens {p T MaxLen} : Lens (Tp.denote p) (bvTp T MaxLen) (Tp.u 32) :=
  Lens.nil.cons (Access.tuple Builtin.Member.head.tail)

def active {p T MaxLen} (v : Repr p T MaxLen) : List (T.denote p) :=
  (storage v).toList.take (len v).toNat

def embed {p T MaxLen} (v : Repr p T MaxLen) : List (T.denote p) :=
  active v

def bounded {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  (len v).toNat ≤ MaxLen.toNat

/--
Semantic "well-formedness" predicate for the concrete representation.

Recall:
* `storage v` is a `Vector` of length exactly `MaxLen.toNat` (by its type).
* `embed v = (storage v).toList.take (len v).toNat`.

So `embed` *always* truncates the concrete storage to at most `MaxLen.toNat` elements, and:

`(embed v).length = Nat.min (len v).toNat MaxLen.toNat`.

This means the "obvious" bound `(embed v).length ≤ MaxLen.toNat` is **always true**, even for
representations where `len v` is out of range.

`wellFormed v` is the *non-trivial* semantic condition "no truncation happened", i.e.
`(embed v).length = (len v).toNat`, which is equivalent to the concrete capacity check
`(len v).toNat ≤ MaxLen.toNat` (see `bounded_iff_wellFormed`).
-/
def wellFormed {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  (embed v).length = (len v).toNat

lemma embed_length_eq_min_len_toNat {p T MaxLen} (v : Repr p T MaxLen) :
    (embed v).length = Nat.min (len v).toNat MaxLen.toNat := by
  simp [embed, active, List.length_take, storage, List.Vector.toList_length]

lemma embed_length_eq_len_toNat {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) :
    (embed v).length = (len v).toNat := by
  simp [embed, active, List.length_take, List.Vector.toList_length, Nat.min_eq_left hb]

lemma bounded_iff_embed_length_eq_len_toNat {p T MaxLen} (v : Repr p T MaxLen) :
    bounded v ↔ (embed v).length = (len v).toNat := by
  constructor
  · intro hb
    exact embed_length_eq_len_toNat (v := v) hb
  · intro hlen
    have hmin : Nat.min (len v).toNat MaxLen.toNat = (len v).toNat := by
      exact (embed_length_eq_min_len_toNat (v := v)).symm.trans hlen
    have : Nat.min (len v).toNat MaxLen.toNat ≤ MaxLen.toNat :=
      Nat.min_le_right (len v).toNat MaxLen.toNat
    simpa [hmin] using this

lemma bounded_iff_wellFormed {p T MaxLen} (v : Repr p T MaxLen) :
    bounded v ↔ wellFormed v := by
  simpa [wellFormed] using (bounded_iff_embed_length_eq_len_toNat (v := v))

/-! ### Sanity lemmas -/

/-- `embed` never exceeds the concrete `len` (it is a `take`). -/
lemma embed_length_le_len_toNat {p T MaxLen} (v : Repr p T MaxLen) :
    (embed v).length ≤ (len v).toNat := by
  simpa [embed_length_eq_min_len_toNat (v := v)] using Nat.min_le_left (len v).toNat MaxLen.toNat

/-- `embed` always fits in capacity, regardless of `len`. -/
lemma embed_length_le_MaxLen {p T MaxLen} (v : Repr p T MaxLen) :
    (embed v).length ≤ MaxLen.toNat := by
  simp [embed, active, List.length_take, storage, List.Vector.toList_length, Nat.min_le_right]

/-- `bounded` implies the semantic no-truncation condition. -/
lemma wellFormed_of_bounded {p T MaxLen} {v : Repr p T MaxLen} (hb : bounded v) : wellFormed v :=
  (bounded_iff_wellFormed (v := v)).1 hb

/-- Semantic no-truncation implies the concrete bound on `len`. -/
lemma bounded_of_wellFormed {p T MaxLen} {v : Repr p T MaxLen} (hwf : wellFormed v) : bounded v :=
  (bounded_iff_wellFormed (v := v)).2 hwf

/-!
`lenLens` updates are common in extracted code (`self.len = ...`).  We keep the following small
projection lemmas to avoid repeatedly unfolding `Lens.modify` / tuple replacement details in proofs.
-/

lemma len_get_modify_lenLens {p T MaxLen} (v : Repr p T MaxLen) (n : U 32)
    (h : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).isSome = true) :
    len (((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).get h) = n := by
  simp [lenLens, len, Lens.modify, Lens.get, Access.get, Access.modify, Option.get_some,
    Builtin.replaceTuple', Builtin.indexTpl]

lemma storage_get_modify_lenLens {p T MaxLen} (v : Repr p T MaxLen) (n : U 32)
    (h : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).isSome = true) :
    storage (((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).get h) = storage v := by
  simp [lenLens, storage, Lens.modify, Lens.get, Access.get, Access.modify, Option.get_some]
  cases v <;> rfl

/-- Updating `len` with `lenLens` preserves the concrete `bounded` fact when the new `len` fits. -/
lemma bounded_get_modify_lenLens_of_toNat_le {p T MaxLen} (v : Repr p T MaxLen) (n : U 32)
    (h : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).isSome = true)
    (hn : n.toNat ≤ MaxLen.toNat) :
    bounded (((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).get h) := by
  simpa [bounded, len_get_modify_lenLens (v := v) (n := n) (h := h)] using hn

/-- Updating `len` with `lenLens` yields a semantically well-formed representation when the new `len` fits. -/
lemma wellFormed_get_modify_lenLens_of_toNat_le {p T MaxLen} (v : Repr p T MaxLen) (n : U 32)
    (h : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).isSome = true)
    (hn : n.toNat ≤ MaxLen.toNat) :
    wellFormed (((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).get h) :=
  wellFormed_of_bounded (bounded_get_modify_lenLens_of_toNat_le (v := v) (n := n) (h := h) hn)

/-- Variant of `wellFormed_get_modify_lenLens_of_toNat_le` that takes a `BitVec` inequality. -/
lemma wellFormed_get_modify_lenLens_of_le {p T MaxLen} (v : Repr p T MaxLen) (n : U 32)
    (h : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).isSome = true)
    (hn : n ≤ MaxLen) :
    wellFormed (((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v n).get h) :=
  wellFormed_get_modify_lenLens_of_toNat_le (v := v) (n := n) (h := h) ((BitVec.le_def).1 hn)

/-- For an `array : T.array Len`, the runtime `Vector.length` cast back to `U 32` is exactly `Len`. -/
lemma u32_cast_vector_length_array_eq {p} {T : Tp} {Len : U 32} (array : Tp.denote p (T.array Len)) :
    (↑(List.Vector.length array) : U 32) = Len := by
  have : List.Vector.length array = Len.toNat := by rfl
  simpa [this] using (BitVec.ofNat_toNat (x := Len))

/-- If `len v = 0`, then the embedded list is empty (assuming the representation is bounded). -/
lemma embed_nil_of_len_zero {p T MaxLen} {v : Repr p T MaxLen}
    (hlen : len v = 0) :
    embed v = ([] : List (T.denote p)) := by
  simp [embed, active, hlen]

lemma embed_getElem_toList {p T MaxLen} {self : Repr p T MaxLen} (i : Nat)
    (hxs : i < (embed self).length) (hstorage : i < (storage self).toList.length) :
    (embed self)[i]'hxs = (storage self).toList[i]'hstorage := by
  have hxs' : i < (len self).toNat := by
    have : (embed self).length = Nat.min (len self).toNat (storage self).toList.length := by
      simp [embed, active, List.length_take]
    have hmin : i < Nat.min (len self).toNat (storage self).toList.length := by
      simpa [this] using hxs
    exact Nat.lt_of_lt_of_le hmin (Nat.min_le_left _ _)
  simp [embed, active, List.getElem_take, hxs', hstorage]

abbrev BV {p : Prime} {T : Tp} {MaxLen : U 32} (selfRef : Ref) (xs : List (Tp.denote p T)) : SLP (State p) :=
  ∃∃ v : Repr p T MaxLen, [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆ ⟦wellFormed v ∧ embed v = xs⟧

/-- Fold a singleton heap into `BV` when wellFormedness and embed equality are known. -/
lemma BV_of_wellFormed_embed {p : Prime} {T : Tp} {MaxLen : U 32}
    {selfRef : Ref} {v : Repr p T MaxLen} {xs : List (Tp.denote p T)}
    (hwf : wellFormed v) (hembed : embed v = xs) :
    [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⊢ BV (MaxLen := MaxLen) selfRef xs := by
  intro st hst
  exact ⟨v, st, ∅, by simp [LawfulHeap.disjoint_empty], by simp, hst, ⟨hwf, hembed⟩, rfl⟩

/-! ### List/`embed` helper lemmas (non-Hoare) -/

theorem List.take_set {α : Type _} (l : List α) (n i : Nat) (a : α) :
    List.take n (l.set i a) = (List.take n l).set i a := by
  induction l generalizing n i with
  | nil => cases n <;> cases i <;> simp [List.take, List.set]
  | cons x xs ih =>
    cases n with
    | zero => simp [List.take]
    | succ n =>
      cases i with
      | zero => simp [List.take, List.set]
      | succ i => simp [List.take, List.set, ih]

theorem List.take_succ_set_eq_take_append {α : Type _} (l : List α) (n : Nat) (a : α)
    (hn : n < l.length) :
    List.take (n + 1) (l.set n a) = List.take n l ++ [a] := by
  induction l generalizing n with
  | nil => cases hn
  | cons x xs ih =>
    cases n with
    | zero => simp [List.take, List.set]
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
    | zero => simp [List.take]
    | succ n =>
      have hn' : n < xs.length := by simpa using hn
      simpa [List.take] using (ih (n := n) hn')

theorem BitVec.toNat_add_one_of_lt {x : U 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1).toNat = x.toNat + 1 := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  rw [Nat.mod_eq_of_lt (by linarith [hx])]

theorem BitVec.toNat_add_of_lt {x y : U 32} (hxy : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
  rw [Nat.mod_eq_of_lt (by linarith [hxy])]

lemma bitvec_ofNat_eq_of_toNat_eq {i : Nat} {x : U 32} (h : i = x.toNat) :
    BitVec.ofNat 32 i = x := by
  simpa [h] using (BitVec.ofNat_toNat (x := x))

@[simp] lemma bitvec_ofNatLT_eq_ofNat {i : Nat} (h : i < 2 ^ 32) :
    BitVec.ofNatLT i h = BitVec.ofNat 32 i := by
  simpa using (BitVec.ofNatLT_eq_ofNat (w := 32) (n := i) h)

lemma lt_two_pow_of_lt_maxLen {i : Nat} {MaxLen : U 32} (hhi : i < MaxLen.toNat) :
    i < 2 ^ 32 :=
  lt_trans hhi (by simpa using BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))

lemma nat_lt_of_bv_lt {i : Nat} {x : U 32}
    (hhi : i < 2 ^ 32) (hcond : (BitVec.ofNat 32 i) < x) : i < x.toNat := by
  rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hhi)] at hcond
  exact hcond

lemma nat_le_of_bv_le {i : Nat} {x : U 32}
    (hhi : i < 2 ^ 32) (hcond : x ≤ BitVec.ofNat 32 i) : x.toNat ≤ i := by
  rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using hhi)] at hcond
  exact hcond

lemma decide_ofNat_eq_toNat {i : Nat} {x : U 32} (pf : i < 2 ^ 32) :
    decide (BitVec.ofNat 32 i = x) = decide (i = x.toNat) := by
  simp only [decide_eq_decide]
  exact ⟨fun h => by rw [← h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using pf)],
         bitvec_ofNat_eq_of_toNat_eq⟩

lemma decide_lt_succ_eq {a b : Nat} :
    decide (a < b + 1) = (decide (a < b) || decide (a = b)) := by
  rcases Nat.lt_or_ge a b with h | h
  · simp [h, Nat.lt_trans h (Nat.lt_succ_self b), Nat.ne_of_lt h]
  · rcases Nat.eq_or_lt_of_not_lt (Nat.not_lt_of_ge h) with rfl | h'
    · simp
    · simp [Nat.not_lt_of_ge h, Nat.not_lt_of_ge (Nat.succ_le_of_lt h'), Nat.ne_of_gt h']

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
  simp [show (⟨i, h1⟩ : Fin n) = ⟨i, h2⟩ from Fin.ext rfl]

theorem vector_get_proof_irrel {n : Nat} {α : Type _} (v : List.Vector α n) (i : Nat)
    (h1 h2 : i < n) :
    List.Vector.get v ⟨i, h1⟩ = List.Vector.get v ⟨i, h2⟩ := by
  simp [show (⟨i, h1⟩ : Fin n) = ⟨i, h2⟩ from Fin.ext rfl]

lemma embed_eq_set_of_storage_set {p T MaxLen} {v v' : Repr p T MaxLen}
    (i : Nat) (hi : i < MaxLen.toNat) (a : T.denote p)
    (hlen : len v' = len v)
    (hstorage : storage v' = (storage v).set ⟨i, hi⟩ a) :
    embed v' = (embed v).set i a := by
  simp only [embed, active, hstorage, hlen, List.Vector.toList_set, List.take_set]

lemma embed_eq_append_of_storage_set_at_len {p T MaxLen} {v v' : Repr p T MaxLen}
    (a : T.denote p)
    (hb : bounded v)
    (hpush : (len v).toNat < MaxLen.toNat)
    (hlen : len v' = len v + 1)
    (hstorage : storage v' = (storage v).set ⟨(len v).toNat, hpush⟩ a) :
    embed v' = embed v ++ [a] := by
  have hmax : MaxLen.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  have hx32 : (len v).toNat + 1 < 2 ^ 32 :=
    lt_of_le_of_lt (Nat.succ_le_of_lt hpush) hmax
  have htoNat_v' : (len v').toNat = (len v).toNat + 1 := by
    simp [hlen]; simpa using (BitVec.toNat_add_one_of_lt (x := len v) hx32)
  have hstor_len : (len v).toNat < (storage v).toList.length := by
    simpa [storage, List.Vector.toList_length] using hpush
  calc
    embed v' = List.take (len v').toNat (storage v').toList := by
      simp [embed, active]
    _ = List.take ((len v).toNat + 1) ((storage v).toList.set (len v).toNat a) := by
      simp [htoNat_v', hstorage, List.Vector.toList_set]
    _ = List.take (len v).toNat (storage v).toList ++ [a] := by
      simpa using List.take_succ_set_eq_take_append (storage v).toList (len v).toNat a hstor_len
    _ = embed v ++ [a] := by simp [embed, active]

/-! ### `pop`-style semantic lemmas -/

lemma toNat_len_sub_one {p T MaxLen} {v : Repr p T MaxLen}
    (hnonzero : (0 : U 32) < len v) :
    (len v - 1).toNat = (len v).toNat - 1 := by
  have h1le : (1 : U 32) ≤ len v := by
    rw [BitVec.le_def]; simpa [BitVec.lt_def] using hnonzero
  simpa using BitVec.toNat_sub_of_le h1le

lemma embed_dropLast_eq_take_pred {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ []) :
    (embed v).dropLast = List.take ((len v).toNat - 1) (storage v).toList := by
  have hlenE := embed_length_eq_len_toNat hb
  calc (embed v).dropLast
      = List.take ((embed v).length - 1) (embed v) := by simp [List.dropLast_eq_take]
    _ = List.take ((len v).toNat - 1) (embed v) := by simp [hlenE]
    _ = List.take ((len v).toNat - 1) (List.take (len v).toNat (storage v).toList) := by
        simp [embed, active]
    _ = List.take (Nat.min ((len v).toNat - 1) (len v).toNat) (storage v).toList := by
        simp [List.take_take]
    _ = List.take ((len v).toNat - 1) (storage v).toList := by
        simp [Nat.min_eq_left (Nat.sub_le _ _)]

lemma embed_getLast_eq_storage_get {p T MaxLen} {v : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ [])
    (hnonzero : (0 : U 32) < len v) (hlast : (len v - 1).toNat < MaxLen.toNat) :
    (embed v).getLast hnonempty = (storage v)[(len v - 1).toNat]'hlast := by
  have hlenE := embed_length_eq_len_toNat hb
  have htoNat_sub := toNat_len_sub_one (v := v) hnonzero
  have hpos_len : 0 < (len v).toNat := by
    rw [BitVec.lt_def] at hnonzero; simpa using hnonzero
  have hidx_lt_len : (len v - 1).toNat < (embed v).length := by
    rw [hlenE, htoNat_sub]; exact Nat.sub_lt hpos_len Nat.one_pos
  have hstorageLen : (len v - 1).toNat < (storage v).toList.length := by
    simpa [storage, List.Vector.toList_length] using hlast
  have hlenIdx : (embed v).length - 1 = (len v - 1).toNat := by
    calc (embed v).length - 1 = (len v).toNat - 1 := by simp [hlenE]
      _ = (len v - 1).toNat := by simpa using htoNat_sub.symm
  have hlastEq : (embed v).getLast hnonempty = (embed v)[(len v - 1).toNat]'hidx_lt_len := by
    simpa [hlenIdx] using (List.getLast_eq_getElem (l := embed v) hnonempty)
  calc (embed v).getLast hnonempty
      = (embed v)[(len v - 1).toNat]'hidx_lt_len := by simpa using hlastEq
    _ = (storage v).toList[(len v - 1).toNat]'hstorageLen := by
        simpa using embed_getElem_toList _ hidx_lt_len hstorageLen
    _ = (storage v)[(len v - 1).toNat]'hlast := by
        simp [List.Vector.getElem_def, storage]

lemma embed_eq_dropLast_of_pop_update {p T MaxLen} {v v' : Repr p T MaxLen}
    (hb : bounded v) (hnonempty : embed v ≠ [])
    (hnonzero : (0 : U 32) < len v)
    (hlen : len v' = len v - 1)
    (hlast : (len v - 1).toNat < MaxLen.toNat)
    (hstorage : storage v' = (storage v).set ⟨(len v - 1).toNat, hlast⟩ (Tp.zero p T)) :
    embed v' = (embed v).dropLast := by
  have htoNat_sub := toNat_len_sub_one (v := v) hnonzero
  rw [embed_dropLast_eq_take_pred hb hnonempty]
  simp only [embed, active, hstorage, List.Vector.toList_set, List.take_set]
  conv_lhs => rw [List.set_eq_of_length_le (by simp [hlen, List.length_take_le])]
  have hv : (len v').toNat = (len v - 1).toNat := by simp [hlen]
  rw [hv, htoNat_sub]

section BVNat

@[simp] lemma u32_toNat_lt (x : U 32) : x.toNat < 2 ^ 32 :=
  BitVec.toNat_lt_twoPow_of_le (by rfl)

@[simp] lemma u32_toNat_lt' (x : U 32) : x.toNat < 4294967296 := by
  simpa using u32_toNat_lt x

lemma ofNat32_toNat {i : Nat} (h : i < 2 ^ 32) :
    (BitVec.ofNat 32 i).toNat = i := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simpa using h)]

lemma nat_mod_4294967296 {n : Nat} (h : n < 2 ^ 32) :
    n % 4294967296 = n :=
  Nat.mod_eq_of_lt (by simpa using h)

lemma nat_lt_4294967296 {n : Nat} (h : n < 2 ^ 32) :
    n < 4294967296 := by simpa using h

end BVNat

/-! ### List helper for extend_from loop bodies -/

/-- One step of the extend_from copy-loop: given that `take (offset + i) storage = prefix ++ source.take i`,
setting `storage[offset + i] := source[i]` extends the equation to `i + 1`. -/
theorem List.take_set_extends {α : Type _} {l : List α} {prefix_ source : List α}
    {offset i : Nat}
    (h_take : l.take (offset + i) = prefix_ ++ source.take i)
    (h_stor : offset + i < l.length)
    (h_src : i < source.length) :
    (l.set (offset + i) (source[i]'h_src)).take (offset + (i + 1)) =
      prefix_ ++ source.take (i + 1) := by
  calc
    (l.set (offset + i) (source[i]'h_src)).take (offset + (i + 1)) =
      l.take (offset + i) ++ [source[i]'h_src] := by
      simpa using List.take_succ_set_eq_take_append l (offset + i) (source[i]'h_src) h_stor
    _ = (prefix_ ++ source.take i) ++ [source[i]'h_src] := by rw [h_take]
    _ = prefix_ ++ (source.take i ++ [source[i]'h_src]) := by rw [List.append_assoc]
    _ = prefix_ ++ source.take (i + 1) := by
      congr 1; symm
      simpa using List.take_succ_eq_take_append_get source i h_src

/-- Given `len v = len self` and `(len self).toNat + i < 2^32`,
compute that `(v.2.1 + i) % 4294967296 = (len self).toNat + i`. -/
theorem extend_loop_idx_mod {p T MaxLen} {v self : Repr p T MaxLen} {i : Nat}
    (hlenV : len v = len self)
    (hi_lt : (len self).toNat + i < 2 ^ 32) :
    (BitVec.toNat v.2.1 + i) % 4294967296 = (len self).toNat + i := by
  have hlenVNat' : BitVec.toNat v.2.1 = (len self).toNat := by simpa [len] using congrArg BitVec.toNat hlenV
  simpa [hlenVNat'] using nat_mod_4294967296 (by simpa [hlenVNat'] using hi_lt)

/-- Given `len v = len self` and `(len self).toNat + i < 2^32`,
the index `len v + ofNat 32 i` has toNat equal to `(len self).toNat + i`. -/
theorem extend_loop_idx_toNat {p T MaxLen} {v self : Repr p T MaxLen} {i : Nat}
    (hlenV : len v = len self) (hi32 : i < 2 ^ 32)
    (hi_lt : (len self).toNat + i < 2 ^ 32) :
    (len v + BitVec.ofNat 32 i).toNat = (len self).toNat + i := by
  have hlenVNat : (len v).toNat = (len self).toNat := by simpa using congrArg BitVec.toNat hlenV
  have htoNat_i := ofNat32_toNat hi32
  have hsum_lt' : (len v).toNat + (BitVec.ofNat 32 i).toNat < 2 ^ 32 := by
    simpa [hlenVNat, htoNat_i] using hi_lt
  simpa [hlenVNat, htoNat_i] using BitVec.toNat_add_of_lt (x := len v) (y := BitVec.ofNat 32 i) hsum_lt'


/-- In the `extend_from_bounded_vec` constrained loop,
the negated condition `¬(exceeded_len)` after the OR-update
gives `i ≤ x.toNat` and `ofNatLT i ≠ x`, hence `i < x.toNat`. -/
lemma exceeded_len_lt_of_cond_true
    {i : Nat} {x : U 32}
    (pf : i < 2 ^ 32)
    (hi_le : i ≤ x.toNat)
    (hi_ne : ¬(BitVec.ofNatLT i pf = x)) :
    i < x.toNat := by
  refine lt_of_le_of_ne hi_le ?_
  intro hi_eq
  exact hi_ne (by
    simpa [hi_eq] using BitVec.ofNat_toNat (x := x))

/-- Post-loop finalization for all `extend_from_*` proofs:
given the loop invariant at completion, derive `wellFormed` and correct `embed` after updating `len`. -/
theorem extend_from_finalize {p T MaxLen} {self v : Repr p T MaxLen}
    {newLen : U 32} {source : List (T.denote p)}
    (hlenV : len v = len self)
    (htakeV : List.take ((len self).toNat + source.length) (storage v).toList =
              embed self ++ source)
    (h_isSome : ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v newLen).isSome = true)
    (hnew_toNat : newLen.toNat = (len self).toNat + source.length)
    (hnew_le : newLen.toNat ≤ MaxLen.toNat) :
    let v' := ((lenLens (p := p) (T := T) (MaxLen := MaxLen)).modify v newLen).get h_isSome
    wellFormed v' ∧ embed v' = embed self ++ source := by
  intro v'
  have hwf : wellFormed v' :=
    wellFormed_get_modify_lenLens_of_toNat_le v newLen h_isSome hnew_le
  have hembed : embed v' = embed self ++ source := by
    have hlen' : len v' = newLen := len_get_modify_lenLens v newLen h_isSome
    have hstor' : storage v' = storage v := storage_get_modify_lenLens v newLen h_isSome
    simp [embed, active, hlen', hstor', hnew_toNat, htakeV]
  exact ⟨hwf, hembed⟩

end Lampe.Stdlib.Collections.BoundedVec
