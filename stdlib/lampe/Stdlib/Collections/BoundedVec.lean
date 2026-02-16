import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.12»

/-!
`collections::bounded_vec` is represented as a pair:
- `storage : Array<T, MaxLen>`
- `len : u32`

The intended abstract sequence is `storage.take len`.
For the "safe" API surface (`new`, `get`, `set`, `push`, `pop`, `extend_*`, `from_array`,
`from_parts`), we also want a zeroed-tail invariant for indices `i ≥ len`.

This file starts the formalization by:
- introducing model projections/invariants,
- proving the trivial accessor specs (`len`, `max_len`, `storage`),
- documenting the spec backlog for the remaining methods.
-/

abbrev Repr (p : Prime) (T : Tp) (MaxLen : U 32) : Type :=
  Tp.denoteArgs p [T.array MaxLen, .u 32]

def storage {p T MaxLen} (v : Repr p T MaxLen) : List.Vector (T.denote p) MaxLen.toNat :=
  Builtin.indexTpl v Builtin.Member.head

def len {p T MaxLen} (v : Repr p T MaxLen) : U 32 :=
  Builtin.indexTpl v Builtin.Member.head.tail

def active {p T MaxLen} (v : Repr p T MaxLen) : List (T.denote p) :=
  (storage v).toList.take (len v).toNat

def bounded {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  (len v).toNat ≤ MaxLen.toNat

def zeroedTail {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  ∀ i (hlo : (len v).toNat ≤ i) (hhi : i < MaxLen.toNat),
    (storage v)[i]'hhi = Tp.zero p T

def wellFormed {p T MaxLen} (v : Repr p T MaxLen) : Prop :=
  bounded v ∧ zeroedTail v

abbrev bvTp (T : Tp) (MaxLen : U 32) : Tp :=
  «std-1.0.0-beta.12::collections::bounded_vec::BoundedVec».tp h![T, MaxLen]

def withStorage {p T MaxLen}
    (v : Repr p T MaxLen) (arr : List.Vector (T.denote p) MaxLen.toNat) : Repr p T MaxLen :=
  Builtin.replaceTuple' v Builtin.Member.head arr

def withLen {p T MaxLen}
    (v : Repr p T MaxLen) (l : U 32) : Repr p T MaxLen :=
  Builtin.replaceTuple' v Builtin.Member.head.tail l

def withStorageAt {p T MaxLen}
    (v : Repr p T MaxLen) (idx : Fin MaxLen.toNat) (value : Tp.denote p T) : Repr p T MaxLen :=
  withStorage v ((storage v).set idx value)

def pushed {p T MaxLen}
    (v : Repr p T MaxLen)
    (elem : Tp.denote p T)
    (hpush : (len v).toNat < MaxLen.toNat) : Repr p T MaxLen :=
  withLen (withStorageAt v ⟨(len v).toNat, hpush⟩ elem) (len v + 1)

def popped {p T MaxLen}
    (v : Repr p T MaxLen)
    (hlast : (len v - 1).toNat < MaxLen.toNat) : Repr p T MaxLen :=
  withLen (withStorageAt v ⟨(len v - 1).toNat, hlast⟩ (Tp.zero p T)) (len v - 1)

@[simp]
theorem storage_withStorage {p T MaxLen} {v : Repr p T MaxLen}
    {arr : List.Vector (T.denote p) MaxLen.toNat} :
    storage (withStorage v arr) = arr := by
  unfold storage withStorage
  simp [Builtin.index_replaced_tpl (tpl := v) (mem := Builtin.Member.head) (v' := arr)]

@[simp]
theorem len_withStorage {p T MaxLen} {v : Repr p T MaxLen}
    {arr : List.Vector (T.denote p) MaxLen.toNat} :
    len (withStorage v arr) = len v := by
  unfold len withStorage
  rfl

@[simp]
theorem len_withLen {p T MaxLen} {v : Repr p T MaxLen} {l : U 32} :
    len (withLen v l) = l := by
  unfold len withLen
  simp [Builtin.index_replaced_tpl (tpl := v) (mem := Builtin.Member.head.tail) (v' := l)]

@[simp]
theorem index_replace_head_tail {p T MaxLen} {v : Repr p T MaxLen} {l : U 32} :
    Builtin.indexTpl (Builtin.replaceTuple' v Builtin.Member.head.tail l)
      Builtin.Member.head.tail = l := by
  simp [Builtin.index_replaced_tpl (tpl := v) (mem := Builtin.Member.head.tail) (v' := l)]

@[simp]
theorem storage_withLen {p T MaxLen} {v : Repr p T MaxLen} {l : U 32} :
    storage (withLen v l) = storage v := by
  unfold storage withLen
  rfl

@[simp]
theorem len_modify_head_tail {p T MaxLen}
    {v : Tp.denote p (bvTp T MaxLen)} {l : U 32}
    (h : ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify v l).isSome = true) :
    len (((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify v l).get h) = l := by
  unfold len
  simp [Lens.modify, Lens.get, Access.modify]
  exact (Builtin.index_replaced_tpl (tpl := v) (mem := Builtin.Member.head.tail) (v' := l))

@[simp]
theorem len_withStorageAt {p T MaxLen} {v : Repr p T MaxLen} {idx : Fin MaxLen.toNat}
    {value : Tp.denote p T} :
    len (withStorageAt v idx value) = len v := by
  simp [withStorageAt]

@[simp]
theorem withStorageAt_withLen {p T MaxLen} {v : Repr p T MaxLen} {l : U 32} {idx : Fin MaxLen.toNat}
    {value : Tp.denote p T} :
    withStorageAt (withLen v l) idx value = withLen (withStorageAt v idx value) l := by
  cases v; rfl

theorem vector_set_proof_irrel {n : Nat} {α : Type _} (v : List.Vector α n) (i : Nat)
    (h1 h2 : i < n) (x : α) :
    List.Vector.set v ⟨i, h1⟩ x = List.Vector.set v ⟨i, h2⟩ x := by
  have : (⟨i, h1⟩ : Fin n) = ⟨i, h2⟩ := by
    apply Fin.ext
    rfl
  simp [this]

@[simp]
theorem indexTpl_replace_tail_head {p T MaxLen} (v : Repr p T MaxLen) (l : U 32) :
    Builtin.indexTpl (Builtin.replaceTuple' v Builtin.Member.head.tail l) Builtin.Member.head =
      Builtin.indexTpl v Builtin.Member.head := by
  cases v; rfl

@[simp]
theorem indexTpl_replace_head_tail {p T MaxLen} (v : Repr p T MaxLen)
    (arr : List.Vector (T.denote p) MaxLen.toNat) :
    Builtin.indexTpl (Builtin.replaceTuple' v Builtin.Member.head arr) Builtin.Member.head.tail =
      Builtin.indexTpl v Builtin.Member.head.tail := by
  cases v; rfl

theorem replaceTuple'_head_tail_comm {p T MaxLen} (v : Repr p T MaxLen)
    (arr : List.Vector (T.denote p) MaxLen.toNat) (l : U 32) :
    Builtin.replaceTuple' (Builtin.replaceTuple' v Builtin.Member.head.tail l) Builtin.Member.head arr =
      Builtin.replaceTuple' (Builtin.replaceTuple' v Builtin.Member.head arr) Builtin.Member.head.tail l := by
  cases v; rfl

theorem modify_head_array_some {p T MaxLen} {v : Tp.denote p (bvTp T MaxLen)} {idx : U 32} {value : Tp.denote p T}
    (hidx : idx.toNat < MaxLen.toNat) :
    (((Lens.nil.cons (Access.tuple Builtin.Member.head)).cons (Access.array idx)).modify v value) =
      some (withStorageAt v ⟨idx.toNat, hidx⟩ value) := by
  simp [Lens.modify, Lens.get, Access.get, Access.modify, withStorageAt, withStorage, storage, hidx]

lemma bitvec_ofNat_eq_of_toNat_eq {i : Nat} {x : U 32} (h : i = x.toNat) :
    BitVec.ofNat 32 i = x := by
  simp [h, BitVec.ofNat_toNat (x := x)]

@[simp] lemma bitvec_ofNatLT_eq_ofNat {i : Nat} (h : i < 2 ^ 32) :
    BitVec.ofNatLT i h = BitVec.ofNat 32 i := by
  simpa using (BitVec.ofNatLT_eq_ofNat (w := 32) (n := i) h)

lemma bitvec_ofNatLT_eq_of_toNat_eq {i : Nat} {x : U 32} (h : i = x.toNat) (pf : i < 2 ^ 32) :
    BitVec.ofNatLT i pf = x := by
  simpa using (bitvec_ofNat_eq_of_toNat_eq (i := i) (x := x) h)

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

lemma toNat_ofNat_lt_of_lt_maxLen {i : Nat} {MaxLen : U 32} (hhi : i < MaxLen.toNat) :
    (BitVec.ofNat 32 i).toNat < MaxLen.toNat := by
  have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
  have pf' : i < 4294967296 := by
    simpa using pf
  have hhi' : i % 4294967296 < MaxLen.toNat := by
    simpa [Nat.mod_eq_of_lt pf'] using hhi
  simpa [BitVec.toNat_ofNat] using hhi'

lemma active_prefix_storage {p T MaxLen} {self : Repr p T MaxLen} {i : Nat}
    (hbounded : bounded self) (hi : i < (len self).toNat) :
    List.take i (active self) ++
        [(storage self).toList[i]'(by
          have : i < (storage self).toList.length := by
            simpa [bounded, storage, List.Vector.toList_length] using (lt_of_lt_of_le hi hbounded)
          exact this)] <+:
      active self := by
  have hbounded' : (len self).toNat ≤ MaxLen.toNat := hbounded
  have hactive_len : (active self).length = (len self).toNat := by
    simp [active, List.length_take, List.Vector.toList_length, hbounded']
  have hlt : i < (active self).length := by
    simpa [hactive_len] using hi
  have hprefix :
      List.take i (active self) ++ [(active self)[i]'hlt] <+: active self := by
    have htake :
        List.take i (active self) ++ [(active self)[i]'hlt] =
          List.take (i + 1) (active self) := by
      simpa using (List.take_succ_eq_append_getElem hlt)
    have hpre : List.take (i + 1) (active self) <+: active self := by
      simpa using (List.take_prefix (i + 1) (active self))
    simpa [htake] using hpre
  have hstorage : i < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using (lt_of_lt_of_le hi hbounded')
  have hget : (active self)[i]'hlt = (storage self).toList[i]'hstorage := by
    simp [active, List.getElem_take, hstorage, hbounded', hi]
  simpa [hget] using hprefix

lemma decide_lt_succ_eq {a b : Nat} :
    decide (a < b + 1) = (decide (a < b) || decide (a = b)) := by
  by_cases h1 : a < b
  · have h2 : a < b + 1 := Nat.lt_trans h1 (Nat.lt_succ_self b)
    simp [h1, h2, Nat.ne_of_lt h1]
  · have h1' : a = b ∨ b < a := Nat.eq_or_lt_of_not_lt h1
    cases h1' with
    | inl hEq =>
        have h2 : a < b + 1 := by simp [hEq, Nat.lt_succ_self b]
        simp [h1, hEq, h2]
    | inr hGt =>
        have h2 : ¬ a < b + 1 := by
          have hle : b + 1 ≤ a := Nat.succ_le_iff.mpr hGt
          exact Nat.not_lt_of_ge hle
        simp [h1, h2, Nat.ne_of_gt hGt]

lemma min_succ_eq_right {i len : Nat} (h : len ≤ i) : min (i + 1) len = len := by
  exact Nat.min_eq_right (Nat.le_trans h (Nat.le_succ i))

lemma take_active_eq_take_storage {p T MaxLen} {self : Repr p T MaxLen} {i : Nat}
    (h : i ≤ (len self).toNat) :
    (active self).take i = (storage self).toList.take i := by
  simp [active, List.take_take, Nat.min_eq_left h]

lemma take_min_take {i len : Nat} {l : List α} (h : i ≤ len) :
    List.take (min i len) (List.take len l) = List.take i l := by
  simp [Nat.min_eq_left h, List.take_take]

-- TODO: i think this could benefit from some other U32 arithimetic lemmas we have
lemma decide_ofNat_eq_toNat {i : Nat} {x : U 32} (pf : i < 2 ^ 32) :
    decide (BitVec.ofNat 32 i = x) = decide (i = x.toNat) := by
  by_cases hxi : i = x.toNat
  · have hbx : BitVec.ofNat 32 i = x := by
      simp [hxi, bitvec_ofNat_eq_of_toNat_eq (i := i) (x := x) hxi]
    simp [hxi, hbx]
  · have pf' : i < 4294967296 := by
      simpa using pf
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

lemma decide_lt_succ_eq_bv {i : Nat} {x : U 32} (pf : i < 2 ^ 32) :
    decide (x.toNat < i + 1) =
      (decide (x.toNat < i) || decide (BitVec.ofNat 32 i = x)) := by
  have h := decide_lt_succ_eq (a := x.toNat) (b := i)
  have h' : decide (x.toNat = i) = decide (BitVec.ofNat 32 i = x) := by
    simpa [eq_comm] using (decide_ofNat_eq_toNat (i := i) (x := x) pf).symm
  simpa [h'] using h

theorem new_storage_len_spec {p T MaxLen} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::new».call h![T, MaxLen] h![])
      (fun r =>
        storage r = List.Vector.replicate MaxLen.toNat (Tp.zero p T) ∧
        len r = 0) := by
  enter_decl
  steps
  subst_vars
  constructor <;> rfl

theorem new_wellFormed_spec {p T MaxLen} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::new».call h![T, MaxLen] h![])
      (fun r => len r = 0 ∧ wellFormed r) := by
  enter_decl
  steps
  subst_vars
  constructor
  · rfl
  · constructor
    · simp [bounded, len]
    · intro i _ hhi
      change (List.Vector.replicate MaxLen.toNat (Tp.zero p T)).get ⟨i, hhi⟩ = Tp.zero p T
      simp [List.Vector.get_replicate (n := MaxLen.toNat) (a := Tp.zero p T) ⟨i, hhi⟩]

theorem new_spec {p T MaxLen} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::new».call h![T, MaxLen] h![])
      (fun r => len r = 0 ∧ bounded r) := by
  enter_decl
  steps
  subst_vars
  constructor
  · rfl
  · simp [bounded, len]

theorem get_unchecked_spec {p T MaxLen self index}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (storage self)[index.toNat]'hindex) := by
  enter_decl
  steps
  simpa [storage]

theorem get_spec {p T MaxLen self index}
    (hbounded : bounded self)
    (hindex : index.toNat < (len self).toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (storage self)[index.toNat]'(lt_of_lt_of_le hindex hbounded)) := by
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex hbounded
  enter_decl
  steps [get_unchecked_spec (hindex := hindex_max)]
  assumption

theorem set_unchecked_spec {p T MaxLen selfRef self index value}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set_unchecked».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ => [selfRef ↦ ⟨bvTp T MaxLen, withStorageAt self ⟨index.toNat, hindex⟩ value⟩]) := by
  enter_decl
  steps
  aesop

theorem set_spec {p T MaxLen selfRef self index value}
    (hbounded : bounded self)
    (hindex : index.toNat < (len self).toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ =>
        [selfRef ↦ ⟨bvTp T MaxLen, withStorageAt self ⟨index.toNat, lt_of_lt_of_le hindex hbounded⟩ value⟩]) := by
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex hbounded
  enter_decl
  steps [set_unchecked_spec (hindex := hindex_max)]

theorem push_spec {p T MaxLen selfRef self elem}
    (hpush : (len self).toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::push».call h![T, MaxLen]
        h![selfRef, elem])
      (fun _ => [selfRef ↦ ⟨bvTp T MaxLen, pushed self elem hpush⟩]) := by
  enter_decl
  steps
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      [selfRef ↦ ⟨bvTp T MaxLen, withStorageAt self ⟨(len self).toNat, hpush⟩ elem⟩]))
  ·
    steps
    subst_vars
    simp [bvTp, modify_head_array_some (v := self) (idx := len self) (value := elem) hpush]
    simp [withStorageAt, withStorage, storage, len]
  ·
    intro _
    steps

theorem len_spec {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r = len self) := by
  enter_decl
  steps
  simpa [len]

theorem max_len_spec {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::max_len».call h![T, MaxLen]
        h![self])
      (fun r => r = MaxLen) := by
  enter_decl
  steps
  assumption

theorem storage_spec {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::storage».call h![T, MaxLen]
        h![self])
      (fun r => r = storage self) := by
  enter_decl
  steps
  simpa [storage]

theorem pop_spec {p T MaxLen selfRef self}
    (hnonzero : (0 : U 32) < len self)
    (hlast : (len self - 1).toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::pop».call h![T, MaxLen]
        h![selfRef])
      (fun r =>
        ⟦r = (storage self)[(len self - 1).toNat]'hlast⟧ ⋆
        [selfRef ↦ ⟨bvTp T MaxLen, popped self hlast⟩]) := by
  enter_decl
  steps
  apply (STHoare.letIn_intro (Q := fun _ => [selfRef ↦ ⟨bvTp T MaxLen, popped self hlast⟩]))
  ·
    steps
    subst_vars
    simp [popped, withStorageAt, withLen, withStorage, storage, len, withStorageAt_withLen, replaceTuple'_head_tail_comm, bvTp]
    congr
  ·
    intro _
    steps
    subst_vars
    simp [storage, len]
    rfl

theorem from_parts_unchecked_spec {p T MaxLen array l}
    (hbounded : l ≤ MaxLen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts_unchecked».call
        h![T, MaxLen] h![array, l])
      (fun r => storage r = array ∧ len r = l ∧ bounded r) := by
  enter_decl
  steps
  subst_vars
  constructor
  · rfl
  constructor
  · rfl
  · simpa [bounded, len] using hbounded

theorem extend_from_array_spec {p T MaxLen Len selfRef self array}
    (hspace : len self + Len ≤ MaxLen) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_array».call
        h![T, MaxLen, Len] h![selfRef, array])
      (fun _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]) := by
  enter_decl
  steps
  loop_inv nat fun _ _ _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]
  · sl
  · simp
  · intro i hlo hhi
    steps
  · steps

theorem extend_from_slice_spec {p T MaxLen selfRef self slice} :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_slice».call
        h![T, MaxLen] h![selfRef, slice])
      (fun _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]) := by
  enter_decl
  steps
  loop_inv nat fun _ _ _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]
  · sl
  · simp
  · intro i hlo hhi
    steps
  · steps

theorem extend_from_bounded_vec_spec {p T MaxLen Len selfRef self vec}
    (hbounded_vec : bounded vec) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_bounded_vec».call
        h![T, MaxLen, Len] h![selfRef, vec])
      (fun _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]) := by
  enter_decl
  steps [len_spec]
  all_goals (try exact ())
  apply (STHoare.letIn_intro (Q := fun _ => ∃∃ v', [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]))
  · steps
    apply STHoare.ite_intro_of_false
    · simp
    · steps
      apply (STHoare.letIn_intro (Q := fun _ =>
        ∃∃ v',
          [exceeded_len ↦ ⟨.bool, decide (append_len.toNat < Len.toNat)⟩] ⋆
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩]))
      ·
        loop_inv nat (fun i _ _ =>
          ∃∃ v',
            [exceeded_len ↦ ⟨.bool, decide (append_len.toNat < i)⟩] ⋆
            [selfRef ↦ ⟨bvTp T MaxLen, v'⟩])
        ·
          have hlt0 : ¬ (append_len.toNat < 0) := by
            exact Nat.not_lt_zero _
          -- Base case `i = 0`: `append_len.toNat < 0` is false.
          simp (config := { failIfUnchanged := false }) [hlt0]
          -- Simplify the ramified-frame entailment produced by `loop_inv nat`.
          sl unsafe
          -- Now finish by unfolding `⋆` and instantiating the remaining frame `?Q` with `⊤`.
          intro st hpre
          rcases hpre with ⟨st₁, st₂, hdisj, hst, hst₁, hst₂⟩
          have hst₁' : st₁.vals = Finmap.singleton exceeded_len ⟨Tp.bool, false⟩ := by
            simpa [State.valSingleton] using hst₁
          have hst₂' : st₂.vals =
              Finmap.singleton selfRef ⟨«std-1.0.0-beta.12::collections::bounded_vec::BoundedVec».tp h![T, MaxLen], self⟩ := by
            simpa [State.valSingleton] using hst₂

          -- Canonical heap chunk for the `exceeded_len` cell: keep lambdas empty so we can move any
          -- lambdas from the precondition's left chunk into the right chunk.
          let vf : State p := ⟨Finmap.singleton exceeded_len ⟨Tp.bool, false⟩, ∅⟩
          let st₂' : State p := ⟨st₂.vals, st₁.lambdas ∪ st₂.lambdas⟩

          -- `⋆ ?Q` frame: take `?Q` to be `⊤` on the empty heap.
          refine ⟨st, (∅ : State p), by simp, by simp, ?_, ?_⟩
          · -- main postcondition heap (the loop invariant package)
            dsimp
            refine ⟨st₂', ?_, ?_, ?_, ?_⟩
            · -- instantiate `?v := vf` and prove disjointness
              refine (show LawfulHeap.disjoint vf st₂' from ?_)
              have hvals : (Finmap.singleton exceeded_len ⟨Tp.bool, false⟩).Disjoint st₂.vals := by
                simpa [hst₁'] using hdisj.1
              refine And.intro ?_ ?_
              · simpa [vf, st₂'] using hvals
              ·
                rw [Finmap.Disjoint.symm_iff]
                simp [vf, st₂']
            · -- heap equality (note `st₂'.lambdas` absorbs `st₁.lambdas`)
              simpa [vf, st₂', State.union_parts, hst₁'] using hst
            · refine ⟨(by simp), ?_⟩
              simp [vf, State.valSingleton]
            · refine ⟨self, ?_⟩
              -- `st₂'` preserves `st₂`'s values.
              simp [st₂', hst₂', State.valSingleton]
          · trivial
        ·
          -- Drop the extra frame `(∃∃ v, ⟦v⟧) ⋆ ?Q`, then drop the unused existential `h`.
          apply SLP.entails_trans
          ·
            -- `A ⋆ ((∃∃ v, ⟦v⟧) ⋆ ?Q) ⊢ A ⋆ ⊤`
            exact (SLP.ent_drop_left (Q := (∃∃ h,
              ∃∃ v',
                [ exceeded_len ↦ ⟨Tp.bool, decide (BitVec.toNat append_len < BitVec.toNat Len)⟩ ] ⋆
                  [ selfRef ↦ ⟨bvTp T MaxLen, v'⟩ ]))
              (H := (∃∃ v, ⟦v⟧) ⋆ ?Q))
          ·
            -- Now show `A ⋆ ⊤ ⊢ A' ⋆ ⊤` by monotonicity on the left component.
            apply SLP.star_mono_r
            intro st hA
            -- `∃ h, ∃ v', R v'` entails `∃ v', R v'`
            rcases hA with ⟨h, v', hv'⟩
            exact ⟨v', hv'⟩
        ·
          intro i hlo hhi
          -- Loop body: update `exceeded_len` then conditionally write into `self`.
          -- The invariant only tracks the `exceeded_len` ref and `selfRef` as a whole.
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
          steps
          -- FIXME: exact ⟨⟩ "bug" here after steps
          all_goals (try exact ())
          apply STHoare.ite_intro
          · intro hcond
            steps
            -- `get_unchecked` needs an index-in-bounds proof; here `i < Len.toNat`.
            have hindex : (BitVec.ofNat 32 i).toNat < Len.toNat :=
              toNat_ofNat_lt_of_lt_maxLen (MaxLen := Len) (i := i) hhi
            -- Important: pass `p`/`T` explicitly so `get_unchecked_spec` doesn't get stuck with
            -- metavariables in the expected `self` type.
            steps [get_unchecked_spec (p := p) (T := T) (MaxLen := Len) (self := vec)
              (index := BitVec.ofNat 32 i) (hindex := hindex)]
            steps
            -- normalize the boolean update to match `decide (append_len.toNat < i+1)`
            simp_all [decide_lt_succ_eq_bv (x := len vec) (pf := pf)]
            -- At this point the goal is mostly a `let` + `modifyLens` + `skip` sequence.
            -- `steps` knows the builtin rules for `modifyLens` and `letIn`; the remaining SL
            -- bookkeeping is handled by `sl`.
            steps [get_unchecked_spec (p := p) (T := T) (MaxLen := Len) (self := vec)
              (index := BitVec.ofNat 32 i) (hindex := hindex)]
          · intro hcond
            steps
            simp_all [decide_lt_succ_eq_bv (x := len vec) (pf := pf)]
      · intro _
        steps
  · intro _
    steps

theorem from_array_spec {p T MaxLen Len array}
    (hbounded : Len ≤ MaxLen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_array».call
        h![T, MaxLen, Len] h![array])
      (fun r => bounded r) := by
  enter_decl
  steps [new_spec]
  rename_i vecVal
  steps [extend_from_array_spec]
  · subst_vars
    simpa using vecVal.2
  · rw [vecVal.1]
    simpa using hbounded

-- README: from here onwards we have the `sorry`'ed proofs
theorem any_spec {p T MaxLen Env self f fb}
    (hbounded : bounded self)
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : Bool) (e : T.denote p),
      (ip ++ [e] <+: active self) →
        STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ∨ r))) :
    STHoare p env
      (inv [] false ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::any».call h![T, MaxLen, Env]
        h![self, f])
      (fun r => inv (active self) r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  all_goals (try exact ())
  step_as
      ([ret ↦ ⟨.bool, false⟩] ⋆ inv [] false ⋆ [λf ↦ fb])
      (fun _ => ∃∃ b, [ret ↦ ⟨.bool, b⟩] ⋆ inv (active self) b ⋆ [λf ↦ fb])
  · steps
    apply STHoare.ite_intro_of_false
    · simp
    · steps
      loop_inv nat fun i _ _ =>
        ∃∃ b,
          [ret ↦ ⟨.bool, b⟩] ⋆
          [exceeded_len ↦ ⟨.bool, decide ((len self).toNat < i)⟩] ⋆
          inv ((active self).take (min i (len self).toNat)) b ⋆
          [λf ↦ fb]
      ·
        have hlt0 : ¬ ((len self).toNat < 0) := by
          exact Nat.not_lt_zero _
        simp [hlt0]
        sl
      · simp
      · intro i hlo hhi
        steps
        all_goals (try exact ())
        apply STHoare.ite_intro
        · intro hcond
          steps
          simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
            zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
            BitVec.toNat_ofNatLT, active, storage, List.Vector.toList_take, List.get_eq_getElem,
            List.getElem_take]
          generalize_proofs
          rename Tp.denote p .bool => b
          have hcond' := by
            simpa using hcond
          rcases hcond' with ⟨hi_le, hi_ne_bv⟩
          have hi_ne : i ≠ (len self).toNat := by
            intro hi_eq
            apply hi_ne_bv
            simpa using
              (bitvec_ofNat_eq_of_toNat_eq (i := i)
                (x := Builtin.indexTpl self Builtin.Member.head.tail) hi_eq)
          have hi_lt : i < (len self).toNat := by
            exact lt_of_le_of_ne hi_le hi_ne
          have hi_lt_max : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have := inv_spec
            ((active self).take i)
            b
            ((storage self).toList[i]'(by
              have : i < (storage self).toList.length := by
                simpa [storage, List.Vector.toList_length] using hi_lt_max
              exact this))
            (by
              simpa using (active_prefix_storage (self := self) (hbounded := hbounded) (hi := hi_lt)))
          steps [STHoare.callLambda_intro (hlam := this)]
          . sorry
          . sorry
          . sorry
          -- steps [STHoare.genericTotalPureBuiltin_intro (b := Builtin.bOr) (h := rfl)]
          -- steps
          -- simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.forall_bool, Bool.false_or,
          --   Bool.true_or, List.take_append_getElem, Lens.modify, Option.get_some]
          -- simp [active, List.take_take, Nat.min_eq_left (Nat.le_of_lt hi_lt),
          --   decide_lt_succ_eq_bv (x := len self) (pf := pf)]
          -- sl
        · intro hcond
          steps
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have pf' : i < 4294967296 := by
            simpa using pf
          simp [Lens.modify, Lens.get, Option.get_some,
            decide_lt_succ_eq_bv (x := len self) (pf := pf),
            bitvec_ofNatLT_eq_ofNat (i := i) pf] at *
          have hcond' : i ≤ (len self).toNat → BitVec.ofNat 32 i = len self := by
            simpa using hcond
          have hnot_lt : ¬ i < (len self).toNat := by
            intro hlt
            have h_eq : BitVec.ofNat 32 i = len self := hcond' (Nat.le_of_lt hlt)
            have h_eq_toNat : (BitVec.ofNat 32 i).toNat = (len self).toNat := by
              simpa using congrArg BitVec.toNat h_eq
            have hmod : i % 4294967296 = i := Nat.mod_eq_of_lt pf'
            have : i = (len self).toNat := by
              have h_eq_toNat' : i % 4294967296 = (len self).toNat := by
                simpa [BitVec.toNat_ofNat] using h_eq_toNat
              simpa [hmod] using h_eq_toNat'
            exact (Nat.ne_of_lt hlt) this
          have hi_ge : (len self).toNat ≤ i := by
            exact Nat.le_of_not_lt hnot_lt
          have hi_ge_succ : (len self).toNat ≤ i + 1 := by
            exact Nat.le_trans hi_ge (Nat.le_succ i)
          have hdec :
              decide ((len self).toNat < i + 1) =
                (decide ((len self).toNat < i) ||
                  decide (BitVec.ofNat 32 i = Builtin.indexTpl self Builtin.Member.head.tail)) := by
            simpa using (decide_lt_succ_eq_bv (x := len self) (pf := pf))
          simp [active, List.take_take, Nat.min_eq_right hi_ge, min_succ_eq_right hi_ge,
            hdec, Lens.modify, Lens.get, Option.get_some,
            bitvec_ofNatLT_eq_ofNat (i := i) pf]
          sl
          have pf' : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          simp [Lens.modify, Lens.get, Option.get_some]
          have hb := decide_lt_succ_eq_bv (i := i) (x := len self) (pf := pf')
          exact congrArg (fun b => Sigma.mk Tp.bool b) hb.symm
      · simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.forall_bool, Bool.false_or,
        Bool.true_or, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
        SLP.star_true, active, List.length_take, List.Vector.toList_length]
        have hmin := Nat.min_eq_right hbounded
        simp [hmin, List.take_length, List.take_take]
        steps
  · steps
    subst_vars
    sl

theorem map_spec {p T MaxLen U Env self f fb}
    (hbounded : bounded self)
    (inv : List (T.denote p) → List (U.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : List (U.denote p)) (e : T.denote p),
      (ip ++ [e] <+: active self) →
        STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ++ [r]))) :
    STHoare p env
      (inv [] [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::map».call h![T, MaxLen, U, Env]
        h![self, f])
      (fun r => inv (active self) (active r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps [new_spec]
  steps [len_spec]
  all_goals (try exact ())
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v, [ret ↦ ⟨bvTp U MaxLen, v⟩] ⋆ ⟦len v = len self⟧ ⋆
        inv (active self) (active v) ⋆ [λf ↦ fb]))
  · apply STHoare.ite_intro_of_false
    · simp
    · steps
      loop_inv nat fun i _ _ =>
        ∃∃ v,
          [ret ↦ ⟨bvTp U MaxLen, v⟩] ⋆
          ⟦len v = len self⟧ ⋆
          inv ((active self).take (min i (len self).toNat))
            ((storage v).toList.take (min i (len self).toNat)) ⋆
          [λf ↦ fb]
      · simp [len_modify_head_tail]
        sl
        sorry
      · simp
      · intro i hlo hhi
        steps [len_spec]
        apply STHoare.ite_intro
        · intro hcond
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have hi_lt : i < (len self).toNat := by
            exact nat_lt_of_bv_lt (x := len self) pf (by simpa using hcond)
          have hi_lt_max : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
          have hindex : (BitVec.ofNat 32 i).toNat < MaxLen.toNat := by
            exact toNat_ofNat_lt_of_lt_maxLen (MaxLen := MaxLen) hi_lt_max
          steps [get_unchecked_spec (hindex := sorry)]
          have hi_le : i ≤ (len self).toNat := Nat.le_of_lt hi_lt
          have hi_le_max : i ≤ MaxLen.toNat := Nat.le_of_lt hi_lt_max
          simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
            zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
            BitVec.toNat_ofNatLT, active, storage, List.Vector.toList_take, List.get_eq_getElem,
            List.getElem_take]
          simp [Nat.min_eq_left hi_le] at *
          generalize_proofs
          rename Tp.denote p (bvTp U MaxLen) => v
          have := inv_spec
            ((active self).take i)
            ((storage v).toList.take i)
            ((storage self).toList[i]'(by
              have : i < (storage self).toList.length := by
                have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                simpa [storage, List.Vector.toList_length] using hi_lt_max'
              exact this))
            (by
              simpa using (active_prefix_storage (self := self) (hbounded := hbounded) (hi := hi_lt)))
          have this' :
              STHoare p env
                (inv (List.take i (List.take (len self).toNat (storage self).toList))
                  ((storage v).toList.take i))
                (fb h![((storage self).toList[i]'(by
                  have : i < (storage self).toList.length := by
                    have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                    simpa [storage, List.Vector.toList_length] using hi_lt_max'
                  exact this))])
                (fun r =>
                  inv
                    (List.take i (List.take (len self).toNat (storage self).toList) ++
                      [(storage self).toList[i]'(by
                        have : i < (storage self).toList.length := by
                          have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                          simpa [storage, List.Vector.toList_length] using hi_lt_max'
                        exact this)])
                    ((storage v).toList.take i ++ [r])) := by
            simpa [active, List.take_take, Nat.min_eq_left hi_le] using this
          steps [STHoare.callLambda_intro (hlam := this')]
          rename_i r
          simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
            BitVec.toNat_ofNatLT, List.Vector.toList_take, List.take_append_getElem, Lens.modify,
            Lens.get, Access.modify, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some,
            Option.bind_fun_some, Option.get_some, List.Vector.toList_set]
          -- have hlen : i < ((storage v).toList.set i r).length := by simp_all
          try
            (simp [List.take_succ_eq_append_getElem hlen, List.getElem_set hlen,
              List.take_set_of_le ()])
          sl
          . sorry
          . sorry
          . sorry
        · intro hcond
          steps
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have hi_ge : (len self).toNat ≤ i := by
            exact nat_le_of_bv_le (x := len self) pf (by simpa using hcond)
          simp [Nat.min_eq_right, hi_ge]
          sl
          . sorry
          . assumption
          . sorry
      · steps
        all_goals (try sl)
        simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
          BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
          List.Vector.toList_take, active, List.length_take, List.Vector.toList_length]
        rename Tp.denote p (bvTp U MaxLen) => v
        rename_i a
        have hlen :
            Builtin.indexTpl v Builtin.Member.head.tail =
              Builtin.indexTpl self Builtin.Member.head.tail := by
          simpa [len] using a
        have hmin : min MaxLen.toNat (len self).toNat = (len self).toNat := by
          exact Nat.min_eq_right hbounded
        simp [hmin, List.take_length, List.take_take, hlen]
        sl
        assumption
  · intro _
    apply Lampe.Steps.pull_exi
    intro v
    steps
    all_goals (try sl)
    subst_vars
    sl

-- structurally developed but have a few holes
theorem mapi_spec {p T MaxLen U Env self f fb}
    (hbounded : bounded self)
    (inv : List (T.denote p) → List (U.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : List (U.denote p)) (e : T.denote p),
      (ip ++ [e] <+: active self) →
        STHoare p env (inv ip op) (fb h![ip.length, e]) (fun r => inv (ip ++ [e]) (op ++ [r]))) :
    STHoare p env
      (inv [] [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::mapi».call h![T, MaxLen, U, Env]
        h![self, f])
      (fun r => inv (active self) (active r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps [new_spec]
  steps [len_spec]
  all_goals (try exact ())
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v, [ret ↦ ⟨bvTp U MaxLen, v⟩] ⋆ ⟦len v = len self⟧ ⋆
        inv (active self) (active v) ⋆ [λf ↦ fb]))
  · apply STHoare.ite_intro_of_false
    · simp
    · steps
      loop_inv nat fun i _ _ =>
        ∃∃ v,
          [ret ↦ ⟨bvTp U MaxLen, v⟩] ⋆
          ⟦len v = len self⟧ ⋆
          inv ((active self).take (min i (len self).toNat))
            ((storage v).toList.take (min i (len self).toNat)) ⋆
          [λf ↦ fb]
      · simp [len_modify_head_tail]
        sl
        sorry
      · simp
      · intro i hlo hhi
        steps [len_spec]
        apply STHoare.ite_intro
        · intro hcond
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have hi_lt : i < (len self).toNat := by
            exact nat_lt_of_bv_lt (x := len self) pf (by simpa using hcond)
          have hi_lt_max : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
          have hindex : (BitVec.ofNat 32 i).toNat < MaxLen.toNat := by
            exact toNat_ofNat_lt_of_lt_maxLen (MaxLen := MaxLen) hi_lt_max
          steps [get_unchecked_spec (hindex := sorry)]
          have hi_le : i ≤ (len self).toNat := Nat.le_of_lt hi_lt
          have hi_le_max : i ≤ MaxLen.toNat := Nat.le_of_lt hi_lt_max
          simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
            EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, List.Vector.toList_take,
            Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
            BitVec.toNat_ofNatLT, active, storage, List.get_eq_getElem, List.getElem_take]
          simp [Nat.min_eq_left hi_le] at *
          generalize_proofs
          rename Tp.denote p (bvTp U MaxLen) => v
          have ip_len : ((active self).take i).length = i := by
            simp [active, List.length_take, List.Vector.toList_length, hbounded, hi_lt,
              Nat.min_eq_left]
            sorry
          have := inv_spec
            ((active self).take i)
            ((storage v).toList.take i)
            ((storage self).toList[i]'(by
              have : i < (storage self).toList.length := by
                have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                simpa [storage, List.Vector.toList_length] using hi_lt_max'
              exact this))
            (by
              simpa using (active_prefix_storage (self := self) (hbounded := hbounded) (hi := hi_lt)))
          have this' :
              STHoare p env (inv ((active self).take i) ((storage v).toList.take i))
                (fb h![BitVec.ofNatLT i pf, (storage self).toList[i]'(by
                  have : i < (storage self).toList.length := by
                    have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                    simpa [storage, List.Vector.toList_length] using hi_lt_max'
                  exact this)])
                (fun r => inv ((active self).take i ++ [(storage self).toList[i]'(by
                  have : i < (storage self).toList.length := by
                    have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                    simpa [storage, List.Vector.toList_length] using hi_lt_max'
                  exact this)])
                  ((storage v).toList.take i ++ [r])) := by
            simpa [ip_len, bitvec_ofNatLT_eq_ofNat (i := i) pf] using this
          have this'' :
              STHoare p env
                (inv (List.take i (List.take (len self).toNat (storage self).toList))
                  ((storage v).toList.take i))
                (fb h![BitVec.ofNatLT i pf, (storage self).toList[i]'(by
                  have : i < (storage self).toList.length := by
                    have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                    simpa [storage, List.Vector.toList_length] using hi_lt_max'
                  exact this)])
                (fun r =>
                  inv
                    (List.take i (List.take (len self).toNat (storage self).toList) ++
                      [(storage self).toList[i]'(by
                        have : i < (storage self).toList.length := by
                          have hi_lt_max' : i < MaxLen.toNat := lt_of_lt_of_le hi_lt hbounded
                          simpa [storage, List.Vector.toList_length] using hi_lt_max'
                        exact this)])
                    ((storage v).toList.take i ++ [r])) := by
            simpa [active, List.take_take, Nat.min_eq_left hi_le, ip_len,
              bitvec_ofNatLT_eq_ofNat (i := i) pf] using this'
          steps [STHoare.callLambda_intro (hlam := this'')]
          rename_i r
          simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
            List.Vector.toList_take, List.length_take, List.Vector.toList_length, BitVec.toNat_ofNat,
            Nat.reducePow, List.take_append_getElem, Lens.modify, Lens.get, Access.modify, ↓reduceDIte,
            Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some, Option.get_some,
            List.Vector.toList_set]
          -- have hlen : i < ((storage v).toList.set i r).length := by simp_all
          try
            (simp [List.take_succ_eq_append_getElem hlen, List.getElem_set hlen,
              List.take_set_of_le ⟨⟩])
          sorry
        · intro hcond
          steps
          have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
          have hi_ge : (len self).toNat ≤ i := by
            exact nat_le_of_bv_le (x := len self) pf (by simpa using hcond)
          simp [Nat.min_eq_right, hi_ge]
          sl
          . sorry
          . assumption
          . sorry
      · steps
        all_goals (try sl)
        simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
          EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
          List.Vector.toList_take, active, List.length_take, List.Vector.toList_length]
        rename Tp.denote p (bvTp U MaxLen) => v
        rename_i a
        have hlen :
            Builtin.indexTpl v Builtin.Member.head.tail =
              Builtin.indexTpl self Builtin.Member.head.tail := by
          simpa [len] using a
        have hmin : min MaxLen.toNat (len self).toNat = (len self).toNat := by
          exact Nat.min_eq_right hbounded
        simp [hmin, List.take_length, List.take_take, hlen]
        sl
        assumption
  · intro _
    apply Lampe.Steps.pull_exi
    intro v
    steps
    all_goals (try sl)
    subst_vars
    sl

theorem for_each_spec {p T MaxLen Env self f fb}
    (hbounded : bounded self)
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (e : T.denote p),
      (ip ++ [e] <+: active self) →
        STHoare p env (inv ip) (fb h![e]) (fun _ => inv (ip ++ [e]))) :
    STHoare p env
      (inv [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::for_each».call h![T, MaxLen, Env]
        h![self, f])
      (fun _ => inv (active self) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  all_goals (try exact ())
  apply STHoare.ite_intro_of_false
  · simp
  · steps
    loop_inv nat fun i _ _ =>
      inv ((active self).take (min i (len self).toNat)) ⋆ [λf ↦ fb]
    · simp
      sl
    · simp
    · intro i hlo hhi
      steps [len_spec]
      apply STHoare.ite_intro
      · intro hcond
        have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
        have pf' : i < 4294967296 := by
          simpa using pf
        steps [get_unchecked_spec (hindex := by
          sorry
          -- simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pf'] using hhi
        )]
        simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
          zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt pf', active, storage, List.Vector.toList_take,
          List.get_eq_getElem, List.getElem_take]
        generalize_proofs
        have hi_lt : i < (len self).toNat := by
          exact nat_lt_of_bv_lt (x := len self) pf (by simpa using hcond)
        have := inv_spec
          ((active self).take i)
          ((storage self).toList[i]'(by
            have : i < (storage self).toList.length := by
              simpa [storage, List.Vector.toList_length] using hhi
            exact this))
          (by
            simpa using (active_prefix_storage (self := self) (hbounded := hbounded) (hi := hi_lt)))
        steps [STHoare.callLambda_intro (hlam := this)]
        -- simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
        --   BitVec.toNat_ofNatLT, List.Vector.toList_take, List.take_append_getElem]
        sl
        . sorry
        . sorry
        . sorry
      · intro hcond
        steps
        have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
        have hi_ge : (len self).toNat ≤ i := by
          exact nat_le_of_bv_le (x := len self) pf (by simpa using hcond)
        have hi_ge_succ : (len self).toNat ≤ i + 1 := by
          exact Nat.le_trans hi_ge (Nat.le_succ i)
        simp [active, List.take_take, Nat.min_eq_right hi_ge, min_succ_eq_right hi_ge]
        sl
    · steps
      all_goals (try sl)
      simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
        BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
        List.Vector.toList_take, active, List.length_take, List.Vector.toList_length]
      have hmin : min MaxLen.toNat (len self).toNat = (len self).toNat := by
        exact Nat.min_eq_right hbounded
      simp [hmin, List.take_length, List.take_take]
      sl

theorem for_eachi_spec {p T MaxLen Env self f fb}
    (hbounded : bounded self)
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (e : T.denote p),
      (ip ++ [e] <+: active self) →
        STHoare p env (inv ip) (fb h![ip.length, e]) (fun _ => inv (ip ++ [e]))) :
    STHoare p env
      (inv [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::for_eachi».call h![T, MaxLen, Env]
        h![self, f])
      (fun _ => inv (active self) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  all_goals (try exact ())
  apply STHoare.ite_intro_of_false
  · simp
  · steps
    loop_inv nat fun i _ _ =>
      inv ((active self).take (min i (len self).toNat)) ⋆ [λf ↦ fb]
    · simp
      sl
    · simp
    · intro i hlo hhi
      steps [len_spec]
      apply STHoare.ite_intro
      · intro hcond
        have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
        have pf' : i < 4294967296 := by
          simpa using pf
        steps [get_unchecked_spec (hindex := by
          sorry
        )]
        simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
          EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, List.Vector.toList_take,
          Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt pf', active, storage, List.get_eq_getElem,
          List.getElem_take]
        generalize_proofs
        have hi_lt : i < (len self).toNat := by
          exact nat_lt_of_bv_lt (x := len self) pf (by simpa using hcond)
        have hi_le : i ≤ (len self).toNat := Nat.le_of_lt hi_lt
        have hi_le_max : i ≤ MaxLen.toNat := Nat.le_of_lt hhi
        have ip_len : ((active self).take i).length = i := by
          simp [active, List.length_take, List.Vector.toList_length, hbounded, hi_lt,
            Nat.min_eq_left]
          sorry
        have := inv_spec
          ((active self).take i)
          ((storage self).toList[i]'(by
            have : i < (storage self).toList.length := by
              simpa [storage, List.Vector.toList_length] using hhi
            exact this))
          (by
            simpa using (active_prefix_storage (self := self) (hbounded := hbounded) (hi := hi_lt)))
        have this' :
            STHoare p env (inv ((active self).take i))
              (fb h![BitVec.ofNatLT i pf, (storage self).toList[i]'(by
                have : i < (storage self).toList.length := by
                  simpa [storage, List.Vector.toList_length] using hhi
                exact this)])
              (fun _ => inv ((active self).take i ++ [(storage self).toList[i]'(by
                have : i < (storage self).toList.length := by
                  simpa [storage, List.Vector.toList_length] using hhi
                exact this)])) := by
          simpa [ip_len, bitvec_ofNatLT_eq_ofNat (i := i) pf] using this
        steps [STHoare.callLambda_intro (hlam := this')]
        simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
          List.Vector.toList_take, List.length_take, List.Vector.toList_length, BitVec.toNat_ofNat,
          Nat.reducePow, List.take_append_getElem]
        sl
        . sorry
        . sorry
        . sorry
      · intro hcond
        steps
        have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
        have hi_ge : (len self).toNat ≤ i := by
          exact nat_le_of_bv_le (x := len self) pf (by simpa using hcond)
        have hi_ge_succ : (len self).toNat ≤ i + 1 := by
          exact Nat.le_trans hi_ge (Nat.le_succ i)
        simp [active, List.take_take, Nat.min_eq_right hi_ge, min_succ_eq_right hi_ge]
        sl
    · steps
      all_goals (try sl)
      simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
        EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
        List.Vector.toList_take, active, List.length_take, List.Vector.toList_length]
      have hmin : min MaxLen.toNat (len self).toNat = (len self).toNat := by
        exact Nat.min_eq_right hbounded
      simp [hmin, List.take_length, List.take_take]
      sl

theorem from_parts_spec {p T MaxLen array l}
    (hbounded : l ≤ MaxLen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts».call
        h![T, MaxLen] h![array, l])
      (fun r => bounded r) := by
  enter_decl
  steps
  all_goals (try exact ())
  apply (STHoare.letIn_intro
    (Q := fun _ => ∃∃ a, [array ↦ ⟨Tp.array T MaxLen, a⟩]))
  · apply STHoare.ite_intro_of_false
    · simp
    · steps
      loop_inv nat fun _ _ _ => ∃∃ a, [array ↦ ⟨Tp.array T MaxLen, a⟩]
      · sl
      · simp
      · intro i hlo hhi
        apply (STHoare.letIn_intro
          (Q := fun _ => ∃∃ a, [array ↦ ⟨Tp.array T MaxLen, a⟩]))
        · apply Lampe.Steps.pull_exi
          intro arrVal
          apply (STHoare.consequence
            (H₁ := [array ↦ ⟨Tp.array T MaxLen, arrVal⟩])
            (Q₁ := fun _ => [array ↦ ⟨Tp.array T MaxLen, arrVal⟩]))
          · exact SLP.entails_self
          · intro _
            sl
          · steps [STHoare.genericTotalPureBuiltin_intro (b := Builtin.uGeq) (h := rfl)]
        · intro b
          apply STHoare.ite_intro
          · intro _
            steps
          · intro _
            steps
      · steps
  · intro _
    steps
    subst_vars
    simpa [bounded, len] using hbounded

theorem eq_spec {p T MaxLen self other}
    {t_eq : «std-1.0.0-beta.12::cmp::Eq».hasImpl env h![] T}
    (array_eq :
      ∀ a b, STHoare p env ⟦⟧ («std-1.0.0-beta.12::cmp::Eq».eq h![] (T.array MaxLen) h![] h![] h![a, b])
        (fun r : Bool => ⟦r = (a = b)⟧)) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::cmp::Eq».eq h![] (bvTp T MaxLen) h![] h![] h![self, other])
      (fun _ : Bool => ⟦True⟧) := by
  resolve_trait
  steps [array_eq]
  apply STHoare.ite_intro
  · intro _
    steps [array_eq]
  · intro _
    steps

theorem from_trait_spec {p T Len MaxLen array}
    (hbounded : Len ≤ MaxLen) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::convert::From».from h![T.array Len] (bvTp T MaxLen) h![] h![] h![array])
  (fun r => bounded r) := by
  resolve_trait
  steps [from_array_spec (hbounded := hbounded)]
  assumption

/-! ## Spec Backlog

Theorem shape we want next (in proof-order):

1. Constructors and primitive accessors
   - `new_spec`: returns `wellFormed` value with `len = 0` and fully zeroed storage.
   - `get_unchecked_spec`: reads `storage[index]` (requires index-in-array precondition).
   - `get_spec`: same as `get_unchecked`, with extra checked precondition `index < len`.
   - `set_unchecked_spec`: updates `storage[index]`, length unchanged.
   - `set_spec`: same as `set_unchecked`, gated by `index < len`.

2. Core mutators
   - `push_spec`: pre `len < MaxLen`; post heap is exactly `[selfRef ↦ pushed self elem hpush]`.
   - `pop_spec`: pre `len > 0`; returns old last element; post heap is exactly `[selfRef ↦ popped self hlast]`.

3. Bulk extension
   - `extend_from_array_spec`
   - `extend_from_slice_spec`
   - `extend_from_bounded_vec_spec`
   Shared postcondition pattern:
   `active' = active ++ appendedPrefix` and `len' = len + appendedPrefix.length`.
   For `extend_from_bounded_vec`, we should prove both execution branches refine to the same
   abstract append behavior.

4. Higher-order traversal/mapping
   - `any_spec` (+ pure variant): result is `List.any` over `active`.
   - `map_spec`, `mapi_spec` (+ pure variants): mapped `active`, same length, zeroed tail.
   - `for_each_spec`, `for_eachi_spec`: callback is executed exactly over `active`.

5. Smart constructors and trait behavior
   - `from_array_spec`: static bound + append semantics.
   - `from_parts_spec`: enforces zeroed tail.
   - `from_parts_unchecked_spec`: only length bound; no zero-tail guarantee.
   - `eq_spec`: models Noir impl (`len` equality plus full-storage equality), with note that
     extensional equality on `active` requires `wellFormed` assumptions.
   - `from_trait_spec`: delegates to `from_array_spec`.
-/

/-! ## Scope Inventory (From `stdlib/src/collections/bounded_vec.nr`)

`BoundedVec` has no `unconstrained fn` declarations in its API impl.
So, under "public-facing constrained only", the proof target set is:

- `new`
- `get`
- `get_unchecked`
- `set`
- `set_unchecked`
- `push`
- `len`
- `max_len`
- `storage`
- `extend_from_array`
- `extend_from_slice`
- `extend_from_bounded_vec`
- `from_array`
- `pop`
- `any`
- `map`
- `mapi`
- `for_each`
- `for_eachi`
- `from_parts`
- `from_parts_unchecked`
- trait method `Eq::eq` for `BoundedVec`
- trait method `From<[T; Len]>::from` for `BoundedVec`

Excluded from proof scope:
- test module `bounded_vec_tests::*`
- test-only private helpers (`for_each_map`, `for_eachi_mapi`)
-/

end Lampe.Stdlib.Collections.BoundedVec
