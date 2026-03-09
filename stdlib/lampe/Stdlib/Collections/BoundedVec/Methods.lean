import Stdlib.Collections.BoundedVec.Core

namespace Lampe

theorem SLP.exists_mono [LawfulHeap α] {H H' : β → SLP α}
    (h : ∀ v, H v ⊢ H' v) : (∃∃ v, H v) ⊢ (∃∃ v, H' v) := by
  intro st hst; unfold SLP.exists' at *; rcases hst with ⟨v, hv⟩; exact ⟨v, h v st hv⟩

theorem SLP.lift_mono [LawfulHeap α] {P Q : Prop}
    (h : P → Q) : (⟦P⟧ : SLP α) ⊢ ⟦Q⟧ := by
  intro st hst; unfold SLP.lift at *; exact ⟨h hst.1, hst.2⟩

theorem SLP.exists_star_lift_mono [LawfulHeap α] {H : β → SLP α} {P Q : β → Prop}
    (h : ∀ v, P v → Q v) :
    (∃∃ v, H v ⋆ ⟦P v⟧) ⊢ (∃∃ v, H v ⋆ ⟦Q v⟧) :=
  SLP.exists_mono fun v => SLP.star_mono_l (SLP.lift_mono (h v))

theorem STHoare.consequence_post
    {P : SLP (State p)} {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare : STHoare p Γ P e Q₁) (h : ∀ v, Q₁ v ⊢ Q₂ v) :
    STHoare p Γ P e Q₂ :=
  STHoare.consequence SLP.entails_self (fun v => SLP.star_mono_r (h v)) h_hoare

end Lampe

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.12»

/-!
`collections::bounded_vec`

This file is the Hoare-logic layer for `BoundedVec`.

We are restarting the development to avoid baking in tuple-update helpers (`withLen`, `popped`, ...).
All method specs should be stated in terms of the semantic function `embed` and Lean `List`
operations; representation projections (`storage`, `len`) are used only as a bridge to the extracted
code during proofs.

First targets:
- `get_unchecked` (converges unconditionally, only constrained in-bounds, no storage mentioned in spec)
- `get` (requires in-bounds precondition, spec stated via `embed`)
-/

/-- Shared loop body step for `extend_from_*`. -/
local macro "extend_loop_step" hlenV:ident htakeV:ident
    hi32:ident hiMax:ident hMax_lt:ident
    hi_src:term : tactic =>
  `(tactic| (
    have _hi_lt := lt_of_lt_of_le $hiMax (Nat.le_of_lt $hMax_lt)
    have _hidx := extend_loop_idx_toNat $hlenV $hi32 _hi_lt
    constructor
    · simpa [len] using $hlenV
    · simp (config := {contextual := false})
        [storage, len, List.Vector.toList_set,
          (by simpa [len] using _hidx :
            (Builtin.indexTpl _ Builtin.Member.head.tail +
              BitVec.ofNat 32 _).toNat = _),
          List.Vector.get_eq_get_toList,
          List.get_eq_getElem, nat_mod_4294967296 $hi32]
      try simp [extend_loop_idx_mod $hlenV _hi_lt]
      simpa [len] using List.take_set_extends
        (by simpa [storage] using $htakeV)
        (by simpa [List.Vector.toList_length] using $hiMax)
        $hi_src))

private theorem SLP.singleton_entails_exists_star_lift
    {ref : Ref} {tp : Tp}
    {v : Tp.denote p tp}
    {P : Tp.denote p tp → Prop}
    (h : P v) :
    ([ref ↦ ⟨tp, v⟩] : SLP (State p))
      ⊢ (∃∃ v', [ref ↦ ⟨tp, v'⟩] ⋆ ⟦P v'⟧) := by
  intro st hst
  exact ⟨v, st, ∅, by simp, by simp, hst, h, rfl⟩

private theorem get_unchecked_concrete_spec {p T MaxLen self index}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (storage self)[index.toNat]'hindex) := by
  enter_decl
  steps
  simpa [storage]

private theorem get_concrete_spec {p T MaxLen self index}
    (hbounded : bounded self)
    (hindex : index.toNat < (len self).toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (storage self)[index.toNat]'(lt_of_lt_of_le hindex hbounded)) := by
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex hbounded
  enter_decl
  steps [get_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen) (self := self) (index := index) (hindex := hindex_max)]
  assumption

theorem get_unchecked_spec {p T MaxLen self index}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![self, index])
      (fun r => ∀ h : index.toNat < (embed self).length, r = (embed self)[index.toNat]'h) := by
  have hstorage : index.toNat < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using hindex
  exact STHoare.consequence_post
    (get_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
      (self := self) (index := index) (hindex := hindex))
    fun r st ⟨hr, hst⟩ => ⟨fun hlt => by
      have hr_list : r = (storage self).toList[index.toNat]'hstorage := by
        simpa [List.Vector.getElem_def] using hr
      have hx_rhs :
          (embed self)[index.toNat]'hlt = (storage self).toList[index.toNat]'hstorage := by
        simpa using
          (embed_getElem_toList (self := self) (i := index.toNat) (hxs := hlt) (hstorage := hstorage))
      exact hr_list.trans hx_rhs.symm, hst⟩

theorem get_spec {p T MaxLen self index}
    (hwf : wellFormed self)
    (hindex : index.toNat < (embed self).length) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (embed self)[index.toNat]'hindex) := by
  have hb : bounded self := bounded_of_wellFormed hwf
  have hlen : (embed self).length = (len self).toNat := hwf
  have hindex_len : index.toNat < (len self).toNat := by
    simpa [hlen] using hindex
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex_len hb
  have hstorage : index.toNat < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using hindex_max
  have hx_rhs :
      (embed self)[index.toNat]'hindex = (storage self).toList[index.toNat]'hstorage := by
    simpa using (embed_getElem_toList (self := self) (i := index.toNat) (hxs := hindex) (hstorage := hstorage))
  have hprec :
      STHoare p env ⟦⟧
        («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
          h![self, index])
        (fun r => r = (storage self)[index.toNat]'hindex_max) := by
    simpa using
      (get_concrete_spec (p := p) (T := T) (MaxLen := MaxLen) (self := self) (index := index)
        (hbounded := hb) (hindex := hindex_len))

  exact STHoare.consequence_post hprec fun r st ⟨hr, hst⟩ =>
    ⟨by
      have hr_list : r = (storage self).toList[index.toNat]'hstorage := by
        simpa [List.Vector.getElem_def] using hr
      exact hr_list.trans hx_rhs.symm, hst⟩

private theorem set_unchecked_concrete_spec {p T MaxLen selfRef self index value}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set_unchecked».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex⟩ value⟧) := by
  let vUpd : Repr p T MaxLen :=
    Builtin.replaceTuple' self Builtin.Member.head ((storage self).set ⟨index.toNat, hindex⟩ value)
  have hstate :
      STHoare p env
        [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
        («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set_unchecked».call h![T, MaxLen]
          h![selfRef, index, value])
        (fun _ =>
          [selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩]) := by
    enter_decl
    steps
    aesop
  have hlen : len vUpd = len self := by
    cases self; rfl
  have hstorage :
      storage vUpd =
        (storage self).set ⟨index.toNat, hindex⟩ value := by
    unfold vUpd storage; cases self; rfl
  exact STHoare.consequence_post hstate fun _ =>
    SLP.singleton_entails_exists_star_lift
      (And.intro hlen hstorage)

theorem set_unchecked_spec {p T MaxLen selfRef self index value}
    (hwf : wellFormed self)
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set_unchecked».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ => BV (MaxLen := MaxLen) selfRef ((embed self).set index.toNat value)) := by
  have hb : bounded self := bounded_of_wellFormed hwf
  exact STHoare.consequence_post
    (set_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
      (selfRef := selfRef) (self := self) (index := index) (value := value) (hindex := hindex))
    fun _ => SLP.exists_star_lift_mono fun v' ⟨hlen', hstorage'⟩ => by
      have hb' : bounded v' := by
        simpa [bounded, hlen'] using hb
      have hwf' : wellFormed v' := wellFormed_of_bounded hb'
      have hembed' : embed v' = (embed self).set index.toNat value := by
        exact embed_eq_set_of_storage_set (v := self) (v' := v')
          (i := index.toNat) (hi := hindex) (a := value) (hlen := hlen') (hstorage := hstorage')
      exact ⟨hwf', hembed'⟩

private theorem set_concrete_spec {p T MaxLen selfRef self index value}
    (hbounded : bounded self)
    (hindex : index.toNat < (len self).toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧
              storage v' = (storage self).set ⟨index.toNat, lt_of_lt_of_le hindex hbounded⟩ value⟧) := by
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex hbounded
  enter_decl
  steps_named [set_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
    (selfRef := selfRef) (self := self) (index := index) (value := value) (hindex := hindex_max)]
    as [v, hproj]
  rcases hproj with ⟨hlen', hstorage'⟩
  refine And.intro hlen' ?_
  have hstorageProof :
      (storage self).set ⟨index.toNat, hindex_max⟩ value =
        (storage self).set ⟨index.toNat, lt_of_lt_of_le hindex hbounded⟩ value := by
    simpa using
      (vector_set_proof_irrel (v := storage self) (i := index.toNat)
        (h1 := hindex_max) (h2 := lt_of_lt_of_le hindex hbounded) (x := value))
  exact hstorage'.trans hstorageProof

theorem set_spec {p T MaxLen selfRef self index value}
    (hwf : wellFormed self)
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ => BV (MaxLen := MaxLen) selfRef ((embed self).set index.toNat value)) := by
  have hbounded : bounded self := bounded_of_wellFormed hwf
  have hlen : (embed self).length = (len self).toNat := hwf
  have hindex_len : index.toNat < (len self).toNat := by
    simpa [hlen] using hindex
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex_len hbounded
  exact STHoare.consequence_post
    (set_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
      (selfRef := selfRef) (self := self) (index := index) (value := value)
      (hbounded := hbounded) (hindex := hindex_len))
    fun _ => SLP.exists_star_lift_mono fun v' ⟨hlen', hstorage'⟩ => by
      have hb' : bounded v' := by
        simpa [bounded, hlen'] using hbounded
      have hwf' : wellFormed v' := wellFormed_of_bounded hb'
      have hembed' : embed v' = (embed self).set index.toNat value := by
        exact embed_eq_set_of_storage_set (v := self) (v' := v')
          (i := index.toNat) (hi := hindex_max) (a := value) (hlen := hlen') (hstorage := hstorage')
      exact ⟨hwf', hembed'⟩

private theorem modify_head_array_some {p T MaxLen} {v : Tp.denote p (bvTp T MaxLen)} {idx : U 32}
    {value : Tp.denote p T} (hidx : idx.toNat < MaxLen.toNat) :
    (((Lens.nil.cons (Access.tuple Builtin.Member.head)).cons (Access.array idx)).modify v value) =
      some (Builtin.replaceTuple' v Builtin.Member.head ((storage v).set ⟨idx.toNat, hidx⟩ value)) := by
  simp [storage, hidx]

private theorem push_concrete_spec {p T MaxLen selfRef self elem}
    (hpush : (len self).toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::push».call h![T, MaxLen]
        h![selfRef, elem])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self + 1 ∧
              storage v' = (storage self).set ⟨(len self).toNat, hpush⟩ elem⟧) := by
  let vStor : Repr p T MaxLen :=
    Builtin.replaceTuple' self Builtin.Member.head ((storage self).set ⟨(len self).toNat, hpush⟩ elem)
  let vUpd : Repr p T MaxLen :=
    Builtin.replaceTuple' vStor Builtin.Member.head.tail (len self + 1)
  have hstate :
      STHoare p env
        [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
        («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::push».call h![T, MaxLen]
          h![selfRef, elem])
        (fun _ =>
          [selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩]) := by
    enter_decl
    steps
    apply (STHoare.letIn_intro
      (Q := fun _ =>
        [selfRef ↦ ⟨bvTp T MaxLen, vStor⟩]))
    ·
      steps_named
      simp [vStor, storage, len]
    ·
      intro _
      steps
  have hlen : len vUpd = len self + 1 := by
    unfold vUpd len; simp [Builtin.index_replaced_tpl]
  have hstorage :
      storage vUpd =
        (storage self).set ⟨(len self).toNat, hpush⟩ elem := by
    unfold vUpd vStor storage; cases self <;> rfl
  exact STHoare.consequence_post hstate fun _ =>
    SLP.singleton_entails_exists_star_lift
      (And.intro hlen hstorage)

theorem push_spec {p T MaxLen selfRef self elem}
    (hwf : wellFormed self)
    (hspace : (embed self).length < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::push».call h![T, MaxLen]
        h![selfRef, elem])
      (fun _ => BV (MaxLen := MaxLen) selfRef (embed self ++ [elem])) := by
  have hbounded : bounded self := bounded_of_wellFormed hwf
  have hlen : (embed self).length = (len self).toNat := hwf
  have hpush : (len self).toNat < MaxLen.toNat := by
    simpa [hlen] using hspace
  exact STHoare.consequence_post
    (push_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
      (selfRef := selfRef) (self := self) (elem := elem) (hpush := hpush))
    fun _ => SLP.exists_star_lift_mono fun v' ⟨hlen', hstorage'⟩ => by
      have hb' : bounded v' := by
        have hmax := u32_toNat_lt MaxLen
        have hx32 : (len self).toNat + 1 < 2 ^ 32 := by
          exact lt_of_le_of_lt (Nat.succ_le_of_lt hpush) hmax
        have htoNat_v' : (len v').toNat = (len self).toNat + 1 := by
          simpa [hlen', BitVec.toNat_add_one_of_lt (x := len self) hx32]
        have : (len v').toNat ≤ MaxLen.toNat := by
          have : (len self).toNat + 1 ≤ MaxLen.toNat := Nat.succ_le_of_lt hpush
          simpa [htoNat_v'] using this
        simpa [bounded] using this
      have hwf' : wellFormed v' := wellFormed_of_bounded hb'
      have hembed' : embed v' = embed self ++ [elem] := by
        exact embed_eq_append_of_storage_set_at_len (v := self) (v' := v') (a := elem)
          (hb := hbounded) (hpush := hpush) (hlen := hlen') (hstorage := hstorage')
      exact ⟨hwf', hembed'⟩

private theorem len_concrete_spec {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r = len self) := by
  enter_decl
  steps
  simpa [len]

theorem len_spec {p T MaxLen self}
    (hwf : wellFormed self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r.toNat = (embed self).length) := by
  have hlen : (embed self).length = (len self).toNat := hwf
  exact STHoare.consequence_post
    (len_concrete_spec (p := p) (T := T) (MaxLen := MaxLen) (self := self))
    fun r st ⟨hr, hst⟩ =>
      ⟨by
        have hrt : r.toNat = (len self).toNat := by
          simpa using congrArg BitVec.toNat hr
        exact hrt.trans hlen.symm, hst⟩

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

theorem new_spec {p T MaxLen} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::new».call h![T, MaxLen] h![])
      (fun r => wellFormed r ∧ len r = 0 ∧ embed r = []) := by
  enter_decl
  steps_named
  set r : Repr p T MaxLen :=
    HList.toTuple p h![List.Vector.replicate (BitVec.toNat MaxLen) (Tp.zero p T), (↑0 : U 32)]
      (some «std-1.0.0-beta.12::collections::bounded_vec::BoundedVec».name)
  have hlen0 : len r = 0 := rfl
  refine And.intro ?_ (And.intro ?_ ?_)
  · exact show wellFormed r by
      simp [wellFormed, embed, active, hlen0]
  · rfl
  · exact show embed r = [] by
      simp [embed, active, hlen0]

private lemma pop_preconditions {p T MaxLen} {self : Repr p T MaxLen}
    (hwf : wellFormed self) (hnonempty : embed self ≠ []) :
    ((0 : U 32) < len self) ∧ ((len self - (1 : U 32)).toNat < MaxLen.toNat) := by
  have hbounded : bounded self := bounded_of_wellFormed hwf
  have hlen : (embed self).length = (len self).toNat := hwf
  have hpos_embed : 0 < (embed self).length := by
    cases h : embed self with
    | nil => cases hnonempty h
    | cons _ _ => simp
  have hpos_len : 0 < (len self).toNat := by
    simpa [hlen] using hpos_embed
  have hnonzero : (0 : U 32) < len self := by
    rw [BitVec.lt_def]
    simpa using hpos_len
  have h1le : (1 : U 32) ≤ len self := by
    rw [BitVec.le_def]
    exact Nat.succ_le_of_lt hpos_len
  have htoNat_sub : (len self - (1 : U 32)).toNat = (len self).toNat - 1 := by
    simpa using (BitVec.toNat_sub_of_le (x := len self) (y := (1 : U 32)) h1le)
  have hpred : (len self).toNat - 1 < (len self).toNat :=
    Nat.pred_lt (Nat.ne_of_gt hpos_len)
  have hlastNat : (len self).toNat - 1 < MaxLen.toNat :=
    lt_of_lt_of_le hpred hbounded
  have hlast : (len self - (1 : U 32)).toNat < MaxLen.toNat := by
    rw [htoNat_sub]
    exact hlastNat
  exact ⟨hnonzero, hlast⟩

@[simp] private lemma indexTpl_head
    {p} {tp : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tps)) :
    Builtin.indexTpl tpl Builtin.Member.head = tpl.1 := by
  rfl

@[simp] private lemma indexTpl_head_tail
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) :
    Builtin.indexTpl tpl Builtin.Member.head.tail = tpl.2.1 := by
  rfl

@[simp] private lemma coe_one_u32' :
    ((↑1 : U 32) = (1#32)) := by
  decide

@[simp] private lemma replaceTuple'_head_fst
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp) :
    (Builtin.replaceTuple' tpl Builtin.Member.head v).1 = v := by
  rfl

@[simp] private lemma replaceTuple'_head_tail_snd
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp) :
    (Builtin.replaceTuple' tpl Builtin.Member.head v).2 = tpl.2 := by
  rfl

@[simp] private lemma replaceTuple'_headTail_fst
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp') :
    (Builtin.replaceTuple' tpl Builtin.Member.head.tail v).1 = tpl.1 := by
  rfl

@[simp] private lemma replaceTuple'_headTail_snd_head
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp') :
    (Builtin.replaceTuple' tpl Builtin.Member.head.tail v).2.1 = v := by
  rfl

private theorem pop_concrete_spec {p T MaxLen selfRef self}
    (hnonzero : (0 : U 32) < len self)
    (hlast : (len self - (1 : U 32)).toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::pop».call h![T, MaxLen]
        h![selfRef])
      (fun r =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self - (1 : U 32) ∧
              storage v' =
                (storage self).set ⟨(len self - (1 : U 32)).toNat, hlast⟩ (Tp.zero p T) ∧
              r = (storage self)[(len self - (1 : U 32)).toNat]'hlast⟧) := by
  enter_decl
  steps
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      (∃∃ v',
        [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦len v' = len self - (1 : U 32) ∧
            storage v' =
              (storage self).set ⟨(len self - (1 : U 32)).toNat, hlast⟩ (Tp.zero p T)⟧ : SLP (State p))))
  ·
    steps_named
    cases self
    simp [len, storage]
    exact coe_one_u32'
  ·
    intro r
    steps_named as [v, hproj]
    have ha :
        len v = len self - (1 : U 32) ∧
          storage v =
            (storage self).set ⟨BitVec.toNat (len self - (1 : U 32)), hlast⟩ (Tp.zero p T) := by
      simpa using (by
        assumption :
          len v = len self - (1 : U 32) ∧
            storage v =
              (storage self).set ⟨BitVec.toNat (len self - (1 : U 32)), hlast⟩ (Tp.zero p T))
    rcases ha with ⟨hlen', hstorage'⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hlen'
    · simpa using hstorage'
    ·
      simp [storage, len]
      set i : Nat := (4294967295 + BitVec.toNat self.2.1) % 4294967296
      change List.Vector.get self.1 ⟨i, ?_⟩ = List.Vector.get self.1 ⟨i, ?_⟩
      exact vector_get_proof_irrel (v := self.1) (i := i) _ _

theorem pop_spec {p T MaxLen selfRef self}
    (hwf : wellFormed self)
    (hnonempty : embed self ≠ []) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::pop».call h![T, MaxLen]
        h![selfRef])
      (fun r =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦wellFormed v' ∧ embed v' = (embed self).dropLast ∧ r = (embed self).getLast hnonempty⟧) := by
  have hbounded : bounded self := bounded_of_wellFormed hwf
  obtain ⟨hnonzero, hlast⟩ := pop_preconditions (self := self) hwf hnonempty
  exact STHoare.consequence_post
    (pop_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
      (selfRef := selfRef) (self := self) (hnonzero := hnonzero) (hlast := hlast))
    fun r => SLP.exists_star_lift_mono fun v' ⟨hlen', hstorage', hret⟩ => by
      have hb' : bounded v' := by
        have : (len v').toNat ≤ MaxLen.toNat := by
          have : (len self - (1 : U 32)).toNat ≤ MaxLen.toNat := Nat.le_of_lt hlast
          simpa [hlen'] using this
        simpa [bounded] using this
      have hwf' : wellFormed v' := wellFormed_of_bounded hb'
      have hembed' : embed v' = (embed self).dropLast := by
        exact embed_eq_dropLast_of_pop_update (v := self) (v' := v')
          (hb := hbounded) (hnonempty := hnonempty) (hnonzero := hnonzero)
          (hlen := hlen') (hlast := hlast) (hstorage := hstorage')
      have hret' : r = (embed self).getLast hnonempty := by
        have hlastEq := embed_getLast_eq_storage_get (v := self)
          (hb := hbounded) (hnonempty := hnonempty) (hnonzero := hnonzero) (hlast := hlast)
        simpa [hret, hlastEq]
      exact ⟨hwf', hembed', hret'⟩

theorem from_parts_unchecked_spec {p T MaxLen array l}
    (hb : l.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts_unchecked».call
        h![T, MaxLen] h![array, l])
      (fun r => wellFormed r ∧ embed r = List.take l.toNat array.toList) := by
  have hble : l ≤ MaxLen := by
    rw [BitVec.le_def]; simpa using hb
  enter_decl
  steps_named
  constructor
  ·
    exact wellFormed_of_bounded (by simpa [bounded, len] using hb)
  · simp [embed, active, storage, len]

theorem extend_from_array_spec {p T MaxLen Len selfRef self array}
    (hspace : (len self).toNat + Len.toNat ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_array».call
        h![T, MaxLen, Len] h![selfRef, array])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦wellFormed v' ∧ embed v' = embed self ++ array.toList⟧) := by
  have hMax_lt := u32_toNat_lt MaxLen
  have hLen_lt := u32_toNat_lt Len
  have hcastLenNat : ((↑(List.Vector.length array) : U 32)).toNat = Len.toNat :=
    congrArg BitVec.toNat (u32_cast_vector_length_array_eq array)
  have hsum_lt : (len self).toNat + ((↑(List.Vector.length array) : U 32)).toNat < 2 ^ 32 := by
    rw [hcastLenNat]; exact lt_of_le_of_lt hspace hMax_lt
  have hnew_le : len self + (↑(List.Vector.length array) : U 32) ≤ MaxLen := by
    rw [BitVec.le_def, BitVec.toNat_add_of_lt hsum_lt, hcastLenNat]
    exact hspace
  enter_decl
  steps
  loop_inv nat (fun i _ _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + i) (storage v).toList =
              embed self ++ array.toList.take i⟧)
  · sl; simp [Nat.add_zero, embed, active, storage]
  · simp
  · intro i hlo hhi
    steps_named as [v, hinv, h_add, h_cast, u2, h_dec, h_isSome]
    rcases hinv with ⟨hlenV, htakeV⟩
    have hhiLen : i < Len.toNat := by simpa [hcastLenNat] using hhi
    have hi32 : i < 2 ^ 32 := lt_of_lt_of_le hhiLen (Nat.le_of_lt hLen_lt)
    have hiMax : (len self).toNat + i < MaxLen.toNat :=
      lt_of_lt_of_le (Nat.add_lt_add_left hhiLen _) hspace
    extend_loop_step hlenV htakeV hi32 hiMax
      hMax_lt
      (by simpa [List.Vector.toList_length] using hhiLen)
  ·
    steps_named as [v, hinv, h_dec, h_isSome]
    rcases hinv with ⟨hlenV, htakeV⟩
    have htakeV' :
        List.take ((len self).toNat + array.toList.length) (storage v).toList =
          embed self ++ array.toList := by
      have : array.toList.take Len.toNat = array.toList := by
        simp [List.Vector.toList_length]
      simpa [hcastLenNat, List.Vector.toList_length, this]
        using htakeV
    exact extend_from_finalize hlenV htakeV'
      (by simpa [lenLens, len] using h_isSome)
      (by have := lt_of_le_of_lt hspace hMax_lt
          simpa [len, hcastLenNat, List.Vector.toList_length,
            BitVec.toNat_add_of_lt hsum_lt])
      ((BitVec.le_def).1 hnew_le)

theorem from_array_spec {p T MaxLen Len array}
    (hbounded : Len.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_array».call
        h![T, MaxLen, Len] h![array])
      (fun r => wellFormed r ∧ embed r = array.toList) := by
  enter_decl
  steps
  steps [new_spec]
  rename_i vecVal
  have hlen0 : len _ = 0 := vecVal.2.1
  have hembed0 : embed _ = ([] : List (T.denote p)) :=
    vecVal.2.2
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v',
        [vec ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦wellFormed v' ∧
            embed v' = array.toList⟧))
  ·
    have hspace' := hlen0 ▸ show
        (0 : U 32).toNat + Len.toNat ≤ MaxLen.toNat
          from by simpa using hbounded
    exact STHoare.consequence_post
      (extend_from_array_spec (hspace := hspace'))
      fun _ =>
        SLP.exists_star_lift_mono fun v' ⟨hwf, he⟩ =>
          ⟨hwf, by simpa [hembed0] using he⟩
  ·
    intro _
    steps_named as [r, hpost]
    exact hpost

theorem extend_from_slice_spec {p T MaxLen selfRef self slice}
    (hspace : (len self).toNat + slice.length ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_slice».call
        h![T, MaxLen] h![selfRef, slice])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦wellFormed v' ∧ embed v' = embed self ++ slice⟧) := by
  have hMax_lt := u32_toNat_lt MaxLen
  have hslen_lt : slice.length < 2 ^ 32 :=
    lt_of_le_of_lt (le_trans (Nat.le_add_left ..) hspace) hMax_lt
  have hcastLenNat : ((↑slice.length : U 32)).toNat = slice.length :=
    ofNat32_toNat hslen_lt
  have hsum_lt : (len self).toNat + ((↑slice.length : U 32)).toNat < 2 ^ 32 := by
    rw [hcastLenNat]; exact lt_of_le_of_lt hspace hMax_lt
  have hnew_le : len self + (↑slice.length : U 32) ≤ MaxLen := by
    rw [BitVec.le_def, BitVec.toNat_add_of_lt hsum_lt, hcastLenNat]
    exact hspace
  enter_decl
  steps
  loop_inv nat (fun i _ _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + i) (storage v).toList =
              embed self ++ slice.take i⟧)
  · sl; simp [Nat.add_zero, embed, active, storage]
  · simp
  · intro i hlo hhi
    steps_named as [v, hinv, h_add, h_cast, u2, h_dec, h_isSome]
    rcases hinv with ⟨hlenV, htakeV⟩
    have hi32 : i < 2 ^ 32 := lt_of_lt_of_le hhi (Nat.le_of_lt hslen_lt)
    have hiMax : (len self).toNat + i < MaxLen.toNat :=
      lt_of_lt_of_le (Nat.add_lt_add_left hhi _) hspace
    extend_loop_step hlenV htakeV hi32 hiMax hMax_lt hhi
  ·
    steps_named as [v, hinv, h_dec, h_isSome]
    rcases hinv with ⟨hlenV, htakeV⟩
    have htakeV' :
        List.take ((len self).toNat + slice.length) (storage v).toList =
          embed self ++ slice := by
      simpa [nat_mod_4294967296 hslen_lt] using htakeV
    exact extend_from_finalize hlenV htakeV'
      (by simpa [lenLens, len, bitvec_ofNatLT_eq_ofNat]
            using h_isSome)
      (by simpa [len, BitVec.toNat_add_of_lt hsum_lt])
      (by simpa [hcastLenNat] using (BitVec.le_def).1 hnew_le)

theorem extend_from_bounded_vec_spec {p T MaxLen Len selfRef self vec}
    (hwfVec : wellFormed (p := p) (T := T) (MaxLen := Len) vec)
    (hspace : (len self).toNat + (len vec).toNat ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_bounded_vec».call
        h![T, MaxLen, Len] h![selfRef, vec])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦wellFormed v' ∧ embed v' = embed self ++ embed vec⟧) := by
  have hbVec : bounded (p := p) (T := T) (MaxLen := Len) vec := bounded_of_wellFormed hwfVec
  have hMax_lt := u32_toNat_lt MaxLen
  have hsum_lt : (len self).toNat + (len vec).toNat < 2 ^ 32 := lt_of_le_of_lt hspace hMax_lt
  have hnew_le : len self + len vec ≤ MaxLen := by
    rw [BitVec.le_def,
      BitVec.toNat_add_of_lt (x := len self) (y := len vec) hsum_lt]
    exact hspace
  have hLen_lt := u32_toNat_lt Len
  have hlenVec : (embed vec).length = (len vec).toNat := hwfVec

  enter_decl
  steps_named [len_concrete_spec (p := p) (T := T) (MaxLen := Len) (self := vec)]
  all_goals (try (first | exact hnew_le | exact ()))

  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + (len vec).toNat) (storage v).toList =
              embed self ++ embed vec⟧))
  ·
    apply STHoare.ite_intro_of_false
    · simp
    ·
      steps
      loop_inv nat (fun i _ _ =>
          ∃∃ v : Repr p T MaxLen,
            [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
              [exceeded_len ↦ ⟨.bool, decide ((len vec).toNat < i)⟩] ⋆
                ⟦len v = len self ∧
                  List.take ((len self).toNat + Nat.min i (len vec).toNat) (storage v).toList =
                    embed self ++ (embed vec).take (Nat.min i (len vec).toNat)⟧)
      · sl; simp [embed, active]
      · simp
      · intro i hlo hhi
        steps_named
        all_goals (try (first | exact () | exact hnew_le))
        rename_i v0 hinv u_el h_isSome_el
        rcases u_el with ⟨hlenV, htakeV⟩
        have hi32 : i < 2 ^ 32 :=
          lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
        apply STHoare.ite_intro
        · intro hcond
          have hcond' := by simpa using hcond
          rcases hcond' with ⟨hi_le, hi_ne_bv⟩
          have hltVec : i < (len vec).toNat :=
            exceeded_len_lt_of_cond_true hi32 hi_le (by
              simp_all [BitVec.ofNatLT_eq_ofNat])
          have hmin_i := Nat.min_eq_left (Nat.le_of_lt hltVec)
          have hmin_succ := Nat.min_eq_left
            (Nat.succ_le_of_lt hltVec)
          have hiMax : (len self).toNat + i < MaxLen.toNat :=
            lt_of_lt_of_le
              (Nat.add_lt_add_left hltVec _) hspace

          steps [get_unchecked_spec (p := p) (T := T)
            (MaxLen := Len) (self := vec)
            (index := BitVec.ofNatLT i
              (lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi))
            (hindex := by
              simpa [nat_mod_4294967296 hi32] using hhi)]
          subst_vars
          case h₁.heq =>
            simp [decide_lt_succ_eq_bv (x := len vec) hi32]
          case h₁.a =>
            rename_i hidx elemEq _h_isSome_set _u_post
            simp [hmin_i, hmin_succ] at htakeV ⊢
            have hiEmb : i < (embed vec).length :=
              hlenVec ▸ hltVec
            have helem := elemEq (by
              simpa [nat_mod_4294967296 hi32] using hiEmb)
            generalize_proofs at helem
            have helem' := by
              simpa [nat_mod_4294967296 hi32] using helem
            have htoNat_idx :
                i_3643.toNat = (len self).toNat + i := by
              have : i_3643 = len hinv + BitVec.ofNat 32 i := by
                simpa [len, bitvec_ofNatLT_eq_ofNat (i := i)
                  (nat_lt_4294967296 hi32)] using hidx
              simpa [this] using extend_loop_idx_toNat
                hlenV hi32 (lt_trans hiMax hMax_lt)
            constructor
            · simpa [len] using hlenV
            · simp (config := {contextual := false})
                [storage, List.Vector.toList_set, htoNat_idx, helem',
                  List.get_eq_getElem, nat_mod_4294967296 hi32]
              have := List.take_set_extends
                (by simpa [storage] using htakeV)
                (by simpa [List.Vector.toList_length] using hiMax)
                hiEmb
              simpa [Nat.add_comm, Nat.add_assoc] using this
        · intro hcond
          steps_named
          case h₁.heq =>
            simp [decide_lt_succ_eq_bv (x := len vec) hi32]
          case h₁.a =>
            have hge : (len vec).toNat ≤ i := by
              have hflag_raw :
                  (len vec).toNat < i ∨ BitVec.ofNatLT i hi32 = append_len := by
                simpa using (by simpa using congrArg Bool.not hcond)
              rcases hflag_raw with hlt | hbv
              · exact Nat.le_of_lt hlt
              · exact (by
                  have := congrArg BitVec.toNat hbv
                  simpa [BitVec.toNat_ofNatLT,
                    Nat.mod_eq_of_lt (nat_lt_4294967296 hi32),
                    *] using this : i = (len vec).toNat).symm.le
            have hmin_i := Nat.min_eq_right (a := i) hge
            have hmin_succ := Nat.min_eq_right (a := i + 1)
              (Nat.le_trans hge (Nat.le_succ i))
            constructor
            · simpa [len] using hlenV
            · simp [hmin_i, hmin_succ] at htakeV ⊢
              simpa using htakeV
      · steps_named as [v, hinv, _u, _hsl, _hdec]
        rcases hinv with ⟨hlenV, htakeV⟩
        constructor
        · simpa [len] using hlenV
        · have htake_full : List.take (len vec).toNat (embed vec) = embed vec := by
            simp [hlenVec]
          simpa [Nat.min_eq_right hbVec, htake_full] using htakeV
  ·
    intro _
    steps_named as [h_pre, _u, _hsl, _hdec, h_isSome]
    rcases _u with ⟨hlenV, htakeV⟩
    have htakeV' : List.take ((len self).toNat + (embed vec).length) (storage h_pre).toList =
        embed self ++ embed vec := by
      simpa [hlenVec, Nat.min_eq_right hbVec] using htakeV
    exact extend_from_finalize hlenV htakeV'
      (by simpa [lenLens, len] using h_isSome)
      (by simpa [len, hlenVec, BitVec.toNat_add_of_lt hsum_lt])
      ((BitVec.le_def).1 hnew_le)

theorem from_parts_spec {p T MaxLen arr l}
    (hb : l.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts».call
        h![T, MaxLen] h![arr, l])
      (fun r => wellFormed r ∧ embed r = List.take l.toNat arr.toList) := by
  have hble : l ≤ MaxLen := by
    rw [BitVec.le_def]; simpa using hb
  enter_decl
  steps
  all_goals (try exact ())
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ a : List.Vector (T.denote p) MaxLen.toNat,
        [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
          ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList⟧))
  ·
    apply STHoare.ite_intro_of_false
    · simp
    ·
      steps
      loop_inv nat (fun _ _ _ =>
          ∃∃ a : List.Vector (T.denote p) MaxLen.toNat,
            [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
              ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList⟧)
      · sl; simp
      · simp
      · intro i hlo hhi
        apply (STHoare.letIn_intro
          (Q := fun b =>
            ∃∃ a : List.Vector (T.denote p) MaxLen.toNat,
              [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
                ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList ∧
                  b = decide (l.toNat ≤ i)⟧))
        · apply Lampe.Steps.pull_exi
          intro a
          apply (STHoare.consequence
            (H₁ := [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
              ⟦List.take l.toNat a.toList =
                List.take l.toNat arr.toList⟧)
            (Q₁ := fun b =>
              [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
                ⟦List.take l.toNat a.toList =
                  List.take l.toNat arr.toList ∧
                  b = decide (l.toNat ≤ i)⟧))
          · exact SLP.entails_self
          · intro b; sl; assumption
          · steps [STHoare.genericTotalPureBuiltin_intro
              (b := Builtin.uGeq) (h := rfl)]
            simp_all only [Builtin.instCastTpU,
              BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
              BitVec.toNat_ofNatLT, BitVec.le_def, ge_iff_le]
            simp
        · intro b
          apply STHoare.ite_intro
          · intro hbTrue
            steps
            generalize_proofs
            rename_i a hpre h_isSome u pf
            rcases hpre with ⟨htake, hbdec⟩
            have hli : l.toNat ≤ i :=
              (decide_eq_true_iff).1 (hbdec ▸ hbTrue)
            simp_all only [BitVec.toNat_ofNatLT, Lens.modify, Access.modify]
            simp
            have hdrop :
                List.take l.toNat (a.toList.set i (Tp.zero p T)) =
                  List.take l.toNat a.toList := by
              rw [List.take_set]
              exact List.set_eq_of_length_le (by
                simp [Nat.min_eq_left hb]; exact hli)
            simpa [hdrop] using htake
          · intro hbFalse
            steps
            generalize_proofs
            rename_i a hpre u
            exact hpre.1
      · steps; assumption
  · intro _
    steps_named as [a, hinv]
    exact ⟨wellFormed_of_bounded (by simpa [bounded, len] using hb),
      by simpa using hinv⟩

end Lampe.Stdlib.Collections.BoundedVec
