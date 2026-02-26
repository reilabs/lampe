import Stdlib.Collections.BoundedVec.Core

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
  refine STHoare.consequence
      (H₁ := (⟦⟧ : SLP (State p)))
      (H₂ := (⟦⟧ : SLP (State p)))
      (Q₁ := fun r => (r = (storage self)[index.toNat]'hindex))
      (Q₂ := fun r => (∀ hlt : index.toNat < (embed self).length, r = (embed self)[index.toNat]'hlt))
      SLP.entails_self ?_ (get_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
        (self := self) (index := index) (hindex := hindex))
  intro r
  have h_lift :
      ((r = (storage self)[index.toNat]'hindex) : SLP (State p)) ⊢
        ((∀ hlt : index.toNat < (embed self).length, r = (embed self)[index.toNat]'hlt) : SLP (State p)) := by
    intro st hst
    rcases hst with ⟨hr, hst⟩
    refine ⟨?_, hst⟩
    intro hlt
    have hr_list : r = (storage self).toList[index.toNat]'hstorage := by
      simpa [List.Vector.getElem_def] using hr
    have hx_rhs :
        (embed self)[index.toNat]'hlt = (storage self).toList[index.toNat]'hstorage := by
      simpa using
        (embed_getElem_toList (self := self) (i := index.toNat) (hxs := hlt) (hstorage := hstorage))
    exact hr_list.trans hx_rhs.symm
  exact SLP.star_mono_r h_lift

theorem get_spec {p T MaxLen self index}
    (hbounded : bounded self)
    (hindex : index.toNat < (embed self).length) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (embed self)[index.toNat]'hindex) := by
  have hlen : (embed self).length = (len self).toNat := embed_length_eq_len_toNat (v := self) hbounded
  have hindex_len : index.toNat < (len self).toNat := by
    simpa [hlen] using hindex
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex_len hbounded
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
        (hbounded := hbounded) (hindex := hindex_len))

  -- Post-compose the concrete storage equality into the semantic `embed` equality.
  refine STHoare.consequence
      (H₁ := (⟦⟧ : SLP (State p)))
      (H₂ := (⟦⟧ : SLP (State p)))
      (Q₁ := fun r => (r = (storage self)[index.toNat]'hindex_max))
      (Q₂ := fun r => (r = (embed self)[index.toNat]'hindex))
      SLP.entails_self ?_ hprec
  intro r
  have h_lift :
      ((r = (storage self)[index.toNat]'hindex_max) : SLP (State p))
        ⊢ ((r = (embed self)[index.toNat]'hindex) : SLP (State p)) := by
    intro st hst
    rcases hst with ⟨hr, hst⟩
    refine ⟨?_, hst⟩
    have hr_list : r = (storage self).toList[index.toNat]'hstorage := by
      simpa [List.Vector.getElem_def] using hr
    exact hr_list.trans hx_rhs.symm
  exact SLP.star_mono_r h_lift

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
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun _ =>
        ([selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩] : SLP (State p)))
      (Q₂ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex⟩ value⟧ : SLP (State p)))
      SLP.entails_self ?_ hstate
  intro _
  have hpt :
      ([selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩] : SLP (State p))
        ⊢ (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex⟩ value⟧ : SLP (State p)) := by
    intro st hst
    have hlen : len vUpd = len self := by cases self; rfl
    have hstorage : storage vUpd = (storage self).set ⟨index.toNat, hindex⟩ value := by
      unfold vUpd storage
      cases self
      rfl
    refine ⟨vUpd, st, (∅ : State p), by simp, by simp, ?_, ?_⟩
    · simpa [vUpd] using hst
    · exact ⟨And.intro hlen hstorage, rfl⟩
  exact SLP.star_mono_r hpt

theorem set_unchecked_spec {p T MaxLen selfRef self index value}
    (hb : bounded self)
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set_unchecked».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧) := by
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex⟩ value⟧ : SLP (State p)))
      (Q₂ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧ : SLP (State p)))
      SLP.entails_self ?_ (set_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
        (selfRef := selfRef) (self := self) (index := index) (value := value) (hindex := hindex))
  intro _
  have hpt :
      (∃∃ v',
        [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex⟩ value⟧ : SLP (State p))
        ⊢ (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧ : SLP (State p)) := by
    intro st hst
    unfold SLP.exists' at hst
    rcases hst with ⟨v', hst⟩
    unfold SLP.star at hst
    rcases hst with ⟨st₁, st₂, hdisj, hunion, hpt, hpure⟩
    unfold SLP.lift at hpure
    rcases hpure with ⟨hpure, hempty⟩
    rcases hpure with ⟨hlen', hstorage'⟩
    have hb' : bounded v' := by
      simpa [bounded, hlen'] using hb
    have hembed' : embed v' = (embed self).set index.toNat value := by
      exact embed_eq_set_of_storage_set (v := self) (v' := v')
        (i := index.toNat) (hi := hindex) (a := value) (hlen := hlen') (hstorage := hstorage')
    refine ⟨v', st₁, st₂, hdisj, hunion, hpt, ?_⟩
    exact ⟨And.intro hb' hembed', hempty⟩
  exact SLP.star_mono_r hpt

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
  steps [set_unchecked_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
    (selfRef := selfRef) (self := self) (index := index) (value := value) (hindex := hindex_max)]
  subst_vars
  rename_i v hproj
  rcases hproj with ⟨hlen', hstorage'⟩
  refine And.intro hlen' ?_
  -- `steps` produced the storage update with proof `hindex_max`; rewrite to the desired proof.
  have hstorageProof :
      (storage self).set ⟨index.toNat, hindex_max⟩ value =
        (storage self).set ⟨index.toNat, lt_of_lt_of_le hindex hbounded⟩ value := by
    simpa using
      (vector_set_proof_irrel (v := storage self) (i := index.toNat)
        (h1 := hindex_max) (h2 := lt_of_lt_of_le hindex hbounded) (x := value))
  exact hstorage'.trans hstorageProof

theorem set_spec {p T MaxLen selfRef self index value}
    (hbounded : bounded self)
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::set».call h![T, MaxLen]
        h![selfRef, index, value])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧) := by
  have hlen : (embed self).length = (len self).toNat := embed_length_eq_len_toNat (v := self) hbounded
  have hindex_len : index.toNat < (len self).toNat := by
    simpa [hlen] using hindex
  have hindex_max : index.toNat < MaxLen.toNat := lt_of_lt_of_le hindex_len hbounded
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex_max⟩ value⟧ : SLP (State p)))
      (Q₂ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧ : SLP (State p)))
      SLP.entails_self ?_
      (set_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
        (selfRef := selfRef) (self := self) (index := index) (value := value)
        (hbounded := hbounded) (hindex := hindex_len))
  intro _
  have hpt :
      (∃∃ v',
        [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦len v' = len self ∧ storage v' = (storage self).set ⟨index.toNat, hindex_max⟩ value⟧ : SLP (State p))
        ⊢ (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).set index.toNat value⟧ : SLP (State p)) := by
    intro st hst
    unfold SLP.exists' at hst
    rcases hst with ⟨v', hst⟩
    unfold SLP.star at hst
    rcases hst with ⟨st₁, st₂, hdisj, hunion, hpt, hpure⟩
    unfold SLP.lift at hpure
    rcases hpure with ⟨hpure, hempty⟩
    rcases hpure with ⟨hlen', hstorage'⟩
    have hb' : bounded v' := by
      simpa [bounded, hlen'] using hbounded
    have hembed' : embed v' = (embed self).set index.toNat value := by
      exact embed_eq_set_of_storage_set (v := self) (v' := v')
        (i := index.toNat) (hi := hindex_max) (a := value) (hlen := hlen') (hstorage := hstorage')
    refine ⟨v', st₁, st₂, hdisj, hunion, hpt, ?_⟩
    exact ⟨And.intro hb' hembed', hempty⟩
  exact SLP.star_mono_r hpt

private theorem modify_head_array_some {p T MaxLen} {v : Tp.denote p (bvTp T MaxLen)} {idx : U 32}
    {value : Tp.denote p T} (hidx : idx.toNat < MaxLen.toNat) :
    (((Lens.nil.cons (Access.tuple Builtin.Member.head)).cons (Access.array idx)).modify v value) =
      some (Builtin.replaceTuple' v Builtin.Member.head ((storage v).set ⟨idx.toNat, hidx⟩ value)) := by
  simp [Lens.modify, Lens.get, Access.get, Access.modify, storage, hidx, bvTp]

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
      steps
      subst_vars
      simp [bvTp, vStor, modify_head_array_some (v := self) (idx := len self) (value := elem) hpush,
        storage, len, vector_set_proof_irrel]
    ·
      intro _
      steps
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun _ =>
        ([selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩] : SLP (State p)))
      (Q₂ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self + 1 ∧ storage v' = (storage self).set ⟨(len self).toNat, hpush⟩ elem⟧ : SLP (State p)))
      SLP.entails_self ?_ hstate
  intro _
  have hpt :
      ([selfRef ↦ ⟨bvTp T MaxLen, vUpd⟩] : SLP (State p))
        ⊢ (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self + 1 ∧ storage v' = (storage self).set ⟨(len self).toNat, hpush⟩ elem⟧ : SLP (State p)) := by
    intro st hst
    have hlen : len vUpd = len self + 1 := by
      unfold vUpd len
      simp [Builtin.index_replaced_tpl]
    have hstorage : storage vUpd = (storage self).set ⟨(len self).toNat, hpush⟩ elem := by
      unfold vUpd vStor storage
      cases self <;> rfl
    refine ⟨vUpd, st, (∅ : State p), by simp, by simp, ?_, ?_⟩
    · simpa [vUpd] using hst
    · exact ⟨And.intro hlen hstorage, rfl⟩
  exact SLP.star_mono_r hpt

theorem push_spec {p T MaxLen selfRef self elem}
    (hbounded : bounded self)
    (hspace : (embed self).length < MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::push».call h![T, MaxLen]
        h![selfRef, elem])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = embed self ++ [elem]⟧) := by
  have hlen : (embed self).length = (len self).toNat := embed_length_eq_len_toNat (v := self) hbounded
  have hpush : (len self).toNat < MaxLen.toNat := by
    simpa [hlen] using hspace
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self + 1 ∧ storage v' = (storage self).set ⟨(len self).toNat, hpush⟩ elem⟧ : SLP (State p)))
      (Q₂ := fun _ =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = embed self ++ [elem]⟧ : SLP (State p)))
      SLP.entails_self ?_
      (push_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
        (selfRef := selfRef) (self := self) (elem := elem) (hpush := hpush))
  intro _
  have hpt :
      (∃∃ v',
        [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦len v' = len self + 1 ∧ storage v' = (storage self).set ⟨(len self).toNat, hpush⟩ elem⟧ : SLP (State p))
        ⊢ (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = embed self ++ [elem]⟧ : SLP (State p)) := by
    intro st hst
    unfold SLP.exists' at hst
    rcases hst with ⟨v', hst⟩
    unfold SLP.star at hst
    rcases hst with ⟨st₁, st₂, hdisj, hunion, hpt, hpure⟩
    unfold SLP.lift at hpure
    rcases hpure with ⟨hpure, hempty⟩
    rcases hpure with ⟨hlen', hstorage'⟩
    have hb' : bounded v' := by
      have hmax : MaxLen.toNat < 2 ^ 32 := by
        simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
      have hx32 : (len self).toNat + 1 < 2 ^ 32 := by
        exact lt_of_le_of_lt (Nat.succ_le_of_lt hpush) hmax
      have htoNat_v' : (len v').toNat = (len self).toNat + 1 := by
        simpa [hlen', BitVec.toNat_add_one_of_lt (x := len self) hx32]
      have : (len v').toNat ≤ MaxLen.toNat := by
        have : (len self).toNat + 1 ≤ MaxLen.toNat := Nat.succ_le_of_lt hpush
        simpa [htoNat_v'] using this
      simpa [bounded] using this
    have hembed' : embed v' = embed self ++ [elem] := by
      exact embed_eq_append_of_storage_set_at_len (v := self) (v' := v') (a := elem)
        (hb := hbounded) (hpush := hpush) (hlen := hlen') (hstorage := hstorage')
    refine ⟨v', st₁, st₂, hdisj, hunion, hpt, ?_⟩
    exact ⟨And.intro hb' hembed', hempty⟩
  exact SLP.star_mono_r hpt

private theorem len_concrete_spec {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r = len self) := by
  enter_decl
  steps
  simpa [len]

theorem len_spec {p T MaxLen self}
    (hbounded : bounded self) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r.toNat = (embed self).length) := by
  have hlen : (embed self).length = (len self).toNat :=
    embed_length_eq_len_toNat (v := self) hbounded
  refine STHoare.consequence
      (H₁ := (⟦⟧ : SLP (State p)))
      (H₂ := (⟦⟧ : SLP (State p)))
      (Q₁ := fun r => (r = len self))
      (Q₂ := fun r => (r.toNat = (embed self).length))
      SLP.entails_self ?_ (len_concrete_spec (p := p) (T := T) (MaxLen := MaxLen) (self := self))
  intro r
  have h_lift :
      ((r = len self) : SLP (State p)) ⊢ ((r.toNat = (embed self).length) : SLP (State p)) := by
    intro st hst
    rcases hst with ⟨hr, hst⟩
    refine ⟨?_, hst⟩
    have hrt : r.toNat = (len self).toNat := by
      simpa using congrArg BitVec.toNat hr
    exact hrt.trans hlen.symm
  exact SLP.star_mono_r h_lift

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
      (fun r => bounded r ∧ len r = 0 ∧ embed r = []) := by
  enter_decl
  steps
  subst_vars
  refine And.intro ?_ (And.intro ?_ ?_)
  · simp [bounded, len]
  · rfl
  · simp [embed, active, len, storage]

private lemma pop_preconditions {p T MaxLen} {self : Repr p T MaxLen}
    (hbounded : bounded self) (hnonempty : embed self ≠ []) :
    ((0 : U 32) < len self) ∧ ((len self - (1 : U 32)).toNat < MaxLen.toNat) := by
  have hlen : (embed self).length = (len self).toNat :=
    embed_length_eq_len_toNat (v := self) hbounded
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

@[simp] private lemma indexTpl_replaceTuple'_head_tail
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp) :
    Builtin.indexTpl (Builtin.replaceTuple' tpl Builtin.Member.head v) Builtin.Member.head.tail =
      Builtin.indexTpl tpl Builtin.Member.head.tail := by
  rfl

@[simp] private lemma indexTpl_replaceTuple'_headTail_head
    {p} {tp tp' : Tp} {tps : List Tp}
    (tpl : Tp.denoteArgs p (tp :: tp' :: tps)) (v : Tp.denote p tp') :
    Builtin.indexTpl (Builtin.replaceTuple' tpl Builtin.Member.head.tail v) Builtin.Member.head =
      Builtin.indexTpl tpl Builtin.Member.head := by
  rfl

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

@[simp] private lemma toNat_sub_one_u32 (x : U 32) :
    BitVec.toNat (x - (1 : U 32)) = (4294967295 + BitVec.toNat x) % 4294967296 := by
  rfl

@[simp] private lemma coe_one_u32 :
    ((↑(1 : Nat) : U 32) = (1#32)) := by
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
  -- split on the final `let` corresponding to the `Unit`-returning block that zeroes the tail slot
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      (∃∃ v',
        [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦len v' = len self - (1 : U 32) ∧
            storage v' =
              (storage self).set ⟨(len self - (1 : U 32)).toNat, hlast⟩ (Tp.zero p T)⟧ : SLP (State p))))
  ·
    steps
    subst_vars
    -- At this point `steps` has reduced the heap update to pure projection equalities.
    cases self
    simp [
      Repr, len, storage,
      Builtin.indexTpl, Builtin.replaceTuple',
      vector_set_proof_irrel, BitVec.ofNat_eq_ofNat
    ]
    exact coe_one_u32'
  ·
    intro r
    steps
    subst_vars
    -- Add the return-value equation.
    rename_i v hproj
    have ha :
        len v = len self - (1 : U 32) ∧
          storage v =
            (storage self).set ⟨BitVec.toNat (len self - (1 : U 32)), hlast⟩ (Tp.zero p T) := by
      simpa using (by
        -- `steps` leaves exactly this conjunction as a hypothesis (with an unreadable generated name).
        assumption :
          len v = len self - (1 : U 32) ∧
            storage v =
              (storage self).set ⟨BitVec.toNat (len self - (1 : U 32)), hlast⟩ (Tp.zero p T))
    rcases ha with ⟨hlen', hstorage'⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [len, Builtin.indexTpl, BitVec.ofNat_eq_ofNat] using hlen'
    · simpa [storage, len, Builtin.indexTpl, vector_set_proof_irrel, BitVec.ofNat_eq_ofNat] using hstorage'
    ·
      simp [storage, len, Builtin.indexTpl, Builtin.replaceTuple', BitVec.ofNat_eq_ofNat]
      set i : Nat := (4294967295 + BitVec.toNat self.2.1) % 4294967296
      -- normalize both sides to `List.Vector.get` at the same `Nat` index, then drop proof differences
      change List.Vector.get self.1 ⟨i, ?_⟩ = List.Vector.get self.1 ⟨i, ?_⟩
      exact vector_get_proof_irrel (v := self.1) (i := i) _ _

theorem pop_spec {p T MaxLen selfRef self}
    (hbounded : bounded self)
    (hnonempty : embed self ≠ []) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::pop».call h![T, MaxLen]
        h![selfRef])
      (fun r =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).dropLast ∧ r = (embed self).getLast hnonempty⟧) := by
  obtain ⟨hnonzero, hlast⟩ := pop_preconditions (self := self) hbounded hnonempty
  -- Run the concrete spec, then reinterpret in terms of `embed`.
  refine STHoare.consequence
      (H₁ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (H₂ := ([selfRef ↦ ⟨bvTp T MaxLen, self⟩] : SLP (State p)))
      (Q₁ := fun r =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦len v' = len self - (1 : U 32) ∧
              storage v' =
                (storage self).set ⟨(len self - (1 : U 32)).toNat, hlast⟩ (Tp.zero p T) ∧
              r = (storage self)[(len self - (1 : U 32)).toNat]'hlast⟧ : SLP (State p)))
      (Q₂ := fun r =>
        (∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = (embed self).dropLast ∧ r = (embed self).getLast hnonempty⟧ : SLP (State p)))
      SLP.entails_self ?_
      (pop_concrete_spec (p := p) (T := T) (MaxLen := MaxLen)
        (selfRef := selfRef) (self := self) (hnonzero := hnonzero) (hlast := hlast))
  intro r st hst
  -- `STHoare.consequence` asks us to prove `Q₁ r ⋆ ⊤ ⊢ Q₂ r ⋆ ⊤`.
  unfold SLP.star at hst
  rcases hst with ⟨stQ1, stTop, hdisj, hunion, hQ1, hTop⟩
  unfold SLP.exists' at hQ1
  rcases hQ1 with ⟨v', hQ1⟩
  rcases hQ1 with ⟨stPt, stPure, hdisj', hunion', hpt, hpure⟩
  unfold SLP.lift at hpure
  rcases hpure with ⟨hpure, hempty⟩
  rcases hpure with ⟨hlen', hstorage', hret⟩
  have hb' : bounded v' := by
    have : (len v').toNat ≤ MaxLen.toNat := by
      have : (len self - (1 : U 32)).toNat ≤ MaxLen.toNat := Nat.le_of_lt hlast
      simpa [hlen'] using this
    simpa [bounded] using this
  have hembed' : embed v' = (embed self).dropLast := by
    exact embed_eq_dropLast_of_pop_update (v := self) (v' := v')
      (hb := hbounded) (hnonempty := hnonempty) (hnonzero := hnonzero)
      (hlen := hlen') (hlast := hlast) (hstorage := hstorage')
  have hret' : r = (embed self).getLast hnonempty := by
    have hlastEq := embed_getLast_eq_storage_get (v := self)
      (hb := hbounded) (hnonempty := hnonempty) (hnonzero := hnonzero) (hlast := hlast)
    -- `hret` gives `r = storage[...]`; rewrite through `hlastEq`.
    simpa [hret, hlastEq]
  -- Rebuild the goal `Q₂ r ⋆ ⊤` on the same split heap.
  unfold SLP.star
  refine ⟨stQ1, stTop, hdisj, hunion, ?_, hTop⟩
  unfold SLP.exists'
  refine ⟨v', ?_⟩
  refine ⟨stPt, stPure, hdisj', hunion', hpt, ?_⟩
  exact ⟨And.intro hb' (And.intro hembed' hret'), hempty⟩

theorem from_parts_unchecked_spec {p T MaxLen array l}
    (hb : l.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts_unchecked».call
        h![T, MaxLen] h![array, l])
      (fun r => bounded r ∧ embed r = List.take l.toNat array.toList) := by
  have hble : l ≤ MaxLen := by
    -- `≤` on `U 32` is by `toNat`.
    rw [BitVec.le_def]
    simpa using hb
  enter_decl
  steps
  subst_vars
  constructor
  · simpa [bounded, len] using hb
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
            ⟦bounded v' ∧ embed v' = embed self ++ array.toList⟧) := by
  have hb_self : bounded self := by
    -- `len(self) ≤ len(self) + Len ≤ MaxLen`
    have : (len self).toNat ≤ (len self).toNat + Len.toNat := by
      simpa using (Nat.le_add_right (len self).toNat Len.toNat)
    exact le_trans this hspace
  have hMax_lt : MaxLen.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  have hLen_lt : Len.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := Len) (by rfl))
  have hcastLenNat : ((↑(List.Vector.length array) : U 32)).toNat = Len.toNat := by
    have : List.Vector.length array = Len.toNat := by rfl
    simp [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLen_lt]
  have hsum_lt : (len self).toNat + ((↑(List.Vector.length array) : U 32)).toNat < 2 ^ 32 := by
    -- `len(self) + Len ≤ MaxLen < 2^32`
    have : (len self).toNat + Len.toNat < 2 ^ 32 := lt_of_le_of_lt hspace hMax_lt
    simpa [hcastLenNat] using this
  have hnew_le : len self + (↑(List.Vector.length array) : U 32) ≤ MaxLen := by
    rw [BitVec.le_def]
    -- Avoid `simp` rewriting `toNat` of addition to a modular expression too early.
    rw [BitVec.toNat_add_of_lt (x := len self) (y := (↑(List.Vector.length array) : U 32)) hsum_lt]
    -- `≤` on `U 32` is by `toNat`.
    simpa [hcastLenNat] using hspace
  enter_decl
  steps

  -- Loop writes `array[i]` into `storage[len + i]` for `i < Len`, leaving `len` unchanged.
  loop_inv nat (fun i _ _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + i) (storage v).toList =
              embed self ++ array.toList.take i⟧)
  · sl
    simp [Nat.add_zero, embed, active, storage]
  ·
    simp
  · intro i hlo hhi
    steps
    subst_vars
    -- Rename the tail of the context to get the loop witness and its invariant.
    rename_i h_isSome
    rename_i h_dec
    rename_i u2
    rename_i h_cast
    rename_i h_add
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hhiLen : i < Len.toNat := by
      simpa [hcastLenNat] using hhi
    have hi32 : i < 2 ^ 32 := by
      exact lt_of_lt_of_le hhiLen (Nat.le_of_lt hLen_lt)
    have hiArr : i < array.toList.length := by
      simpa [List.Vector.toList_length] using hhiLen
    have hiMax : (len self).toNat + i < MaxLen.toNat := by
      have : (len self).toNat + i < (len self).toNat + Len.toNat :=
        Nat.add_lt_add_left hhiLen (len self).toNat
      exact lt_of_lt_of_le this hspace
    have hiStor : (len self).toNat + i < (storage v).toList.length := by
      simpa [storage, List.Vector.toList_length] using hiMax
    constructor
    ·
      -- `len` does not change when we only update `storage`.
      simpa [len] using hlenV
    ·
      -- Show the updated prefix matches `embed self ++ array.toList.take (i+1)`.
      have hlenVNat : (len v).toNat = (len self).toNat := by
        simpa using congrArg BitVec.toNat hlenV
      have hi32' : i < 4294967296 := by
        simpa using hi32
      have htoNat_i : (BitVec.ofNat 32 i).toNat = i := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32']
      have hsum_lt' : (len v).toNat + (BitVec.ofNat 32 i).toNat < 2 ^ 32 := by
        have : (len self).toNat + i < 2 ^ 32 := by
          have : (len self).toNat + i < (len self).toNat + Len.toNat :=
            Nat.add_lt_add_left hhiLen (len self).toNat
          exact lt_of_lt_of_le (lt_of_lt_of_le this hspace) (Nat.le_of_lt hMax_lt)
        simpa [hlenVNat, htoNat_i] using this
      have htoNat_idx :
          (len v + BitVec.ofNat 32 i).toNat = (len self).toNat + i := by
        have htoNat_add :=
          BitVec.toNat_add_of_lt (x := len v) (y := BitVec.ofNat 32 i) hsum_lt'
        simpa [hlenVNat, htoNat_i] using htoNat_add
      have htoNat_idx' :
          (Builtin.indexTpl v Builtin.Member.head.tail + BitVec.ofNat 32 i).toNat =
            (len self).toNat + i := by
        simpa [len] using htoNat_idx

      -- Normalize the tuple update performed by the loop body down to a `List.set` on `storage.toList`.
      simp (config := {contextual := false})
        [storage, len, List.Vector.toList_set, htoNat_idx', List.Vector.get_eq_get_toList,
          List.get_eq_getElem]

      -- Reduce the modular index to the plain `Nat` index `(len self).toNat + i`.
      have hlenVNat' : BitVec.toNat v.2.1 = (len self).toNat := by
        simpa [len] using hlenVNat
      have hsum_lt'' : BitVec.toNat v.2.1 + i < 4294967296 := by
        have : (len self).toNat + i < 2 ^ 32 := by
          have : (len self).toNat + i < (len self).toNat + Len.toNat :=
            Nat.add_lt_add_left hhiLen (len self).toNat
          exact lt_of_lt_of_le (lt_of_lt_of_le this hspace) (Nat.le_of_lt hMax_lt)
        simpa [hlenVNat'] using this
      have hmod :
          ((BitVec.toNat v.2.1 + i) % 4294967296) = (len self).toNat + i := by
        have hmod' : (BitVec.toNat v.2.1 + i) % 4294967296 = BitVec.toNat v.2.1 + i :=
          Nat.mod_eq_of_lt hsum_lt''
        simpa [hlenVNat'] using hmod'
      try simp [hmod]

      have hiStor_toList : (len self).toNat + i < (List.Vector.toList v.1).length := by
        simpa [List.Vector.toList_length] using hiMax
      have htakeV_toList :
          List.take ((len self).toNat + i) (List.Vector.toList v.1) =
            embed self ++ List.take i (List.Vector.toList array) := by
        simpa [storage] using htakeV
      have hiArr_toList : i < (List.Vector.toList array).length := by
        simpa [List.Vector.toList_length] using hiArr

      -- Extraction computes `toNat (ofNat 32 i)` as `i % 2^32`; under `i < 2^32` this is just `i`.
      have hmod_i : i % 4294967296 = i := Nat.mod_eq_of_lt hi32'
      simp [hmod_i]

      -- Use `take_succ` lemmas plus the loop IH.
      calc
        List.take ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + (i + 1))
            ((List.Vector.toList v.1).set ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + i)
              ((List.Vector.toList array)[i]'hiArr_toList)) =
          List.take ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + i) (List.Vector.toList v.1) ++
            [((List.Vector.toList array)[i]'hiArr_toList)] := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (List.take_succ_set_eq_take_append
              (l := (List.Vector.toList v.1))
              (n := (Builtin.indexTpl self Builtin.Member.head.tail).toNat + i)
              (a := ((List.Vector.toList array)[i]'hiArr_toList))
              (hn := by simpa [len] using hiStor_toList))
        _ =
          (embed self ++ List.take i (List.Vector.toList array)) ++
            [((List.Vector.toList array)[i]'hiArr_toList)] := by
          simpa [len] using
            congrArg (fun t => t ++ [((List.Vector.toList array)[i]'hiArr_toList)]) htakeV_toList
        _ =
          embed self ++ (List.take i (List.Vector.toList array) ++
            [((List.Vector.toList array)[i]'hiArr_toList)]) := by
          simp [List.append_assoc]
        _ =
          embed self ++ List.take (i + 1) (List.Vector.toList array) := by
          -- turn `take i ++ [get i]` into `take (i+1)`
          simpa using
            (List.take_succ_eq_take_append_get
              (l := (List.Vector.toList array)) (n := i) (hn := hiArr_toList))
  ·
    -- After the loop, `len` is set to `new_len = len + Len`.
    steps
    subst_vars
    rename_i h_isSome
    rename_i h_dec
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hsum_lt_final : (len self).toNat + Len.toNat < 4294967296 := by
      have : (len self).toNat + Len.toNat < 2 ^ 32 := lt_of_le_of_lt hspace hMax_lt
      simpa using this
    have hmod :
        (((len self).toNat + Len.toNat) % 4294967296) = (len self).toNat + Len.toNat := by
      exact Nat.mod_eq_of_lt hsum_lt_final
    have hmod_simp :
        ((BitVec.toNat self.2.1 + BitVec.toNat Len) % 4294967296) =
          BitVec.toNat self.2.1 + BitVec.toNat Len := by
      -- `simp [len]` turns `(len self).toNat` into `BitVec.toNat self.2.1`.
      simpa [len] using hmod

    constructor
    ·
      -- boundedness reduces to `len + Len ≤ MaxLen`.
      simpa [bounded, len, hmod_simp, hcastLenNat] using hspace
    ·
      have htakeArr : array.toList.take Len.toNat = array.toList := by
        simp [List.Vector.toList_length]
      have htakeV' :
          List.take ((len self).toNat + Len.toNat) (List.Vector.toList v.1) =
            embed self ++ List.take Len.toNat (List.Vector.toList array) := by
        simpa [storage, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htakeV
      -- `embed` is `take len storage`; `storage` is unchanged by the final `len` update.
      simpa [embed, active, storage, len, hmod_simp, htakeArr] using htakeV'

private theorem extend_from_array_from_empty_spec {p T MaxLen Len selfRef self array}
    (hlen0 : len self = 0)
    (hspace : Len.toNat ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_array».call
        h![T, MaxLen, Len] h![selfRef, array])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = array.toList⟧) := by
  have hnew_le : Len ≤ MaxLen := by
    rw [BitVec.le_def]
    simpa using hspace
  have hLen_lt : Len.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := Len) (by rfl))
  enter_decl
  steps
  all_goals (try (first | exact hnew_le | simp [hlen0]))
  -- Loop writes `array[i]` into `storage[i]` for `i < Len`, leaving `len` unchanged (still 0).
  loop_inv nat (fun i _ _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = 0 ∧ List.take i (storage v).toList = array.toList.take i⟧)
  ·
    sl
    simp [hlen0]
  ·
    simp
  ·
    intro i hlo hhi
    steps
    all_goals (try (first | exact hnew_le | simp [hlen0]))
    subst_vars
    -- `steps` reduces the heap part; we are left with the pure prefix facts for the invariant.
    -- `steps` leaves a bunch of inaccessible hypotheses (`v✝`, `a✝`, `#v_12`, ...).
    -- We rename them from the end of the context, one-by-one, so this is robust to insertion/removal.
    rename_i h_isSome
    rename_i h_dec
    rename_i u2
    rename_i h_cast
    rename_i h_add
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hi32 : i < 2 ^ 32 := lt_of_lt_of_le hhi (Nat.le_of_lt hLen_lt)
    have hiArr : i < array.toList.length := by
      simpa [List.Vector.toList_length] using hhi
    have hiMax : i < MaxLen.toNat := lt_of_lt_of_le hhi hspace
    have hiStor : i < (storage v).toList.length := by
      simpa [storage, List.Vector.toList_length] using hiMax
    constructor
    ·
      -- `len` does not change when we only update `storage`.
      -- (We are replacing the `head` of the tuple.)
      simpa [len] using hlenV
    ·
      -- Show the updated prefix matches `array.toList.take (i+1)`.
      have hlenVNat : (len v).toNat = 0 := by
        simpa using congrArg BitVec.toNat hlenV
      have hi32' : i < 4294967296 := by
        simpa using hi32
      have htoNat_i : (BitVec.ofNat 32 i).toNat = i := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32']
      have hsum_lt : (len v).toNat + (BitVec.ofNat 32 i).toNat < 2 ^ 32 := by
        simpa [hlenVNat, htoNat_i] using hi32
      have htoNat_idx :
          (len v + BitVec.ofNat 32 i).toNat = i := by
        have htoNat_add :=
          BitVec.toNat_add_of_lt (x := len v) (y := BitVec.ofNat 32 i) hsum_lt
        simpa [hlenVNat, htoNat_i] using htoNat_add
      have htoNat_idx' :
          (Builtin.indexTpl v Builtin.Member.head.tail + BitVec.ofNat 32 i).toNat = i := by
        simpa [len] using htoNat_idx

      -- Normalize the tuple update performed by the loop body down to a `List.set` on
      -- `storage.toList`. This avoids definitional-equality issues from the `Fin` proofs created
      -- by extraction.
      simp (config := {contextual := false})
        [storage, len, List.Vector.toList_set, htoNat_idx', List.Vector.get_eq_get_toList,
          List.get_eq_getElem]

      -- The index that extraction produces is modular (`toNat` of a `U32` addition); reduce it to `i`
      -- using `len v = 0` and `i < 2^32`.
      have hlenVNat0 : BitVec.toNat v.2.1 = 0 := by
        -- `v.2.1` is the concrete `len` field after simplification.
        simpa [len] using hlenVNat
      have hmod_i : ((BitVec.toNat v.2.1 + i) % 4294967296) = i := by
        simp [hlenVNat0, Nat.mod_eq_of_lt hi32']
      try simp [hmod_i]

      have hiStor_toList : i < (List.Vector.toList v.1).length := by
        -- `v.1` is a `Vector` of length `MaxLen.toNat`.
        simpa [List.Vector.toList_length] using hiMax
      have htakeV_toList : List.take i (List.Vector.toList v.1) = List.take i (List.Vector.toList array) := by
        simpa [storage] using htakeV
      have hiArr_toList : i < (List.Vector.toList array).length := by
        simpa using hiArr

      -- Extraction indexes `array` via a `u32` cast, so `i` appears as `i % 2^32`.
      have hmodIdx : i % 4294967296 = i := Nat.mod_eq_of_lt hi32'
      simp (config := {failIfUnchanged := false}) [hmodIdx]

      -- Now use the standard `take_succ` lemmas plus the loop IH.
      calc
        List.take (i + 1) ((List.Vector.toList v.1).set i ((List.Vector.toList array)[i]'hiArr_toList)) =
        List.take i (List.Vector.toList v.1) ++ [((List.Vector.toList array)[i]'hiArr_toList)] := by
          simpa using
            (List.take_succ_set_eq_take_append
              (l := (List.Vector.toList v.1)) (n := i) (a := ((List.Vector.toList array)[i]'hiArr_toList))
              (hn := hiStor_toList))
        _ = List.take i (List.Vector.toList array) ++ [((List.Vector.toList array)[i]'hiArr_toList)] := by
          -- rewrite the prefix using the loop IH
          simp [htakeV_toList]
        _ = List.take (i + 1) (List.Vector.toList array) := by
          symm
          simpa using
            (List.take_succ_eq_take_append_get (l := (List.Vector.toList array)) (n := i) (hn := hiArr_toList))
  ·
    -- After the loop, `len` is set to `new_len = Len`.
    steps
    all_goals (try (first | exact hnew_le | simp [hlen0]))
    subst_vars
    -- Rename the tail of the context to get the loop witness and its invariant.
    rename_i h_isSome
    rename_i h_dec
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hlenSelfNat : (Builtin.indexTpl self Builtin.Member.head.tail).toNat = 0 := by
      simpa [len] using congrArg BitVec.toNat hlen0
    have hcastLenNat : ((↑(List.Vector.length array) : U 32)).toNat = Len.toNat := by
      have : List.Vector.length array = Len.toNat := by rfl
      simp [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLen_lt]
    have hsum : (Builtin.indexTpl self Builtin.Member.head.tail).toNat + ((↑(List.Vector.length array) : U 32)).toNat < 2 ^ 32 := by
      simpa [hlenSelfNat, hcastLenNat] using hLen_lt
    have htoNat_newLen :
        (Builtin.indexTpl self Builtin.Member.head.tail + (↑(List.Vector.length array) : U 32)).toNat = Len.toNat := by
      have htoNat_add :=
        BitVec.toNat_add_of_lt (x := Builtin.indexTpl self Builtin.Member.head.tail)
          (y := (↑(List.Vector.length array) : U 32)) hsum
      simpa [hlenSelfNat, hcastLenNat] using htoNat_add
    constructor
    ·
      -- boundedness reduces to `Len.toNat ≤ MaxLen.toNat`.
      have hLen_lt' : Len.toNat < 4294967296 := by
        simpa using hLen_lt
      have hmod :
          ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + Len.toNat) % 4294967296 = Len.toNat := by
        simp [hlenSelfNat, Nat.mod_eq_of_lt hLen_lt']
      -- `bounded` is about `toNat` of the post-loop `len`, which is modular addition.
      simpa [bounded, len, hmod] using hspace
    ·
      have hLen_lt' : Len.toNat < 4294967296 := by
        simpa using hLen_lt
      have hmod :
          ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + Len.toNat) % 4294967296 = Len.toNat := by
        simp [hlenSelfNat, Nat.mod_eq_of_lt hLen_lt']
      have htakeArr : array.toList.take Len.toNat = array.toList := by
        simp [List.Vector.toList_length]
      -- `embed` is `take len storage`; `storage` is unchanged by a tail update.
      have htakeV' :
          List.take Len.toNat (List.Vector.toList v.1) = List.take Len.toNat (List.Vector.toList array) := by
        simpa [storage] using htakeV
      have htakeArr' :
          List.take Len.toNat (List.Vector.toList array) = List.Vector.toList array := by
        simpa using htakeArr
      -- Reduce to the loop invariant prefix equation at `Len`.
      simpa [embed, active, storage, len, hmod] using (htakeV'.trans htakeArr')

theorem from_array_spec {p T MaxLen Len array}
    (hbounded : Len.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_array».call
        h![T, MaxLen, Len] h![array])
      (fun r => bounded r ∧ embed r = array.toList) := by
  enter_decl
  steps
  steps [new_spec]
  rename_i vecVal
  -- `vecVal : bounded v ∧ len v = 0 ∧ embed v = []` for the freshly-allocated `v` stored in `vec`.
  have hlen0 : len _ = 0 := vecVal.2.1
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v',
        [vec ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
          ⟦bounded v' ∧ embed v' = array.toList⟧))
  ·
    -- call
    exact extend_from_array_from_empty_spec (p := p) (T := T) (MaxLen := MaxLen) (Len := Len)
      (selfRef := vec) (array := array) (hlen0 := hlen0) (hspace := hbounded)
  ·
    -- read back the updated value
    intro _
    steps
    subst_vars
    assumption

theorem extend_from_slice_spec {p T MaxLen selfRef self slice}
    (hspace : (len self).toNat + slice.length ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_slice».call
        h![T, MaxLen] h![selfRef, slice])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = embed self ++ slice⟧) := by
  have hb_self : bounded self := by
    have : (len self).toNat ≤ (len self).toNat + slice.length := by
      simpa using (Nat.le_add_right (len self).toNat slice.length)
    exact le_trans this hspace
  have hMax_lt : MaxLen.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  have hslen_lt : slice.length < 2 ^ 32 := by
    have : slice.length ≤ MaxLen.toNat := by
      have : slice.length ≤ (len self).toNat + slice.length := by
        simpa using (Nat.le_add_left slice.length (len self).toNat)
      exact le_trans this hspace
    exact lt_of_le_of_lt this hMax_lt
  have hcastLenNat : ((↑slice.length : U 32)).toNat = slice.length := by
    have hslen_lt' : slice.length < 4294967296 := by
      simpa using hslen_lt
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hslen_lt']
  have hsum_lt : (len self).toNat + ((↑slice.length : U 32)).toNat < 2 ^ 32 := by
    -- Avoid `simp` rewriting `(↑slice.length : U 32).toNat` to `slice.length % 2^32` too early.
    rw [hcastLenNat]
    exact lt_of_le_of_lt hspace hMax_lt
  have hnew_le : len self + (↑slice.length : U 32) ≤ MaxLen := by
    rw [BitVec.le_def]
    rw [BitVec.toNat_add_of_lt (x := len self) (y := (↑slice.length : U 32)) hsum_lt]
    rw [hcastLenNat]
    exact hspace
  enter_decl
  steps

  -- Loop writes `slice[i]` into `storage[len + i]` for `i < slice.length`, leaving `len` unchanged.
  loop_inv nat (fun i _ _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + i) (storage v).toList =
              embed self ++ slice.take i⟧)
  ·
    sl
    simp [Nat.add_zero, embed, active, storage]
  ·
    simp
  ·
    intro i hlo hhi
    steps
    subst_vars
    rename_i h_isSome
    rename_i h_dec
    rename_i u2
    rename_i h_cast
    rename_i h_add
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hi32 : i < 2 ^ 32 := lt_of_lt_of_le hhi (Nat.le_of_lt hslen_lt)
    have hiSlice : i < slice.length := hhi
    have hiMax : (len self).toNat + i < MaxLen.toNat := by
      have : (len self).toNat + i < (len self).toNat + slice.length :=
        Nat.add_lt_add_left hhi (len self).toNat
      exact lt_of_lt_of_le this hspace
    have hiStor : (len self).toNat + i < (storage v).toList.length := by
      simpa [storage, List.Vector.toList_length] using hiMax
    constructor
    ·
      simpa [len] using hlenV
    ·
      have hlenVNat : (len v).toNat = (len self).toNat := by
        simpa using congrArg BitVec.toNat hlenV
      have hi32' : i < 4294967296 := by
        simpa using hi32
      have htoNat_i : (BitVec.ofNat 32 i).toNat = i := by
        simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32']
      have hsum_lt' : (len v).toNat + (BitVec.ofNat 32 i).toNat < 2 ^ 32 := by
        have : (len self).toNat + i < 2 ^ 32 := by
          have : (len self).toNat + i < (len self).toNat + slice.length :=
            Nat.add_lt_add_left hhi (len self).toNat
          exact lt_of_lt_of_le (lt_of_lt_of_le this hspace) (Nat.le_of_lt hMax_lt)
        simpa [hlenVNat, htoNat_i] using this
      have htoNat_idx :
          (len v + BitVec.ofNat 32 i).toNat = (len self).toNat + i := by
        have htoNat_add :=
          BitVec.toNat_add_of_lt (x := len v) (y := BitVec.ofNat 32 i) hsum_lt'
        simpa [hlenVNat, htoNat_i] using htoNat_add
      have htoNat_idx' :
          (Builtin.indexTpl v Builtin.Member.head.tail + BitVec.ofNat 32 i).toNat =
            (len self).toNat + i := by
        simpa [len] using htoNat_idx

      simp (config := {contextual := false})
        [storage, len, List.Vector.toList_set, htoNat_idx', List.get_eq_getElem]

      have hlenVNat' : BitVec.toNat v.2.1 = (len self).toNat := by
        simpa [len] using hlenVNat
      have hsum_lt'' : BitVec.toNat v.2.1 + i < 4294967296 := by
        have : (len self).toNat + i < 2 ^ 32 := by
          have : (len self).toNat + i < (len self).toNat + slice.length :=
            Nat.add_lt_add_left hhi (len self).toNat
          exact lt_of_lt_of_le (lt_of_lt_of_le this hspace) (Nat.le_of_lt hMax_lt)
        simpa [hlenVNat'] using this
      have hmod :
          ((BitVec.toNat v.2.1 + i) % 4294967296) = (len self).toNat + i := by
        have hmod' : (BitVec.toNat v.2.1 + i) % 4294967296 = BitVec.toNat v.2.1 + i :=
          Nat.mod_eq_of_lt hsum_lt''
        simpa [hlenVNat'] using hmod'
      try simp [hmod]

      have hiStor_toList : (len self).toNat + i < (List.Vector.toList v.1).length := by
        simpa [List.Vector.toList_length] using hiMax
      have htakeV_toList :
          List.take ((len self).toNat + i) (List.Vector.toList v.1) =
            embed self ++ slice.take i := by
        simpa [storage] using htakeV

      -- As above, normalize `i % 2^32` away in the goal.
      have hmod_i : i % 4294967296 = i := Nat.mod_eq_of_lt hi32'
      simp [hmod_i]

      calc
        List.take ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + (i + 1))
            ((List.Vector.toList v.1).set ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + i)
              (slice[i]'hiSlice)) =
          List.take ((Builtin.indexTpl self Builtin.Member.head.tail).toNat + i) (List.Vector.toList v.1) ++
            [slice[i]'hiSlice] := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (List.take_succ_set_eq_take_append
              (l := (List.Vector.toList v.1))
              (n := (Builtin.indexTpl self Builtin.Member.head.tail).toNat + i)
              (a := slice[i]'hiSlice)
              (hn := by simpa [len] using hiStor_toList))
        _ = (embed self ++ slice.take i) ++ [slice[i]'hiSlice] := by
          simpa [len] using
            congrArg (fun t => t ++ [slice[i]'hiSlice]) htakeV_toList
        _ = embed self ++ (slice.take i ++ [slice[i]'hiSlice]) := by
          simp [List.append_assoc]
        _ = embed self ++ slice.take (i + 1) := by
          symm
          simpa using
            (List.take_succ_eq_take_append_get (l := slice) (n := i) (hn := hiSlice))
  ·
    steps
    subst_vars
    rename_i h_isSome
    rename_i h_dec
    rename_i hinv
    rename_i v
    rcases hinv with ⟨hlenV, htakeV⟩
    have hsum_lt_final : (len self).toNat + slice.length < 4294967296 := by
      have : (len self).toNat + slice.length < 2 ^ 32 := lt_of_le_of_lt hspace hMax_lt
      simpa using this
    have hmod :
        (((len self).toNat + slice.length) % 4294967296) = (len self).toNat + slice.length := by
      exact Nat.mod_eq_of_lt hsum_lt_final
    have hmod_simp :
        ((BitVec.toNat self.2.1 + List.length slice) % 4294967296) =
          BitVec.toNat self.2.1 + List.length slice := by
      simpa [len] using hmod
    constructor
    ·
      simpa [bounded, len, hmod_simp, hcastLenNat] using hspace
    ·
      have htakeSlice : slice.take slice.length = slice := by
        simp
      have hmodSlice : slice.length % 4294967296 = slice.length := by
        -- `slice.length < 2^32` was established earlier in the proof as `hslen_lt`.
        have hslen_lt' : slice.length < 4294967296 := by
          simpa using hslen_lt
        exact Nat.mod_eq_of_lt hslen_lt'
      have htakeV' :
          List.take ((len self).toNat + slice.length) (storage v).toList =
            embed self ++ slice.take slice.length := by
        -- The extracted loop index computes `slice.length` via a `u32` truncation; under our bounds
        -- this truncation is identity.
        simpa [hmodSlice, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htakeV
      simpa [embed, active, storage, len, hmod_simp, htakeSlice] using htakeV'

theorem extend_from_bounded_vec_spec {p T MaxLen Len selfRef self vec}
    (hbVec : bounded (p := p) (T := T) (MaxLen := Len) vec)
    (hspace : (len self).toNat + (len vec).toNat ≤ MaxLen.toNat) :
    STHoare p env
      [selfRef ↦ ⟨bvTp T MaxLen, self⟩]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::extend_from_bounded_vec».call
        h![T, MaxLen, Len] h![selfRef, vec])
      (fun _ =>
        ∃∃ v',
          [selfRef ↦ ⟨bvTp T MaxLen, v'⟩] ⋆
            ⟦bounded v' ∧ embed v' = embed self ++ embed vec⟧) := by
  have hMax_lt : MaxLen.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := MaxLen) (by rfl))
  have hsum_lt : (len self).toNat + (len vec).toNat < 2 ^ 32 := lt_of_le_of_lt hspace hMax_lt
  have hnew_le : len self + len vec ≤ MaxLen := by
    rw [BitVec.le_def]
    rw [BitVec.toNat_add_of_lt (x := len self) (y := len vec) hsum_lt]
    exact hspace
  have hLen_lt : Len.toNat < 2 ^ 32 := by
    simpa using (BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := Len) (by rfl))
  have hlenVec : (embed vec).length = (len vec).toNat :=
    embed_length_eq_len_toNat (v := vec) hbVec

  enter_decl
  -- Compute `append_len := vec.len()` and `new_len := self.len + append_len`.
  steps [len_concrete_spec (p := p) (T := T) (MaxLen := Len) (self := vec)]
  subst_vars
  -- Debug: see what `steps` introduced.
  -- trace_state
  all_goals (try (first | exact hnew_le | exact ()))

  -- The extracted code is `let _ := (if isUnconstrained then ... else ...) in self.len := new_len`.
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p T MaxLen,
        [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
          ⟦len v = len self ∧
            List.take ((len self).toNat + (len vec).toNat) (storage v).toList =
              embed self ++ embed vec⟧))
  ·
    -- The `if isUnconstrained() { ... } else { ... }` branch.
    apply STHoare.ite_intro_of_false
    · simp
    ·
      -- Constrained branch: `exceeded_len := false; for i in 0..Len { ... }`.
      steps
      loop_inv nat (fun i _ _ =>
          ∃∃ v : Repr p T MaxLen,
            [selfRef ↦ ⟨bvTp T MaxLen, v⟩] ⋆
              [exceeded_len ↦ ⟨.bool, decide ((len vec).toNat < i)⟩] ⋆
                ⟦len v = len self ∧
                  List.take ((len self).toNat + Nat.min i (len vec).toNat) (storage v).toList =
                    embed self ++ (embed vec).take (Nat.min i (len vec).toNat)⟧)
      ·
        -- base case `i = 0`
        sl
        simp [Nat.min_zero, embed, active, storage]
      ·
        simp
      ·
        intro i hlo hhi
        -- One iteration: update `exceeded_len` and (if needed) write `vec[i]` into `self.storage[len+i]`.
        steps
        subst_vars
        all_goals (try (first | exact () | exact hnew_le))
        -- Pull the loop invariant witness and its pure facts into named hypotheses before we split on the inner `if`.
        rename_i h_isSome_el
        rename_i u_el
        rename_i hinv
        rename_i v0
        -- `u_el` is the pure part of the loop invariant for the current `hinv`.
        rcases u_el with ⟨hlenV, htakeV⟩
        apply STHoare.ite_intro
        ·
          intro hcond
          -- We are in the write branch, so `i < append_len` (expressed as `i ≤ len vec` and `i ≠ len vec`).
          have pf : i < 2 ^ 32 := lt_of_lt_of_le hhi (Nat.le_of_lt hLen_lt)
          have hcond' := by
            -- `hcond` is `bNot exceeded_len = true` after the update `exceeded_len := exceeded_len || (i == append_len)`.
            -- We keep the simplified shape inferred by `simp` to avoid having to name extraction binders.
            simpa [Lens.modify, Lens.get, Option.get_some] using hcond
          rcases hcond' with ⟨hi_le, hi_ne_bv⟩
          have hltVec : i < (len vec).toNat := by
            refine lt_of_le_of_ne hi_le ?_
            intro hi_eq
            apply hi_ne_bv
            -- Goal is the extraction's bitvector equality `i# = append_len`; rewrite it using local equalities.
            have hbv : BitVec.ofNat 32 i = len vec := by
              -- `i = (len vec).toNat` implies `ofNat i = len vec`.
              simpa [hi_eq] using (BitVec.ofNat_toNat (x := len vec))
            -- Close by rewriting `i#` and `append_len` with the local context.
            simp_all [BitVec.ofNatLT_eq_ofNat]
          have hmin_i : Nat.min i (len vec).toNat = i := Nat.min_eq_left (Nat.le_of_lt hltVec)
          have hmin_succ : Nat.min (i + 1) (len vec).toNat = i + 1 :=
            Nat.min_eq_left (Nat.succ_le_of_lt hltVec)

          -- Run the branch body, using the `get_unchecked` semantic spec for `vec[i]`.
          steps [get_unchecked_spec (p := p) (T := T) (MaxLen := Len) (self := vec)
            (index := BitVec.ofNatLT i (lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi))
            (hindex := by
              -- `get_unchecked` needs `index.toNat < Len.toNat`; extraction represents the loop index as `i#'pf`.
              -- Depending on normalization, the goal is either `toNat (ofNatLT ..) < Len.toNat` or
              -- `toNat (ofNat ..) < Len.toNat`; both reduce to `i < Len.toNat` under `i < 2^32`.
              have hi32 : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
              have hi32' : i < 4294967296 := by simpa using hi32
              simpa [BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32'] using hhi)]
          all_goals (try (first | exact () | exact hnew_le))
          subst_vars
          -- `steps` leaves two pure goals: the `exceeded_len` cell value (`heq`) and the loop-invariant payload.
          case h₁.heq =>
            -- `exceeded_len` after the update is `decide (len vec < i+1)`.
            simp [Lampe.AnyValue, Lens.modify, Lens.get, Option.get_some,
              decide_lt_succ_eq_bv (x := len vec) pf]
          case h₁.a =>
            -- Main invariant payload after the storage write.
            -- The extracted branch introduces a few `unit`/evidence binders; name the semantic element equation.
            rename_i _u_post
            rename_i _h_isSome_set
            rename_i elemEq
            rename_i hidx
            constructor
            ·
              -- Only `storage` changes; `len` stays the same.
              simpa [len] using hlenV
            ·
              -- Rewrite mins under `i < len vec`.
              simp [hmin_i, hmin_succ] at htakeV ⊢
              have hiMax : (len self).toNat + i < MaxLen.toNat := by
                have : (len self).toNat + i < (len self).toNat + (len vec).toNat :=
                  Nat.add_lt_add_left hltVec (len self).toNat
                exact lt_of_lt_of_le this hspace
              have hiEmb : i < (embed vec).length := by
                simpa [hlenVec] using hltVec
              -- The written element is the `i`th element of `embed vec` (this avoids mentioning the extracted `#v_*` name).
              have hi32 : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
              have hi32' : i < 4294967296 := by simpa using hi32
              have helem' := elemEq (by
                -- `elemEq` is stated at `(i#).toNat`, which normalizes to `i % 2^32`.
                simpa [Nat.mod_eq_of_lt hi32'] using hiEmb)
              generalize_proofs at helem'
              have helem'' := (by
                -- normalize the casted index `(i#).toNat` down to `i`
                simpa [BitVec.toNat_ofNatLT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32'] using helem')

              -- `toNat (ofNat 32 i) = i` under `i < 2^32`.
              have hi32' : i < 4294967296 := by
                have : i < 2 ^ 32 := lt_of_lt_of_le hhi (Nat.le_of_lt hLen_lt)
                simpa using this
              have htoNat_i : (BitVec.ofNat 32 i).toNat = i := by
                simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32']

              -- Compute the extracted write index `i_3643` in `Nat`.
              have hlenHinVNat : (len hinv).toNat = (len self).toNat := by
                simpa using congrArg BitVec.toNat hlenV
              have hsum_lt' : (len hinv).toNat + (BitVec.ofNat 32 i).toNat < 2 ^ 32 := by
                have : (len self).toNat + i < 2 ^ 32 := by
                  have : (len self).toNat + i < (len self).toNat + (len vec).toNat :=
                    Nat.add_lt_add_left hltVec (len self).toNat
                  exact lt_trans this hsum_lt
                simpa [hlenHinVNat, htoNat_i] using this
              have htoNat_idx : i_3643.toNat = (len self).toNat + i := by
                have htoNat_add :=
                  BitVec.toNat_add_of_lt (x := len hinv) (y := BitVec.ofNat 32 i) hsum_lt'
                have hidx' : i_3643 = len hinv + BitVec.ofNat 32 i := by
                  simpa [len, bitvec_ofNatLT_eq_ofNat (i := i) (by simpa using hi32')] using hidx
                calc
                  i_3643.toNat = (len hinv + BitVec.ofNat 32 i).toNat := by simpa [hidx']
                  _ = (len hinv).toNat + (BitVec.ofNat 32 i).toNat := htoNat_add
                  _ = (len self).toNat + i := by simp [hlenHinVNat, htoNat_i]

              have hiStor_toList : (len self).toNat + i < (List.Vector.toList hinv.1).length := by
                simpa [List.Vector.toList_length] using hiMax
              have htakeV' :
                  List.take ((len self).toNat + i) (List.Vector.toList hinv.1) =
                    embed self ++ List.take i (embed vec) := by
                simpa [storage] using htakeV

              -- Normalize the extracted tuple update down to a `List.set` on `storage.toList`.
              simp (config := {contextual := false})
                [storage, List.Vector.toList_set, htoNat_idx, helem'', List.get_eq_getElem,
                  Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mod_eq_of_lt hi32']
              have hiStor_toList' : i + (len self).toNat < (List.Vector.toList hinv.1).length := by
                simpa [Nat.add_comm] using hiStor_toList
              have htakeV'' :
                  List.take (i + (len self).toNat) (List.Vector.toList hinv.1) =
                    embed self ++ List.take i (embed vec) := by
                simpa [Nat.add_comm] using htakeV'
              calc
                List.take (i + (1 + (len self).toNat))
                    ((List.Vector.toList hinv.1).set (i + (len self).toNat) ((embed vec)[i]'hiEmb)) =
                  List.take (i + (len self).toNat) (List.Vector.toList hinv.1) ++ [((embed vec)[i]'hiEmb)] := by
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                    (List.take_succ_set_eq_take_append
                      (l := (List.Vector.toList hinv.1)) (n := i + (len self).toNat)
                      (a := ((embed vec)[i]'hiEmb)) (hn := hiStor_toList'))
                _ =
                  (embed self ++ List.take i (embed vec)) ++ [((embed vec)[i]'hiEmb)] := by
                  simpa [htakeV'']
                _ =
                  embed self ++ (List.take i (embed vec) ++ [((embed vec)[i]'hiEmb)]) := by
                  simp [List.append_assoc]
                _ = embed self ++ List.take (i + 1) (embed vec) := by
                  simpa using (List.take_succ_eq_take_append_get (l := embed vec) (n := i) (hn := hiEmb))
        ·
          intro hcond
          -- Skip branch: no write, only the flag update.
          steps
          subst_vars
          -- `steps` leaves two pure goals: the updated `exceeded_len` cell value and the invariant payload.
          case h₁.heq =>
            have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
            simp [Lampe.AnyValue, Lens.modify, Lens.get, Option.get_some,
              decide_lt_succ_eq_bv (x := len vec) pf]
          case h₁.a =>
            have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := Len) hhi
            -- In the skip branch `(!flag) = false`, hence the updated flag is `true`, i.e.
            -- `len vec < i` or `i = len vec`.
            have h_exceeded := (by
              -- `!x = false` implies `x = true`.
              simpa using (congrArg Bool.not hcond))
            have hflag_raw :
                (len vec).toNat < i ∨ BitVec.ofNatLT i pf = append_len := by
              simpa [Lens.modify, Lens.get, Option.get_some] using h_exceeded
            have hge : (len vec).toNat ≤ i := by
              cases hflag_raw with
              | inl hlt =>
                  exact Nat.le_of_lt hlt
              | inr hbv =>
                  have pf' : i < 4294967296 := by
                    simpa using pf
                  have : i = (len vec).toNat := by
                    have ht := congrArg BitVec.toNat hbv
                    have ht' : i = append_len.toNat := by
                      simpa [BitVec.toNat_ofNatLT, Nat.mod_eq_of_lt pf'] using ht
                    -- Rewrite `append_len` to `len vec` using the equality from the outer `steps`.
                    simpa [*] using ht'
                  exact this.symm.le
            have hmin_i : Nat.min i (len vec).toNat = (len vec).toNat := Nat.min_eq_right hge
            have hmin_succ : Nat.min (i + 1) (len vec).toNat = (len vec).toNat := by
              exact Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ i))
            constructor
            · simpa [len] using hlenV
            ·
              simp [hmin_i, hmin_succ] at htakeV ⊢
              simpa using htakeV
      ·
        -- After the loop, use `min Len append_len = append_len` (since `bounded vec`).
        steps
        subst_vars
        -- `steps` leaves some `decide` bookkeeping proof terms; name and ignore them to reach the loop invariant.
        rename_i _hdec
        rename_i _hsumlt
        rename_i _u_post
        rename_i hinv
        rename_i v
        rcases hinv with ⟨hlenV, htakeV⟩
        have hmin : Nat.min Len.toNat (len vec).toNat = (len vec).toNat := Nat.min_eq_right hbVec
        have htakeVec : List.take (len vec).toNat (embed vec) = embed vec := by
          -- `bounded vec` implies `length (embed vec) = len vec.toNat`.
          simpa [hlenVec] using (List.take_length (embed vec))
        constructor
        · simpa [len] using hlenV
        ·
          have htakeV' :
              List.take ((len self).toNat + (len vec).toNat) (storage v).toList =
                embed self ++ List.take (len vec).toNat (embed vec) := by
            simpa [hmin, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htakeV
          simpa [htakeVec] using htakeV'
  ·
    intro _
    -- Final `self.len := new_len`: `storage` unchanged, `len` updated to `len self + len vec`.
    steps
    subst_vars
    -- Name the `steps` products from the end of the context.
    rename_i h_isSome_set
    rename_i _hdec
    rename_i _hsumlt
    rename_i _u_post
    rename_i h_pre
    rcases _u_post with ⟨hlenV, htakeV⟩
    -- The modified value is `h_pre` with its `len` field overwritten with `len self + len vec`.
    set v' :=
      (((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify h_pre
              (Builtin.indexTpl self Builtin.Member.head.tail + len vec)).get
          h_isSome_set) with hv'
    constructor
    ·
      have hb : BitVec.toNat (len self + len vec) ≤ MaxLen.toNat :=
        (BitVec.le_def).1 hnew_le
      -- `bounded v'` reduces to the `U32` bound on the new length.
      simpa [v', hv', bounded, len, Lens.modify, Lens.get, Access.get, Access.modify, Option.get_some] using hb
    ·
      have hsum_lt' : BitVec.toNat (len self) + BitVec.toNat (len vec) < 4294967296 := by
        simpa using hsum_lt
      have hmod :
          ((BitVec.toNat (len self) + BitVec.toNat (len vec)) % 4294967296) =
            BitVec.toNat (len self) + BitVec.toNat (len vec) := by
        exact Nat.mod_eq_of_lt hsum_lt'
      have hmod' :
          ((BitVec.toNat (Builtin.indexTpl self Builtin.Member.head.tail) +
              BitVec.toNat (Builtin.indexTpl vec Builtin.Member.head.tail)) % 4294967296) =
            BitVec.toNat (Builtin.indexTpl self Builtin.Member.head.tail) +
              BitVec.toNat (Builtin.indexTpl vec Builtin.Member.head.tail) := by
        simpa [len] using hmod
      -- `embed v'` is `take` of the unchanged storage at the new length.
      simpa [v', hv', embed, active, storage, len, Lens.modify, Lens.get, Access.get, Access.modify,
        Option.get_some, Builtin.indexTpl, Builtin.replaceTuple', hmod'] using htakeV

theorem from_parts_spec {p T MaxLen arr l}
    (hb : l.toNat ≤ MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::from_parts».call
        h![T, MaxLen] h![arr, l])
      (fun r => bounded r ∧ embed r = List.take l.toNat arr.toList) := by
  have hble : l ≤ MaxLen := by
    rw [BitVec.le_def]
    simpa using hb
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
      · sl
        simp
      · simp
      ·
        intro i hlo hhi
        -- The loop body starts with `let b := uGeq i l; if b then ...`.
        apply (STHoare.letIn_intro
          (Q := fun b =>
            ∃∃ a : List.Vector (T.denote p) MaxLen.toNat,
              [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
                ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList ∧
                  b = decide (l.toNat ≤ i)⟧))
        ·
          -- Evaluate the pure builtin `uGeq`.
          apply Lampe.Steps.pull_exi
          intro a
          apply (STHoare.consequence
            (H₁ := [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆ ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList⟧)
            (Q₁ := fun b =>
              [array ↦ ⟨Tp.array T MaxLen, a⟩] ⋆
                ⟦List.take l.toNat a.toList = List.take l.toNat arr.toList ∧
                  b = decide (l.toNat ≤ i)⟧))
          · exact SLP.entails_self
          ·
            intro b
            sl; assumption
          ·
            steps [STHoare.genericTotalPureBuiltin_intro (b := Builtin.uGeq) (h := rfl)]
            simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
              BitVec.toNat_ofNatLT, BitVec.le_def, ge_iff_le]
            simp
        ·
          intro b
          apply STHoare.ite_intro
          ·
            intro hbTrue
            steps
            generalize_proofs
            -- Order for `rename_i`: oldest-to-newest among the last renamable binders.
            rename_i a hpre h_isSome u pf
            rcases hpre with ⟨htake, hbdec⟩
            -- In this branch, `b = true`, so `l.toNat ≤ i`.
            have hli : l.toNat ≤ i := by
              have : decide (l.toNat ≤ i) = true := by
                calc
                  decide (l.toNat ≤ i) = b := by simpa using (Eq.symm hbdec)
                  _ = true := hbTrue
              exact (decide_eq_true_iff).1 this
            -- Normalize the post-state array update.
            simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
              BitVec.toNat_ofNatLT, Lens.modify, Lens.get, Access.get, Access.modify, Option.get_some,
              List.Vector.toList_set]
            -- `simp_all` leaves some `Option`-monad plumbing; `simp` finishes normalizing it.
            simp
            have htake_len : (List.take l.toNat a.toList).length = l.toNat := by
              simp [List.length_take, List.Vector.toList_length, Nat.min_eq_left hb]
            have hdrop :
                List.take l.toNat (a.toList.set i (Tp.zero p T)) = List.take l.toNat a.toList := by
              have ht :=
                (List.take_set (l := a.toList) (n := l.toNat) (i := i) (a := Tp.zero p T))
              have hset :
                  (List.take l.toNat a.toList).set i (Tp.zero p T) = List.take l.toNat a.toList := by
                exact List.set_eq_of_length_le (by simpa [htake_len] using hli)
              simpa [hset] using ht
            simpa [hdrop] using htake
          ·
            intro hbFalse
            steps
            generalize_proofs
            rename_i a hpre u
            rcases hpre with ⟨htake, _⟩
            exact htake
      ·
        steps; assumption
        -- the loop invariant is already the postcondition we need here
  ·
    intro _
    steps
    subst_vars
    rename_i hinv
    rename_i a
    constructor
    · simpa [bounded, len] using hb
    · simpa [embed, active, storage, len] using hinv

end Lampe.Stdlib.Collections.BoundedVec
