import Stdlib.Collections.BoundedVec

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.12»

/-!
Higher-order method specs for Noir `BoundedVec`: `map` and `mapi` (pure variants).

This module is intentionally not imported by `Stdlib.Collections.BoundedVec` yet; develop proofs
here without breaking the main build, then import once stable.
-/

private theorem len_concrete_spec' {p T MaxLen self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len».call h![T, MaxLen] h![self])
      (fun r => r = len self) := by
  enter_decl
  steps
  simpa [len]

private theorem get_unchecked_concrete_spec' {p T MaxLen self index}
    (hindex : index.toNat < MaxLen.toNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get_unchecked».call h![T, MaxLen]
        h![self, index])
      (fun r => r = (storage self)[index.toNat]'hindex) := by
  enter_decl
  steps
  simpa [storage]

@[simp]
private theorem len_modify_head_tail {p T MaxLen}
    {v : Tp.denote p (bvTp T MaxLen)} {l : U 32}
    (h : ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify v l).isSome = true) :
    len (((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify v l).get h) = l := by
  unfold len
  simp [Lens.modify, Lens.get, Access.modify]

private lemma toNat_ofNat32 (i : Nat) (pf32 : i < 2 ^ 32) :
    (BitVec.ofNat 32 i).toNat = i := by
  have pf' : i < 4294967296 := by
    -- `2^32 = 4294967296`.
    simpa using pf32
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pf']

private lemma nat_lt_of_decide_bv_lt_true {i : Nat} {x : U 32} (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNat 32 i < x) = true) : i < x.toNat := by
  have hlt_bv : BitVec.ofNat 32 i < x := by
    have := of_decide_eq_true h
    simpa using this
  exact nat_lt_of_bv_lt (i := i) (x := x) pf32 hlt_bv

private lemma nat_le_of_decide_bv_lt_false {i : Nat} {x : U 32} (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNat 32 i < x) = false) : x.toNat ≤ i := by
  by_contra hlt
  have hlt' : i < x.toNat := Nat.lt_of_not_ge hlt
  have hlt_bv : BitVec.ofNat 32 i < x := by
    -- Convert back to a BitVec comparison; `pf32` avoids wraparound.
    have pf' : i < 4294967296 := by simpa using pf32
    have hi_toNat : (BitVec.ofNat 32 i).toNat = i := by
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pf']
    -- `BitVec.lt_def` is by `toNat`.
    have : (BitVec.ofNat 32 i).toNat < x.toNat := by simpa [hi_toNat] using hlt'
    simpa [BitVec.lt_def] using this
  have htrue : decide (BitVec.ofNat 32 i < x) = true := by simp [hlt_bv]
  have : (true : Bool) = false := by simpa [htrue] using h
  cases this

-- Wrappers for the extracted loop index, which is usually `BitVec.ofNatLT i pf32`.
private lemma nat_lt_of_decide_bv_lt_trueLT {i : Nat} {x : U 32} (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNatLT i pf32 < x) = true) : i < x.toNat := by
  have h' : decide (BitVec.ofNat 32 i < x) = true := by
    simpa using h
  exact nat_lt_of_decide_bv_lt_true (i := i) (x := x) pf32 h'

private lemma nat_le_of_decide_bv_lt_falseLT {i : Nat} {x : U 32} (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNatLT i pf32 < x) = false) : x.toNat ≤ i := by
  have h' : decide (BitVec.ofNat 32 i < x) = false := by
    simpa using h
  exact nat_le_of_decide_bv_lt_false (i := i) (x := x) pf32 h'

private lemma storage_get_eq_embed_get_of_toNat {p T MaxLen} (self : Repr p T MaxLen)
    {idxNat i : Nat} (htoNat : idxNat = i) (hiIdx : idxNat < MaxLen.toNat)
    (hi : i < (embed self).length) :
    (storage self)[idxNat]'hiIdx = (embed self)[i]'hi := by
  have hstorageIdx : idxNat < (storage self).toList.length := by
    simpa [storage, List.Vector.toList_length] using hiIdx
  have hstorage : i < (storage self).toList.length := by
    simpa [htoNat] using hstorageIdx
  have hvec :
      (storage self)[idxNat]'hiIdx = (storage self).toList[idxNat]'hstorageIdx := by
    simpa using (List.Vector.getElem_def (v := storage self) (i := idxNat) (hi := hiIdx))
  have hembed :
      (embed self)[i]'hi = (storage self).toList[i]'hstorage :=
    embed_getElem_toList (self := self) (i := i) (hxs := hi) (hstorage := hstorage)
  calc
    (storage self)[idxNat]'hiIdx = (storage self).toList[idxNat]'hstorageIdx := hvec
    _ = (storage self).toList[i]'hstorage := by simp [htoNat]
    _ = (embed self)[i]'hi := by simpa using hembed.symm

private lemma take_succ_set_eq_map {α β : Type _} (f : α → β) (xs : List α) (l : List β) (i : Nat)
    (hi_xs : i < xs.length) (hi_l : i < l.length)
    (htake : List.take i l = (xs.take i).map f) :
    List.take (i + 1) (l.set i (f (xs[i]'hi_xs))) = (xs.take (i + 1)).map f := by
  have htake_set :
      List.take (i + 1) (l.set i (f (xs[i]'hi_xs))) = List.take i l ++ [f (xs[i]'hi_xs)] := by
    simpa using
      (List.take_succ_set_eq_take_append (l := l) (n := i) (a := f (xs[i]'hi_xs)) hi_l)
  have htake_xs : xs.take (i + 1) = xs.take i ++ [xs[i]'hi_xs] := by
    simpa using (List.take_succ_eq_take_append_get (l := xs) (n := i) (hn := hi_xs))
  calc
    List.take (i + 1) (l.set i (f (xs[i]'hi_xs))) =
        List.take i l ++ [f (xs[i]'hi_xs)] := htake_set
    _ = (xs.take i).map f ++ [f (xs[i]'hi_xs)] := by simp [htake]
    _ = ((xs.take i ++ [xs[i]'hi_xs]).map f) := by
        symm
        simpa using (List.map_append (f := f) (l₁ := xs.take i) (l₂ := [xs[i]'hi_xs]))
    _ = (xs.take (i + 1)).map f := by
        rw [htake_xs]

private lemma mapIdx_const_eq_map {α β : Type _} (f : α → β) (xs : List α) :
    xs.mapIdx (fun _ a => f a) = xs.map f := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      -- Reduce via `mapIdx_cons`; the shifted function is definitional equal for index-ignoring `f`.
      simpa [List.mapIdx_cons, ih]

private lemma take_succ_set_eq_mapIdx {α β : Type _} (f : Nat → α → β) (xs : List α) (l : List β)
    (i : Nat) (hi_xs : i < xs.length) (hi_l : i < l.length)
    (htake : List.take i l = (xs.take i).mapIdx f) :
    List.take (i + 1) (l.set i (f i (xs[i]'hi_xs))) = (xs.take (i + 1)).mapIdx f := by
  have htake_set :
      List.take (i + 1) (l.set i (f i (xs[i]'hi_xs))) = List.take i l ++ [f i (xs[i]'hi_xs)] := by
    simpa using
      (List.take_succ_set_eq_take_append (l := l) (n := i) (a := f i (xs[i]'hi_xs)) hi_l)
  have htake_xs : xs.take (i + 1) = xs.take i ++ [xs[i]'hi_xs] := by
    simpa using (List.take_succ_eq_take_append_get (l := xs) (n := i) (hn := hi_xs))
  have hlen_take : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi_xs)]
  calc
    List.take (i + 1) (l.set i (f i (xs[i]'hi_xs))) =
        List.take i l ++ [f i (xs[i]'hi_xs)] := htake_set
    _ = (xs.take i).mapIdx f ++ [f i (xs[i]'hi_xs)] := by simpa [htake]
    _ = (xs.take (i + 1)).mapIdx f := by
        rw [htake_xs]
        -- `mapIdx_concat` uses `l.length` for the last index.
        rw [List.mapIdx_concat]
        simpa [hlen_take]

private lemma skip_postprocess {p} {H Qfinal : SLP (State p)} (hHQ : H ⊢ Qfinal) :
    STHoare p env H Expr.skip (fun _ => Qfinal) := by
  have hskipH : STHoare p env H Expr.skip (fun v => (v = ()) ⋆ H) := by
    -- `skip_intro` is for `⟦True⟧`; frame it and simplify away the pure `True`.
    simpa using
      (STHoare.frame (p := p) (Γ := env) (H := H)
        (h_hoare := (STHoare.skip_intro (p := p) (Γ := env))))
  refine (STHoare.consequence (p := p) (Γ := env) (tp := Tp.unit) (e := Expr.skip)
    (H₁ := H) (H₂ := H)
    (Q₁ := fun v => (v = ()) ⋆ H)
    (Q₂ := fun _ => Qfinal)
    (h_pre_conseq := SLP.entails_self)
    (h_post_conseq := ?_) hskipH)
  intro v
  -- Drop the pure `v = ()`, then apply `H ⊢ Qfinal`.
  simpa [SLP.star_assoc] using (show (⟦v = ()⟧ ⋆ (H ⋆ ⊤) ⊢ Qfinal ⋆ ⊤) from by
    apply SLP.pure_left
    intro _
    exact SLP.star_mono_r hHQ)

/-!
Shared constrained-branch loop proof for `map`/`mapi`-like methods.

The constrained branch for both methods has the shape:
`for i in 0..MaxLen { if i < self.len { ret[i] := f(..., self[i]) } }`.
-/

private theorem mapLike_constrained_loop_spec
    {p : Prime}
    {T : Tp} {MaxLen : U 32} {Out : Tp}
    {Args : List Tp}
    {self : Repr p T MaxLen}
    {f : FuncRef Args Out}
    {fb : HList (Tp.denote p) Args → Expr (Tp.denote p) Out}
    {fEmb : Nat → Tp.denote p T → Tp.denote p Out}
    {mkArgs : U 32 → Tp.denote p T → HList (Tp.denote p) Args}
    {ret : Ref}
    {vnew : Tp.denote p (bvTp Out MaxLen)}
    (hb : bounded self)
    (hmod :
      ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify vnew (len self)).isSome = true)
    (inv_pure :
      ∀ (i : U 32) (a : Tp.denote p T),
        (hi : i.toNat < (embed self).length) →
          STHoare p env ⟦⟧ (fb (mkArgs i a)) (fun r => r = fEmb i.toNat a)) :
    STHoare p env
      ([ret ↦ ⟨bvTp Out MaxLen,
        ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify vnew (len self)).get hmod⟩] ⋆
        [λf ↦ fb])
      (Expr.letIn
        (Expr.loop (↑0) MaxLen fun i =>
          expr!![
            {
              let lenFn =
                («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::len»<T, MaxLen : u32>
                  as λ(${bvTp T MaxLen}) -> u32);
              let selfLen = (lenFn as λ(${bvTp T MaxLen}) -> u32)(self);
              let cond = (#_uLt returning bool)(i, selfLen);
              if cond then {
                let getUncheckedFn =
                  («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::get_unchecked»<T, MaxLen : u32>
                    as λ(${bvTp T MaxLen}, u32) -> T);
                let elem = (getUncheckedFn as λ(${bvTp T MaxLen}, u32) -> T)(self, i);
                let tmp = ${Expr.call Args Out f (mkArgs i elem)};
                ${Expr.modifyLens (tp₁ := bvTp Out MaxLen) (tp₂ := Out) ret tmp
                  ((Lens.nil.cons (Access.tuple Builtin.Member.head)).cons (Access.array i))};
                #_skip
              }
            }
          ])
        fun _ => Expr.skip)
      (fun _ =>
        ∃∃ v : Repr p Out MaxLen,
          [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆ [λf ↦ fb] ⋆ ⟦bounded v ∧ embed v = (embed self).mapIdx fEmb⟧) := by
  set xs : List (T.denote p) := embed self
  set n : Nat := (len self).toNat
  have hn_le : n ≤ MaxLen.toNat := by
    simpa [n, bounded] using hb
  have hx_len : xs.length = n := by
    simpa [xs, n] using embed_length_eq_len_toNat (v := self) hb

  let Inv : Nat → SLP (State p) :=
    fun i =>
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
          [λf ↦ fb] ⋆
            ⟦len v = len self ∧ bounded v ∧
              List.take (Nat.min i n) (storage v).toList = (xs.take (Nat.min i n)).mapIdx fEmb⟧

  apply (STHoare.letIn_intro (Q := fun _ => Inv MaxLen.toNat))
  ·
    loop_inv nat (fun i _ _ => Inv i)
    ·
      dsimp [Inv]
      sl
      constructor
      · simp [len]
      · constructor
        · simpa [bounded, len] using hb
        · simp [Nat.min_zero, Nat.zero_min]
    ·
      rw [SLP.star_comm]
      apply SLP.pure_left
      intro _
      apply SLP.exists_intro_l
      intro _
      exact SLP.ent_star_top (H := Inv MaxLen.toNat)
    ·
      simp [Nat.zero_le MaxLen.toNat]
    ·
      intro i hlo hhi
      have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
      dsimp [Inv] at *
      steps unsafe 1 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst lenFn
      steps unsafe 2 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst_vars
      rename_i v hpure
      rcases hpure with ⟨hlenV, hbV, htakeV⟩

      apply STHoare.ite_intro
      ·
        intro hcond
        have pf32 : i < 2 ^ 32 := by simpa using pf
        have hi_lt : i < n := by
          have : i < (len self).toNat :=
            nat_lt_of_decide_bv_lt_trueLT (i := i) (x := len self) pf32 hcond
          simpa [n] using this
        have hi_xs : i < xs.length := by simpa [hx_len] using hi_lt
        have hmin_i : Nat.min i n = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
        have hmin_succ : Nat.min (i + 1) n = i + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)

        have hiMax : (BitVec.ofNatLT i pf32).toNat < MaxLen.toNat := by
          have htoNat : (BitVec.ofNatLT i pf32).toNat = i :=
            BitVec.toNat_ofNatLT (w := 32) (x := i) (p := pf32)
          rw [htoNat]
          exact hhi
        have hget :=
          get_unchecked_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)
            (index := BitVec.ofNatLT i pf32) (hindex := hiMax)
        steps [hget]

        let i32 : U 32 := BitVec.ofNatLT i pf32
        have hi_toNat : i32.toNat = i := by
          simpa [i32] using (BitVec.toNat_ofNatLT (w := 32) (x := i) (p := pf32))
        let x : T.denote p := (storage self)[i32.toNat]'(by simpa [i32] using hiMax)
        have hi_embed : i < (embed self).length := by simpa [xs, hx_len] using hi_lt
        have hx' : x = xs[i]'hi_xs := by
          have hx0 :
              (storage self)[i32.toNat]'(by simpa [i32] using hiMax) = (embed self)[i]'hi_embed :=
            storage_get_eq_embed_get_of_toNat (self := self) (idxNat := i32.toNat) (i := i)
              hi_toNat (by simpa [i32] using hiMax) hi_embed
          simpa [x, xs] using hx0

        have hi_lambda_elem : i32.toNat < xs.length := by
          simpa [hi_toNat] using hi_xs
        subst getUncheckedFn
        steps [hget]
        rename_i helemEq
        have hlamElem := inv_pure i32 elem hi_lambda_elem
        steps [STHoare.callLambda_intro (hlam := hlamElem)]
        rename_i uUnit
        clear uUnit
        rename_i hmodSome
        rename_i htmpEq

        constructor
        ·
          simpa [len, Lens.modify, Lens.get, Access.modify] using hlenV
        ·
          constructor
          ·
            simpa [bounded, len, Lens.modify, Lens.get, Access.modify] using hbV
          ·
            have helem : elem = x := by
              simpa [x, i32] using helemEq
            have htmp : tmp = fEmb i (xs[i]'hi_xs) := by
              simpa [hi_toNat, helem, hx'] using htmpEq

            simp [hmin_succ, storage, Lens.modify, Lens.get, Access.modify, List.Vector.toList_set, htmp]
            have htake_i :
                List.take i (List.Vector.toList v.1) = (xs.take i).mapIdx fEmb := by
              simpa [storage, hmin_i] using htakeV
            have hstor_len : i < (List.Vector.toList v.1).length := by
              simpa [storage, List.Vector.toList_length] using hhi
            have hstep :
                List.take (i + 1) ((List.Vector.toList v.1).set i (fEmb i (xs[i]'hi_xs))) =
                  (xs.take (i + 1)).mapIdx fEmb :=
              take_succ_set_eq_mapIdx (f := fEmb) (xs := xs) (l := List.Vector.toList v.1)
                (i := i) hi_xs hstor_len htake_i
            have pf' : i < 4294967296 := by
              simpa using pf32
            have hmod : i % 4294967296 = i := Nat.mod_eq_of_lt pf'
            simpa [hmod, hi_toNat, hx'] using hstep
      ·
        intro hcond
        steps
        have pf32 : i < 2 ^ 32 := by simpa using pf
        have hge : n ≤ i := by
          have : (len self).toNat ≤ i :=
            nat_le_of_decide_bv_lt_falseLT (i := i) (x := len self) pf32 hcond
          simpa [n] using this
        have hmin_i : Nat.min i n = n := Nat.min_eq_right hge
        have hmin_succ : Nat.min (i + 1) n = n :=
          Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ _))
        refine ⟨hlenV, hbV, ?_⟩
        simpa [hmin_i, hmin_succ] using htakeV
  ·
    intro _
    let Qfinal : SLP (State p) :=
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆ [λf ↦ fb] ⋆ ⟦bounded v ∧ embed v = xs.mapIdx fEmb⟧

    have hInv_to_Q : Inv MaxLen.toNat ⊢ Qfinal := by
      dsimp [Inv, Qfinal]
      apply SLP.exists_intro_l
      intro v
      apply SLP.exists_intro_r (a := v)
      have hpure :
          (len v = len self ∧ bounded v ∧
              List.take (MaxLen.toNat.min n) (storage v).toList =
                List.mapIdx fEmb (List.take (MaxLen.toNat.min n) xs)) →
            (bounded v ∧ embed v = xs.mapIdx fEmb) := by
        intro hp
        rcases hp with ⟨hlenV, hbV, htakeV⟩
        refine ⟨hbV, ?_⟩
        have hmin : Nat.min MaxLen.toNat n = n := Nat.min_eq_right hn_le
        have htake_xs : xs.take n = xs := by
          apply List.take_of_length_le
          exact Nat.le_of_eq hx_len
        have hlenNat : (len v).toNat = n := by
          simpa [n] using congrArg BitVec.toNat hlenV
        simpa [embed, active, hlenNat, hmin, htake_xs] using htakeV
      refine SLP.star_mono SLP.entails_self ?_
      ·
        refine SLP.star_mono SLP.entails_self ?_
        intro st h
        refine ⟨hpure h.1, h.2⟩
    exact skip_postprocess (p := p) (H := Inv MaxLen.toNat) (Qfinal := Qfinal) hInv_to_Q

theorem map_pure_spec {p T MaxLen Out Env self f fb fEmb}
    (hb : bounded self)
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::map».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => bounded r ∧ embed r = (embed self).map fEmb) := by
  enter_decl
  -- `map` is the index-ignoring special case of `mapIdx`.
  let fIdx : Nat → T.denote p → Out.denote p := fun _ a => fEmb a

  steps [new_spec (p := p) (T := Out) (MaxLen := MaxLen)]
  steps [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)]
  all_goals (try exact ())

  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
          [λf ↦ fb] ⋆
            ⟦bounded v ∧ embed v = (embed self).mapIdx fIdx⟧))
  ·
    apply STHoare.ite_intro_of_false rfl
    steps
    rename_i hmod

    have inv_pure' :
        ∀ (i : U 32) (a : Tp.denote p T),
          (hi : i.toNat < (embed self).length) →
            STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fIdx i.toNat a) := by
      intro _ a _
      simpa [fIdx] using inv_pure a

    simpa [fIdx] using
      (mapLike_constrained_loop_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out)
        (Args := [T]) (mkArgs := fun _ a => h![a])
        (hb := hb) (hmod := hmod) (inv_pure := inv_pure'))
  ·
    intro _
    steps
    subst_vars
    rename_i h
    simpa [fIdx, mapIdx_const_eq_map] using h

theorem mapi_pure_spec {p T MaxLen Out Env self f fb fEmb}
    (hb : bounded self)
    (inv_pure : ∀ (i : U 32) (a : Tp.denote p T),
        (hi : i.toNat < (embed self).length) →
          STHoare p env ⟦⟧ (fb h![i, a]) (fun r => r = fEmb i.toNat a))
  : STHoare p env [λf ↦ fb]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::mapi».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => bounded r ∧ embed r = (embed self).mapIdx fEmb) := by
  enter_decl
  steps [new_spec (p := p) (T := Out) (MaxLen := MaxLen)]
  steps [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)]
  all_goals (try exact ())

  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
          [λf ↦ fb] ⋆
            ⟦bounded v ∧ embed v = (embed self).mapIdx fEmb⟧))
  ·
    apply STHoare.ite_intro_of_false rfl
    steps
    rename_i hmod
    -- Constrained branch: `for i in 0..MaxLen { if i < self.len { ret[i] := f(i, self[i]) } }`.
    simpa using
      (mapLike_constrained_loop_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out)
        (Args := [Tp.u 32, T]) (mkArgs := fun i a => h![i, a])
        (hb := hb) (hmod := hmod) (inv_pure := inv_pure))
  ·
    intro _
    steps
    subst_vars
    assumption

/-!
## Effectful map spec

This is the “no purity assumption” variant. The callback is specified by a per-step Hoare triple
threading an invariant `inv` over:

- `ip`: prefix of the input semantic list `embed self`
- `op`: prefix of the output semantic list `embed out`

The key postcondition is `inv (embed self) (embed out)`.

Note: `inv` must describe only external state effects; it is framed disjointly from the internal
`ret` heaplet used to build the output vector (same assumption as `Stdlib.Slice.map_spec`).
-/
theorem map_effectful_spec {p T MaxLen Out Env self f fb}
    (hb : bounded self)
    (inv : List (T.denote p) → List (Out.denote p) → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (op : List (Out.denote p)) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
          STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env (inv [] [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::map».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => ⟦bounded r⟧ ⋆ inv (embed self) (embed r)) := by
  enter_decl
  set xs : List (T.denote p) := embed self
  set n : Nat := (len self).toNat

  have hn_le : n ≤ MaxLen.toNat := by
    simpa [n, bounded] using hb
  have hx_len : xs.length = n := by
    simpa [xs, n] using embed_length_eq_len_toNat (v := self) hb

  -- `ret := ref (new()); ret.len := self.len(); ...`
  steps [new_spec (p := p) (T := Out) (MaxLen := MaxLen)]
  steps [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)]
  all_goals (try exact ())

  -- Peel the `let _ := (if isUnconstrained {..} else {..}) in readRef ret`.
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
          [λf ↦ fb] ⋆
            ⟦bounded v⟧ ⋆ inv xs (embed v)))
  ·
    -- Reduce the `isUnconstrained()` branch and prove only the constrained branch.
    apply STHoare.ite_intro_of_false rfl
    -- Constrained branch: `for i in 0..MaxLen { if i < self.len { ret[i] := f(self[i]) } }`.
    steps
    let Inv : Nat → SLP (State p) :=
      fun i =>
        ∃∃ v : Repr p Out MaxLen,
          [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
            [λf ↦ fb] ⋆
              inv (xs.take (Nat.min i n)) (List.take (Nat.min i n) (storage v).toList) ⋆
                ⟦len v = len self ∧ bounded v⟧

    apply (STHoare.letIn_intro (Q := fun _ => Inv MaxLen.toNat))
    ·
      loop_inv nat (fun i _ _ => Inv i)
      ·
        -- i = 0: output is empty and we have `inv [] []`.
        dsimp [Inv]
        -- Normalize the `take/min` expressions so `sl` sees `inv [] []` directly.
        simp [Nat.min_zero, Nat.zero_min]
        sl
        constructor
        · simp [len]
        · simpa [bounded, len] using hb
      ·
        rw [SLP.star_comm]
        apply SLP.pure_left
        intro _
        apply SLP.exists_intro_l
        intro _
        exact SLP.ent_star_top (H := Inv MaxLen.toNat)
      ·
        simp [Nat.zero_le MaxLen.toNat]
      ·
        intro i hlo hhi
        have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
        dsimp [Inv] at *
        steps [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)]
        rename_i v hpure
        rcases hpure with ⟨hlenV, hbV⟩

        apply STHoare.ite_intro
        ·
          intro hcond
          have pf32 : i < 2 ^ 32 := by simpa using pf
          have hi_lt : i < n := by
            have : i < (len self).toNat :=
              nat_lt_of_decide_bv_lt_trueLT (i := i) (x := len self) pf32 hcond
            simpa [n] using this
          have hi_xs : i < xs.length := by simpa [hx_len] using hi_lt
          have hmin_i : Nat.min i n = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
          have hmin_succ : Nat.min (i + 1) n = i + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)
          have pf' : i < 4294967296 := by
            -- `2^32 = 4294967296`.
            simpa using pf32
          have hmodNat : i % 4294967296 = i := Nat.mod_eq_of_lt pf'

          -- Reduce `get_unchecked` to a direct read from `storage self`.
          have hiMax : (BitVec.ofNatLT i pf32).toNat < MaxLen.toNat := by
            have htoNat : (BitVec.ofNatLT i pf32).toNat = i :=
              BitVec.toNat_ofNatLT (w := 32) (x := i) (p := pf32)
            rw [htoNat]
            exact hhi
          have hget :=
            get_unchecked_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)
              (index := BitVec.ofNatLT i pf32) (hindex := hiMax)
          steps [hget]

          -- Kill the extracted `% 2^32` index (it comes from `BitVec.toNat`).
          simp [hmodNat]

          -- Normalize `x` to the semantic element `xs[i]`.
          let x : T.denote p := (storage self)[i]'hhi
          have hi_embed : i < (embed self).length := by simpa [xs] using hi_xs
          have hx' : x = xs[i]'hi_xs := by
            have hx0 :
                (storage self)[i]'hhi = (embed self)[i]'hi_embed :=
              storage_get_eq_embed_get_of_toNat (self := self) (idxNat := i) (i := i) rfl hhi hi_embed
            simpa [x, xs] using hx0

          have hprefix : xs.take i ++ [x] <+: xs := by
            simpa [hx'] using (by simp [List.take_prefix])
          have hlam : STHoare p env
              (inv (xs.take i) (List.take i (storage v).toList))
              (fb h![x])
              (fun r => inv (xs.take i ++ [x]) (List.take i (storage v).toList ++ [r])) := by
            have :=
              inv_step (ip := xs.take i) (op := List.take i (storage v).toList) (e := x)
                (by simpa [xs] using hprefix)
            simpa [hmin_i] using this

          -- Help `sl` by normalizing away `min i n = i` and `min (i+1) n = i+1`.
          simp [hmin_i, hmin_succ] at *
          steps [STHoare.callLambda_intro (hlam := hlam)]
          -- Rewrite the `inv` arguments to match the next loop invariant:
          -- `xs.take (i+1)` and the updated output prefix `take (i+1) storage`.
          have htake_xs : xs.take (i + 1) = xs.take i ++ [x] := by
            simpa [hx'] using (List.take_succ_eq_take_append_get (l := xs) (n := i) (hn := hi_xs))
          have hstor_len : i < (storage v).toList.length := by
            -- `storage` has length `MaxLen.toNat`.
            simpa [storage, List.Vector.toList_length] using hhi

          -- `steps` leaves three goals here:
          -- 1) the main entailment `inv ... ⊢ inv ... ⋆ ?R`
          -- 2) a pure goal about `len`/`bounded` for the updated `ret`
          -- 3) an `SLP` goal that fixes `?R`
          --
          -- Since the array-element update does not affect `len`, we can instantiate `?R` with the
          -- pure facts about the *original* `v`; they are definitional equal to the updated ones.
          case R =>
            exact ⟦len v = len self ∧ bounded v⟧
          case h.h₁.a =>
            constructor
            ·
              simpa [len, Lens.modify, Lens.get, Access.modify] using hlenV
            ·
              simpa [bounded, len, Lens.modify, Lens.get, Access.modify] using hbV

          -- Main entailment: rewrite the target `inv` arguments and add the pure facts.
          have hset (a : Out.denote p) :
              List.take (i + 1) ((List.Vector.toList v.1).set i a) =
                List.take i (List.Vector.toList v.1) ++ [a] := by
            have hstor_len' : i < (List.Vector.toList v.1).length := by
              simpa [List.Vector.toList_length] using hhi
            simpa using
              (List.take_succ_set_eq_take_append (l := (List.Vector.toList v.1)) (n := i) (a := a) hstor_len')
          rw [SLP.star_comm]
          refine SLP.pure_right ⟨hlenV, hbV⟩ ?_
          intro st hinv
          simpa [htake_xs, storage, Lens.modify, Lens.get, Access.modify, List.Vector.toList_set, hmodNat, hset] using hinv
        ·
          intro hcond
          -- `i ≥ len self`: no write, and `min` saturates at `n`.
          steps
          have pf32 : i < 2 ^ 32 := by simpa using pf
          have hge : n ≤ i := by
            have : (len self).toNat ≤ i :=
              nat_le_of_decide_bv_lt_falseLT (i := i) (x := len self) pf32 hcond
            simpa [n] using this
          have hmin_i : Nat.min i n = n := Nat.min_eq_right hge
          have hmin_succ : Nat.min (i + 1) n = n :=
            Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ _))
          simp [hmin_i, hmin_succ] at *
          sl
          exact ⟨hlenV, hbV⟩
    ·
      -- Postprocess: convert `Inv MaxLen.toNat` into `inv xs (embed v)`.
      intro _
      let Qfinal : SLP (State p) :=
        ∃∃ v : Repr p Out MaxLen,
          [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆ [λf ↦ fb] ⋆ ⟦bounded v⟧ ⋆ inv xs (embed v)
      have hInv_to_Q : Inv MaxLen.toNat ⊢ Qfinal := by
        dsimp [Inv, Qfinal]
        apply SLP.exists_intro_l
        intro v
        apply SLP.exists_intro_r (a := v)
        refine SLP.star_mono SLP.entails_self ?_
        refine SLP.star_mono SLP.entails_self ?_
        rw [SLP.star_comm]
        apply SLP.pure_left
        intro hpure
        rcases hpure with ⟨hlenV, hbV⟩
        have hmin : Nat.min MaxLen.toNat n = n := Nat.min_eq_right hn_le
        have htake_xs : xs.take n = xs := by
          apply List.take_of_length_le
          exact Nat.le_of_eq hx_len
        have hlenNat : (len v).toNat = n := by
          simpa [n] using congrArg BitVec.toNat hlenV
        have hembed : embed v = List.take n (storage v).toList := by
          simp [embed, active, hlenNat, hmin]
        refine SLP.pure_right hbV ?_
        intro st hinv
        simpa [hmin, htake_xs, hembed] using hinv
      exact skip_postprocess (p := p) (H := Inv MaxLen.toNat) (Qfinal := Qfinal) hInv_to_Q
  ·
    intro _
    steps
    subst_vars
    -- The extracted return value and its boundedness proof get fresh names.
    rename_i r hbR
    sl
    ·
      -- The boundedness proof is for a definitional-equal value; rename and rewrite.
      rename_i hEq r' hb
      simpa [hb] using hEq

end Lampe.Stdlib.Collections.BoundedVec
