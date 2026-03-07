import Stdlib.Collections.BoundedVec.Methods

namespace Lampe.Stdlib.Collections.BoundedVec

open «std-1.0.0-beta.12»

/-!
Higher-order method specs for Noir `BoundedVec`: `map` and `mapi` (pure variants).

This module is imported by `Stdlib.Collections.BoundedVec` as part of the public API surface.
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
    len (p := p) (T := T) (MaxLen := MaxLen)
        (((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify v l).get h) = l := by
  unfold len
  simp [Lens.modify]

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
  simpa [SLP.star_assoc] using (show (⟦v = ()⟧ ⋆ (H ⋆ ⊤) ⊢ Qfinal ⋆ ⊤) from by
    apply SLP.pure_left
    intro _
    exact SLP.star_mono_r hHQ)

/-!
Shared constrained-branch loop proof for effectful `map`/`mapi`-like methods.

This is the “no purity assumption” variant: instead of relating the callback to a Lean function
`fEmb`, we only assume a step Hoare triple `inv_step` threading an invariant `inv` over the input
and output semantic prefixes.
-/

private theorem mapLike_constrained_loop_effectful_spec
    {p : Prime}
    {T : Tp} {MaxLen : U 32} {Out : Tp}
    {Args : List Tp}
    {self : Repr p T MaxLen}
    {f : FuncRef Args Out}
    {fb : HList (Tp.denote p) Args → Expr (Tp.denote p) Out}
    {mkArgs : U 32 → Tp.denote p T → HList (Tp.denote p) Args}
    {ret : Ref}
    {vnew : Tp.denote p (bvTp Out MaxLen)}
    (hb : bounded self)
    (hmod :
      ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify vnew (len self)).isSome = true)
    (inv : List (T.denote p) → List (Out.denote p) → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (op : List (Out.denote p)) (i : U 32) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
        i.toNat = ip.length →
          STHoare p env (inv ip op) (fb (mkArgs i e)) (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env
      ([ret ↦ ⟨bvTp Out MaxLen,
        ((Lens.nil.cons (Access.tuple Builtin.Member.head.tail)).modify vnew (len self)).get hmod⟩] ⋆
        [λf ↦ fb] ⋆ inv [] [])
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
          [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆ [λf ↦ fb] ⋆ ⟦bounded v⟧ ⋆ inv (embed self) (embed v)) := by
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
            inv (xs.take (Nat.min i n)) (List.take (Nat.min i n) (storage v).toList) ⋆
              ⟦len v = len self ∧ bounded v⟧

  apply (STHoare.letIn_intro (Q := fun _ => Inv MaxLen.toNat))
  ·
    loop_inv nat (fun i _ _ => Inv i)
    ·
      -- i = 0
      dsimp [Inv]
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
      -- Peel the loop body's `let`-bindings, then split on the `if i < self.len`.
      steps unsafe 1 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst lenFn
      steps unsafe 2 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst_vars
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

        -- Read `self[i]` via `get_unchecked`.
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

        -- Normalize `x` to the semantic element `xs[i]`.
        let x : T.denote p := (storage self)[i32.toNat]'(by simpa [i32] using hiMax)
        have hi_embed : i < (embed self).length := by simpa [xs, hx_len] using hi_lt
        have hx' : x = xs[i]'hi_xs := by
          have hx0 :
              (storage self)[i32.toNat]'(by simpa [i32] using hiMax) = (embed self)[i]'hi_embed :=
            storage_get_eq_embed_get_of_toNat (self := self) (idxNat := i32.toNat) (i := i)
              hi_toNat (by simpa [i32] using hiMax) hi_embed
          simpa [x, xs] using hx0

        -- Now step into `let elem = get_unchecked(self, i)`.
        subst getUncheckedFn
        steps [hget]
        rename_i helemEq

        have helem : elem = x := by
          simpa [x, i32] using helemEq
        have helem_xs : elem = xs[i]'hi_xs := by
          simpa [helem] using hx'

        -- Instantiate the callback spec on this step.
        have hip_len : (xs.take i).length = i := by
          have hi_le : i ≤ xs.length := Nat.le_of_lt hi_xs
          simpa [List.length_take, Nat.min_eq_left hi_le]
        let idx : U 32 := BitVec.ofNat 32 i
        have hidx_toNat : idx.toNat = i := by
          simpa [idx] using toNat_ofNat32 (i := i) pf32
        have hprefix : xs.take i ++ [elem] <+: xs := by
          simpa [helem_xs] using (by simp [List.take_prefix])

        have hlam : STHoare p env
            (inv (xs.take i) (List.take i (storage v).toList))
            (fb (mkArgs idx elem))
            (fun r => inv (xs.take i ++ [elem]) (List.take i (storage v).toList ++ [r])) := by
          have :=
            inv_step (ip := xs.take i) (op := List.take i (storage v).toList) (i := idx) (e := elem)
              (by simpa [xs] using hprefix) (by simpa [hidx_toNat, hip_len])
          simpa [hmin_i] using this

        -- Help `sl` by normalizing the `min` expressions.
        simp [hmin_i, hmin_succ] at *
        steps [STHoare.callLambda_intro (hlam := hlam)]

        have htake_xs : xs.take (i + 1) = xs.take i ++ [elem] := by
          -- `take (i+1) xs = take i xs ++ [xs[i]]`.
          have := List.take_succ_eq_take_append_get (l := xs) (n := i) (hn := hi_xs)
          simpa [helem_xs] using this
        have hstor_len : i < (storage v).toList.length := by
          simpa [storage, List.Vector.toList_length] using hhi

        have hset (a : Out.denote p) :
            List.take (i + 1) ((List.Vector.toList v.1).set i a) =
              List.take i (List.Vector.toList v.1) ++ [a] := by
          have hstor_len' : i < (List.Vector.toList v.1).length := by
            simpa [List.Vector.toList_length] using hhi
          simpa using
            (List.take_succ_set_eq_take_append (l := (List.Vector.toList v.1)) (n := i) (a := a) hstor_len')

        -- Discharge the final entailment to establish `Inv (i+1)` from the `inv_step` result and
        -- the storage update.
        case R =>
          exact ⟦len v = len self ∧ bounded v⟧
        case h.h₁.a =>
          constructor
          · simpa [len] using hlenV
          · simpa [bounded, len] using hbV
        rw [SLP.star_comm]
        refine SLP.pure_right ⟨hlenV, hbV⟩ ?_
        intro st hinv
        -- `BitVec.toNat` introduces `% 2^32`; rewrite it away since `i < 2^32`.
        have pf' : i < 4294967296 := by simpa using pf32
        have hmod : i % 4294967296 = i := Nat.mod_eq_of_lt pf'
        simpa [htake_xs, storage, hmod, hset] using hinv
      ·
        intro hcond
        -- i ≥ len self: no write, and `min` saturates at `n`.
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
    -- Postprocess `Inv MaxLen.toNat` into the desired `inv xs (embed v)`.
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
        simp [embed, active, hlenNat]
      refine SLP.pure_right hbV ?_
      intro st hinv
      simpa [hmin, htake_xs, hembed] using hinv
    exact skip_postprocess (p := p) (H := Inv MaxLen.toNat) (Qfinal := Qfinal) hInv_to_Q

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
    (hwf_self : wellFormed self)
    (inv : List (T.denote p) → List (Out.denote p) → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (op : List (Out.denote p)) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
          STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env (inv [] [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::map».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => ⟦wellFormed r⟧ ⋆ inv (embed self) (embed r)) := by
  enter_decl
  have hb : bounded self := (bounded_iff_wellFormed (v := self)).2 hwf_self
  set xs : List (T.denote p) := embed self

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
    apply STHoare.ite_intro_of_false rfl
    steps
    rename_i hmod

    have inv_step' :
        ∀ (ip : List (T.denote p)) (op : List (Out.denote p)) (i : U 32) (e : T.denote p),
          (ip ++ [e] <+: embed self) →
          i.toNat = ip.length →
            STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ++ [r])) := by
      intro ip op _ e hprefix _
      exact inv_step (ip := ip) (op := op) (e := e) hprefix

    simpa [xs] using
      (mapLike_constrained_loop_effectful_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out)
        (Args := [T]) (mkArgs := fun _ a => h![a])
        (self := self) (f := f) (fb := fb) (ret := ret)
        (hb := hb) (hmod := hmod) (inv := inv) (inv_step := inv_step'))
  ·
    intro _
    steps_named as [r, hbR]
    sl
    ·
      rename_i hEq r' hb
      have hwf : wellFormed _ := (bounded_iff_wellFormed (v := _)).1 hEq
      simpa [hb] using hwf

theorem mapi_effectful_spec {p T MaxLen Out Env self f fb}
    (hwf_self : wellFormed self)
    (inv : List (T.denote p) → List (Out.denote p) → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (op : List (Out.denote p)) (i : U 32) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
        i.toNat = ip.length →
          STHoare p env (inv ip op) (fb h![i, e]) (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env (inv [] [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::mapi».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => ⟦wellFormed r⟧ ⋆ inv (embed self) (embed r)) := by
  enter_decl
  have hb : bounded self := (bounded_iff_wellFormed (v := self)).2 hwf_self
  set xs : List (T.denote p) := embed self

  -- `ret := ref (new()); ret.len := self.len(); ...`
  steps [new_spec (p := p) (T := Out) (MaxLen := MaxLen)]
  steps [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)]
  all_goals (try exact ())

  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ v : Repr p Out MaxLen,
        [ret ↦ ⟨bvTp Out MaxLen, v⟩] ⋆
          [λf ↦ fb] ⋆
            ⟦bounded v⟧ ⋆ inv xs (embed v)))
  ·
    apply STHoare.ite_intro_of_false rfl
    steps
    rename_i hmod

    simpa [xs] using
      (mapLike_constrained_loop_effectful_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out)
        (Args := [Tp.u 32, T]) (mkArgs := fun i a => h![i, a])
        (self := self) (f := f) (fb := fb) (ret := ret)
        (hb := hb) (hmod := hmod) (inv := inv) (inv_step := inv_step))
  ·
    intro _
    steps_named as [r, hbR]
    sl
    ·
      rename_i hEq r' hb
      have hwf : wellFormed _ := (bounded_iff_wellFormed (v := _)).1 hEq
      simpa [hb] using hwf

-- Helper entailment: `[λf ↦ fb] ⊢ ⟦P⟧ ⋆ [λf ↦ fb]` when `P` holds.
-- Used by `map_pure_spec` and `mapi_pure_spec` to bridge from the pure precondition
-- `[λf ↦ fb]` to the effectful precondition `⟦[] = ...⟧ ⋆ [λf ↦ fb]`.
private lemma lambda_entails_lift_star_left
    {p : Prime} {Args : List Tp} {Out : Tp}
    {f : FuncRef Args Out}
    {fb : HList (Tp.denote p) Args → Expr (Tp.denote p) Out}
    {P : Prop} (hP : P) :
    ([λf ↦ fb] : SLP (State p)) ⊢ ⟦P⟧ ⋆ [λf ↦ fb] :=
  SLP.pure_right hP SLP.entails_self

theorem map_pure_spec {p T MaxLen Out Env self f fb fEmb}
    (hwf_self : wellFormed self)
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::map».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => wellFormed r ∧ embed r = (embed self).map fEmb) := by
  -- Corollary of `map_effectful_spec` with the pure invariant `inv ip op := ⟦op = ip.map fEmb⟧`.
  refine STHoare.consequence
      (H₁ := ⟦([] : List (Out.denote p)) = ([] : List (T.denote p)).map fEmb⟧ ⋆ [λf ↦ fb])
      (Q₁ := fun r => ⟦wellFormed r⟧ ⋆ ⟦embed r = (embed self).map fEmb⟧)
      ?_ ?_ ?_
  · -- Pre: `[λf ↦ fb] ⊢ ⟦[] = [].map fEmb⟧ ⋆ [λf ↦ fb]`.
    exact lambda_entails_lift_star_left (by simp)
  · -- Post: `(⟦wellFormed r⟧ ⋆ ⟦embed r = ...⟧) ⋆ ⊤ ⊢ ⟦wellFormed r ∧ embed r = ...⟧ ⋆ ⊤`.
    intro r
    simp only [SLP.lift_star_lift]
    exact SLP.entails_self
  · refine map_effectful_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out) (Env := Env)
        (self := self) (f := f) (fb := fb) hwf_self
        (inv := fun ip op => ⟦op = ip.map fEmb⟧)
        (inv_step := ?_)
    intro ip op e _
    -- Frame `⟦op = ip.map fEmb⟧` through `inv_pure e`, then close with pure reasoning.
    have hspec : STHoare p env ⟦⟧ (fb h![e]) (fun r => r = fEmb e) := by simpa using inv_pure e
    refine STHoare.consequence
        (H₁ := ⟦⟧ ⋆ ⟦op = ip.map fEmb⟧)
        (Q₁ := fun r => (r = fEmb e) ⋆ ⟦op = ip.map fEmb⟧)
        (by simp only [SLP.true_star]; exact SLP.entails_self) ?_
        (STHoare.frame (h_hoare := hspec))
    intro r
    simp only [SLP.lift_star_lift, SLP.star_assoc]
    apply SLP.pure_left
    intro ⟨hr, hop⟩
    exact SLP.pure_right (by simp [hr, hop]) SLP.entails_top

theorem mapi_pure_spec {p T MaxLen Out Env self f fb fEmb}
    (hwf_self : wellFormed self)
    (inv_pure : ∀ (i : U 32) (a : Tp.denote p T),
        (hi : i.toNat < (embed self).length) →
          STHoare p env ⟦⟧ (fb h![i, a]) (fun r => r = fEmb i.toNat a))
  : STHoare p env [λf ↦ fb]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::mapi».call h![T, MaxLen, Out, Env]
        h![self, f])
      (fun r => wellFormed r ∧ embed r = (embed self).mapIdx fEmb) := by
  -- Corollary of `mapi_effectful_spec` with the pure invariant `inv ip op := ⟦op = ip.mapIdx fEmb⟧`.
  refine STHoare.consequence
      (H₁ := ⟦([] : List (Out.denote p)) = ([] : List (T.denote p)).mapIdx fEmb⟧ ⋆ [λf ↦ fb])
      (Q₁ := fun r => ⟦wellFormed r⟧ ⋆ ⟦embed r = (embed self).mapIdx fEmb⟧)
      ?_ ?_ ?_
  · -- Pre: `[λf ↦ fb] ⊢ ⟦[] = [].mapIdx fEmb⟧ ⋆ [λf ↦ fb]`.
    exact lambda_entails_lift_star_left (by simp)
  · -- Post: `(⟦wellFormed r⟧ ⋆ ⟦embed r = ...⟧) ⋆ ⊤ ⊢ ⟦wellFormed r ∧ embed r = ...⟧ ⋆ ⊤`.
    intro r
    simp only [SLP.lift_star_lift]
    exact SLP.entails_self
  · refine mapi_effectful_spec (p := p) (T := T) (MaxLen := MaxLen) (Out := Out) (Env := Env)
        (self := self) (f := f) (fb := fb) hwf_self
        (inv := fun ip op => ⟦op = ip.mapIdx fEmb⟧)
        (inv_step := ?_)
    intro ip op i e hprefix hip_len
    -- `ip ++ [e] <+: embed self` implies `ip.length < (embed self).length`.
    have hi_lt : ip.length < (embed self).length := by
      have h := List.IsPrefix.length_le hprefix
      simp [List.length_append] at h
      omega
    -- Frame `⟦op = ip.mapIdx fEmb⟧` through `inv_pure i e`, then close with pure reasoning.
    have hspec : STHoare p env ⟦⟧ (fb h![i, e]) (fun r => r = fEmb i.toNat e) := by
      simpa using inv_pure i e (hip_len ▸ hi_lt)
    refine STHoare.consequence
        (H₁ := ⟦⟧ ⋆ ⟦op = ip.mapIdx fEmb⟧)
        (Q₁ := fun r => (r = fEmb i.toNat e) ⋆ ⟦op = ip.mapIdx fEmb⟧)
        (by simp only [SLP.true_star]; exact SLP.entails_self) ?_
        (STHoare.frame (h_hoare := hspec))
    intro r
    simp only [SLP.lift_star_lift, SLP.star_assoc]
    apply SLP.pure_left
    intro ⟨hr, hop⟩
    apply SLP.pure_right _ SLP.entails_top
    -- `op ++ [r] = (ip ++ [e]).mapIdx fEmb`, given `r = fEmb i.toNat e`,
    -- `op = ip.mapIdx fEmb`, and `i.toNat = ip.length`.
    simp [← hip_len, hr, hop]

theorem any_spec {p T MaxLen Env self f fb}
    (hwf_self : wellFormed self)
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (op : Bool) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
          STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ∨ r)))
  : STHoare p env
      (inv [] false ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::any».call h![T, MaxLen, Env]
        h![self, f])
      (fun r => inv (embed self) r ⋆ [λf ↦ fb]) := by
  enter_decl
  have hb : bounded self := (bounded_iff_wellFormed (v := self)).2 hwf_self
  set xs : List (T.denote p) := embed self
  set n : Nat := (len self).toNat
  have hn_le : n ≤ MaxLen.toNat := by
    simpa [n, bounded] using hb
  have hx_len : xs.length = n := by
    simpa [xs, n] using embed_length_eq_len_toNat (v := self) hb

  -- After initializing `ret`, the extracted function evaluates a `false` guard and executes only the
  -- constrained branch. Peel the `let _ := (if ...) in readRef ret`.
  steps
  all_goals (try exact ())
  apply (STHoare.letIn_intro
    (Q := fun _ =>
      ∃∃ b : Bool, [ret ↦ ⟨.bool, b⟩] ⋆ inv xs b ⋆ [λf ↦ fb]))
  ·
    -- Constrained branch (`Expr.ite false ...`).
    apply STHoare.ite_intro_of_false rfl
    -- Initialize `exceeded_len` and enter the loop.
    steps
    step_as
        ([ret ↦ ⟨.bool, false⟩] ⋆ [exceeded_len ↦ ⟨.bool, false⟩] ⋆ inv [] false ⋆ [λf ↦ fb])
        (fun _ => ∃∃ b : Bool, [ret ↦ ⟨.bool, b⟩] ⋆ inv xs b ⋆ [λf ↦ fb])
    steps
    loop_inv nat
      (fun i _ _ =>
        ∃∃ b : Bool,
          [ret ↦ ⟨.bool, b⟩] ⋆
          [exceeded_len ↦ ⟨.bool, decide (n < i)⟩] ⋆
          inv (xs.take (Nat.min i n)) b ⋆
          [λf ↦ fb])
    ·
      -- i = 0
      sl
      simp
      -- `loop_inv` may introduce a trailing frame; absorb it into `⊤`.
      apply SLP.ent_star_top
    ·
      -- Postcondition weakening: rewrite `take (min MaxLen n)` to `xs`, and absorb `exceeded_len` into `⊤`.
      have hmin : Nat.min MaxLen.toNat n = n := Nat.min_eq_right hn_le
      have htake_xs : xs.take n = xs := by
        apply List.take_of_length_le
        exact Nat.le_of_eq hx_len
      simp [hmin, htake_xs]
      sl
    ·
      simpa using (Nat.zero_le MaxLen.toNat)
    ·
      intro i hlo hhi
      steps
      all_goals (try exact ())
      simp_all only [BitVec.toNat_ofNatLT, Nat.reducePow, Bool.decide_or, Bool.decide_eq_true,
        Bool.decide_eq_false, Bool.false_or, Bool.true_or]

      have pf32 : i < 2 ^ 32 := by
        simpa using (lt_two_pow_of_lt_maxLen (i := i) (MaxLen := MaxLen) hhi)
      have hEq_dec :
          decide (BitVec.ofNat 32 i = len self) = decide (i = (len self).toNat) := by
        simpa using (decide_ofNat_eq_toNat (i := i) (x := len self) pf32)

      have hexceeded_next :
          (decide (n < i) || decide (BitVec.ofNat 32 i = len self)) = decide (n < i + 1) := by
        simp [hEq_dec, n, Nat.lt_succ_iff, Nat.le_iff_lt_or_eq, eq_comm]

      -- `steps` sometimes leaves a meta `R : SLP (State p)` for the frame. It is safe to instantiate
      -- it with `⊤` here (the loop invariant already carries all relevant resources).
      all_goals (try exact (⊤ : SLP (State p)))

      -- Split on the guard `!exceeded_len` after the update.
      apply STHoare.ite_intro
      ·
        intro hcond
        have hor : (decide (n < i) || decide (BitVec.ofNat 32 i = len self)) = false := by
          -- `!exceeded_len` is true, so `exceeded_len` is false after the update.
          simpa [Lens.modify, len] using hcond
        have hnot : decide (n < i + 1) = false := by
          simpa [hexceeded_next] using hor
        have hle_succ : i + 1 ≤ n := by
          have : ¬ n < i + 1 := of_decide_eq_false hnot
          -- `¬ (n < i+1)` is `i+1 ≤ n`.
          exact Nat.le_of_not_gt this
        have hi_lt : i < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hle_succ
        have hi_xs : i < xs.length := by simpa [hx_len] using hi_lt
        have hmin_i : Nat.min i n = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
        have hmin_succ : Nat.min (i + 1) n = i + 1 :=
          Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)

        -- Call the predicate on `xs[i]`.
        steps
        simp [hmin_i, hmin_succ]
        -- `steps` should normalize the array read to `xs[i]` after rewriting `embed = take len storage`.
        simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
          zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
          BitVec.toNat_ofNatLT, List.get_eq_getElem]
        generalize_proofs
        rename Tp.denote p .bool => b
        rename_i hiIdx
        have hi_xs : i < xs.length := by simpa [hx_len] using hi_lt
        let e : T.denote p := xs[i]'hi_xs
        have hi_embed : i < (embed self).length := by
          simpa [xs] using hi_xs
        have htoNat : i % 4294967296 = i := by
          have hi_lt' : i < 4294967296 := by
            simpa using pf32
          simpa using (Nat.mod_eq_of_lt hi_lt')
        have harg : List.Vector.get self.1 ⟨i % 4294967296, hiIdx⟩ = e := by
          have h :=
            storage_get_eq_embed_get_of_toNat (self := self) (idxNat := i % 4294967296) (i := i) htoNat hiIdx hi_embed
          -- Rewrite `storage`/`embed` projections and discharge proof-irrelevance in the indexing proof.
          simpa using h
        have hprefix : xs.take i ++ [e] <+: xs := by
          have he : e = xs[i]'hi_xs := by
            simp [e]
          have htake : xs.take i ++ [xs[i]'hi_xs] = xs.take (i + 1) := by
            simpa using (List.take_append_getElem (l := xs) (i := i) hi_xs)
          have htake' : xs.take i ++ [e] = xs.take (i + 1) := by
            simpa [he] using htake
          simpa [htake'] using (List.take_prefix (i := i + 1) (l := xs))
        have hlam : STHoare p env
            (inv (xs.take i) b)
            (fb h![e])
            (fun r => inv (xs.take i ++ [e]) (b ∨ r)) := by
          have :=
            inv_step (ip := xs.take i) (op := b) (e := e) (by simpa [xs] using hprefix)
          simpa [hmin_i] using this
        -- Rewrite the argument read from storage into our semantic element `e` so `callLambda_intro` matches.
        simp [harg]
        steps [STHoare.callLambda_intro (hlam := hlam)]
        simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.false_or, Bool.true_or,
          List.take_append_getElem, Lens.modify, Option.get_some]
        sl
        ·
          -- Normalize `take i ++ [xs[i]]` to `take (i+1)` to discharge the remaining frame goal.
          have htake : xs.take i ++ [e] = xs.take (i + 1) := by
            simpa [e] using (List.take_append_getElem (l := xs) (i := i) hi_xs)
          simp [htake]
          exact SLP.ent_star_top
        ·
          -- Side condition about the updated `exceeded_len`.
          -- (`!exceeded_len = true` implies the update computed `false`.)
          have horFalse : (decide (n < i) || decide (BitVec.ofNat 32 i = len self)) = false := by
            simpa [len] using hcond
          have horFalse' : (decide (n < i) || decide (BitVec.ofNat 32 i = self.2.1)) = false := by
            simpa [len] using horFalse
          simp [horFalse']
        ·
          exact ()
      ·
        intro hcond
        -- `!exceeded_len = false` means the updated `exceeded_len` is true, i.e. `i ≥ n`.
        have himp : i ≤ n → BitVec.ofNat 32 i = len self := by
          simpa [Lens.modify, len] using hcond
        have hge : n ≤ i := by
          apply Nat.le_of_not_gt
          intro hi_lt
          have hbv : BitVec.ofNat 32 i = len self := himp (Nat.le_of_lt hi_lt)
          have htoNat : (BitVec.ofNat 32 i).toNat = (len self).toNat := congrArg BitVec.toNat hbv
          have hi_lt' : i < 4294967296 := by
            simpa using pf32
          have htoNat_ofNat : (BitVec.ofNat 32 i).toNat = i := by
            simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi_lt']
          have hi_eq : i = n := by
            have : i = (len self).toNat := by
              simpa [htoNat_ofNat] using htoNat
            simpa [n] using this
          exact Nat.ne_of_lt hi_lt hi_eq
        have hmin_i : Nat.min i n = n := Nat.min_eq_right hge
        have hmin_succ : Nat.min (i + 1) n = n :=
          Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ _))
        steps
        simp [hmin_i, hmin_succ] at *
        sl
        ·
          -- Side condition generated by `steps`/`subst_vars` about the updated `exceeded_len`.
          have h :
              (decide (n < i) || decide (BitVec.ofNat 32 i = self.2.1)) = decide (n < i + 1) := by
            simpa [len] using hexceeded_next
          simp [len, h]
    ·
      -- Loop finished.
      have hmin : Nat.min MaxLen.toNat n = n := Nat.min_eq_right hn_le
      have htake_xs : xs.take n = xs := by
        apply List.take_of_length_le
        exact Nat.le_of_eq hx_len
      simp [hmin, htake_xs] at *
      steps
  ·
    -- `readRef ret` returns the final boolean.
    intro _
    steps_named
    sl

theorem any_pure_spec {p T MaxLen Env self f fb fEmb}
    (hwf_self : wellFormed self)
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::any».call h![T, MaxLen, Env]
        h![self, f])
      (fun r => r = (embed self).any fEmb) := by
  -- Specialize `any_spec` with a pure invariant `op = ip.any fEmb`.
  refine STHoare.consequence
      (H₁ := (⟦false = ([] : List (T.denote p)).any fEmb⟧ ⋆ [λf ↦ fb]))
      (Q₁ := fun r => (⟦r = (embed self).any fEmb⟧ ⋆ [λf ↦ fb]))
      ?_ ?_ ?_
  ·
    -- Initial invariant holds since `[].any fEmb = false`.
    have hp : false = ([] : List (T.denote p)).any fEmb := by simp
    exact SLP.pure_right (P := false = ([] : List (T.denote p)).any fEmb) hp SLP.entails_self
  ·
    intro r
    -- Drop the framed lambda predicate (it can be absorbed by `⊤`).
    -- `(⟦P⟧ ⋆ R) ⋆ ⊤ ⊢ ⟦P⟧ ⋆ ⊤` since `R ⊢ ⊤`.
    have hdrop : ([λf ↦ fb] ⋆ (⊤ : SLP (State p))) ⊢ (⊤ : SLP (State p)) := SLP.entails_top
    have h :=
      SLP.star_mono (H₁ := (⟦r = (embed self).any fEmb⟧ : SLP (State p)))
        (H₂ := (⟦r = (embed self).any fEmb⟧ : SLP (State p)))
        (Q₁ := ([λf ↦ fb] ⋆ (⊤ : SLP (State p))))
        (Q₂ := (⊤ : SLP (State p)))
        SLP.entails_self hdrop
    -- Normalize associativity.
    simpa [SLP.star_assoc] using h
  ·
    exact any_spec (p := p) (T := T) (MaxLen := MaxLen) (Env := Env) (self := self) (f := f) (fb := fb)
      (hwf_self := hwf_self)
      (inv := fun ip op => ⟦op = ip.any fEmb⟧)
      (inv_step := by
        intro ip op e pfx
        steps [inv_pure (a := e)]
        simp_all only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.decide_or,
          Bool.decide_eq_true, Bool.forall_bool, Bool.false_or, Bool.true_or])

/-!
Shared constrained-branch loop proof for effectful `for_each`/`for_eachi`-like methods.

The two methods differ only in the callback argument construction:
- `for_each`:  `f(elem)`      i.e. `Args = [T]`,       `mkArgs = fun _ a => h![a]`
- `for_eachi`: `f(i, elem)`   i.e. `Args = [u32, T]`,  `mkArgs = fun i a => h![i, a]`
-/
private theorem forEachLike_constrained_loop_spec
    {p : Prime}
    {T : Tp} {MaxLen : U 32}
    {Args : List Tp}
    {self : Repr p T MaxLen}
    {f : FuncRef Args Tp.unit}
    {fb : HList (Tp.denote p) Args → Expr (Tp.denote p) Tp.unit}
    {mkArgs : U 32 → Tp.denote p T → HList (Tp.denote p) Args}
    (hb : bounded self)
    (Inv : List (T.denote p) → SLP (State p))
    (inv_step :
      ∀ (ip : List (T.denote p)) (i : U 32) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
        i.toNat = ip.length →
          STHoare p env (Inv ip) (fb (mkArgs i e)) (fun _ => Inv (ip ++ [e])))
  : STHoare p env
      (Inv [] ⋆ [λf ↦ fb])
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
                ${Expr.call Args Tp.unit f (mkArgs i elem)};
                #_skip
              }
            }
          ])
        fun _ => Expr.skip)
      (fun _ => Inv (embed self) ⋆ [λf ↦ fb]) := by
  set xs : List (T.denote p) := embed self
  set n : Nat := (len self).toNat
  have hn_le : n ≤ MaxLen.toNat := by
    simpa [n, bounded] using hb
  have hx_len : xs.length = n := by
    simpa [xs, n] using embed_length_eq_len_toNat (v := self) hb
  -- Peel `let _ := (for i in 0..MaxLen { ... }) in skip`.
  apply (STHoare.letIn_intro (Q := fun _ => Inv xs ⋆ [λf ↦ fb]))
  ·
    loop_inv nat (fun i _ _ => Inv (xs.take (Nat.min i n)) ⋆ [λf ↦ fb])
    ·
      -- i = 0
      simp [Nat.min_zero, Nat.zero_min]
      sl
    ·
      -- postcondition weakening for `loop_inv` boilerplate
      rw [SLP.star_comm]
      apply SLP.pure_left
      intro _
      apply SLP.exists_intro_l
      intro _
      have hmin : Nat.min MaxLen.toNat n = n := Nat.min_eq_right hn_le
      have htake_xs : xs.take n = xs := by
        apply List.take_of_length_le
        exact Nat.le_of_eq hx_len
      simpa [hmin, htake_xs] using (SLP.ent_star_top (H := Inv (embed self) ⋆ [λf ↦ fb]))
    ·
      simp [Nat.zero_le MaxLen.toNat]
    ·
      intro i hlo hhi
      have pf : i < 2 ^ 32 := lt_two_pow_of_lt_maxLen (MaxLen := MaxLen) hhi
      -- The loop body checks `i < self.len()`.
      steps unsafe 1 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst lenFn
      steps unsafe 2 [len_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)] +strict
      subst_vars
      apply STHoare.ite_intro
      ·
        intro hcond
        have pf32 : i < 2 ^ 32 := by simpa using pf
        have hi_lt : i < n := by
          have : i < (len self).toNat :=
            nat_lt_of_decide_bv_lt_trueLT (i := i) (x := len self) pf32 hcond
          simpa [n] using this
        have hi_xs : i < xs.length := by
          simpa [hx_len] using hi_lt
        have hi_embed : i < (embed self).length := by
          simpa [xs] using hi_xs
        -- Reduce `get_unchecked` to a direct read from `storage self`.
        have hiMax : (BitVec.ofNatLT i pf32).toNat < MaxLen.toNat := by
          have pf' : i < 4294967296 := by simpa using pf32
          have hmodNat : i % 4294967296 = i := Nat.mod_eq_of_lt pf'
          simpa [BitVec.toNat_ofNatLT, hmodNat] using hhi
        have hget :=
          get_unchecked_concrete_spec' (p := p) (T := T) (MaxLen := MaxLen) (self := self)
            (index := BitVec.ofNatLT i pf32) (hindex := hiMax)
        steps [hget]
        -- Now step into `let elem = get_unchecked(self, i)`.
        subst getUncheckedFn
        steps [hget]
        rename_i helemEq
        have pf' : i < 4294967296 := by simpa using pf32
        have hmodNat : i % 4294967296 = i := Nat.mod_eq_of_lt pf'

        -- Normalize `elem` to the semantic element `xs[i]`.
        let x : T.denote p := (storage self)[i]'hhi
        have hx' : x = xs[i]'hi_xs := by
          have hx0 :
              (storage self)[i]'hhi = (embed self)[i]'hi_embed :=
            storage_get_eq_embed_get_of_toNat (self := self) (idxNat := i) (i := i) rfl hhi hi_embed
          simpa [x, xs] using hx0
        have helem : elem = x := by
          simpa [x, hmodNat] using helemEq
        subst helem
        simp [hmodNat]

        have hprefix : xs.take i ++ [x] <+: xs := by
          simpa [hx'] using (by simp [List.take_prefix])
        -- Instantiate the callback spec on this step.
        have hip_len : (xs.take i).length = i := by
          have hi_le : i ≤ xs.length := Nat.le_of_lt hi_xs
          simpa [List.length_take, Nat.min_eq_left hi_le]
        let idx : U 32 := BitVec.ofNat 32 i
        have hidx_toNat : idx.toNat = i := by
          simpa [idx] using toNat_ofNat32 (i := i) pf32
        have hlam : STHoare p env (Inv (xs.take i)) (fb (mkArgs idx x)) (fun _ => Inv (xs.take i ++ [x])) := by
          have :=
            inv_step (ip := xs.take i) (i := idx) (e := x)
              (by simpa [xs] using hprefix) (by simpa [hidx_toNat, hip_len])
          simp [this]
        -- Help `sl`: rewrite `min` and `take` around the processed prefix.
        have hmin_i : Nat.min i n = i := Nat.min_eq_left (Nat.le_of_lt hi_lt)
        have hmin_succ : Nat.min (i + 1) n = i + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hi_lt)
        simp [hmin_i, hmin_succ] at *
        have htake_xs : xs.take (i + 1) = xs.take i ++ [x] := by
          simpa [hx'] using (List.take_succ_eq_take_append_get (l := xs) (n := i) (hn := hi_xs))
        steps [STHoare.callLambda_intro (hlam := hlam)]
        case R => exact ⟦True⟧
        simp [htake_xs]
        simpa [SLP.star_comm] using
          SLP.pure_right (H₁ := Inv (xs.take i ++ [x])) (H₂ := Inv (xs.take i ++ [x])) (P := True)
            trivial SLP.entails_self
      ·
        intro hcond
        -- i >= self.len(): do nothing.
        have pf32 : i < 2 ^ 32 := by simpa using pf
        have hge : n ≤ i := by
          have : (len self).toNat ≤ i :=
            nat_le_of_decide_bv_lt_falseLT (i := i) (x := len self) pf32 hcond
          simpa [n] using this
        have hmin_i : Nat.min i n = n := Nat.min_eq_right hge
        have hmin_succ : Nat.min (i + 1) n = n :=
          Nat.min_eq_right (Nat.le_trans hge (Nat.le_succ _))
        simp [hmin_i, hmin_succ] at *
        steps
  ·
    intro _
    steps

theorem for_each_spec {T Env p MaxLen self f fb}
    (hwf_self : wellFormed self)
    (Inv : List (Tp.denote p T) → SLP (State p))
    (h_inv :
      ∀ (lp : List (Tp.denote p T)) (e : T.denote p),
        (lp ++ [e] <+: embed self) →
          STHoare p env (Inv lp) (fb h![e]) (fun _ => Inv (lp ++ [e])))
  : STHoare p env
      (Inv [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::for_each».call h![T, MaxLen, Env]
        h![self, f])
      (fun _ => Inv (embed self) ⋆ [λf ↦ fb]) := by
  enter_decl
  have hb : bounded self := (bounded_iff_wellFormed (v := self)).2 hwf_self
  -- Reduce `isUnconstrained()` (always `false`) and enter the constrained branch.
  steps
  all_goals (try exact ())
  apply STHoare.ite_intro_of_false rfl
  steps
  rw [SLP.star_comm]
  apply forEachLike_constrained_loop_spec (p := p) (T := T) (MaxLen := MaxLen)
    (Args := [T]) (mkArgs := fun _ a => h![a])
    (self := self) (f := f) (fb := fb)
    (hb := hb) (Inv := Inv) (inv_step := by
      intro ip i e hprefix _
      exact h_inv (lp := ip) (e := e) hprefix)

theorem for_eachi_spec {T Env p MaxLen self f fb}
    (hwf_self : wellFormed self)
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec :
      ∀ (ip : List (T.denote p)) (e : T.denote p),
        (ip ++ [e] <+: embed self) →
          STHoare p env (inv ip) (fb h![ip.length, e]) (fun _ => inv (ip ++ [e])))
  : STHoare p env
      (inv [] ⋆ [λf ↦ fb])
      («std-1.0.0-beta.12::collections::bounded_vec::BoundedVec::for_eachi».call h![T, MaxLen, Env]
        h![self, f])
      (fun _ => inv (embed self) ⋆ [λf ↦ fb]) := by
  enter_decl
  have hb : bounded self := (bounded_iff_wellFormed (v := self)).2 hwf_self
  -- Reduce `isUnconstrained()` (always `false`) and enter the constrained branch.
  steps
  all_goals (try exact ())
  apply STHoare.ite_intro_of_false rfl
  steps
  rw [SLP.star_comm]
  apply forEachLike_constrained_loop_spec (p := p) (T := T) (MaxLen := MaxLen)
    (Args := [Tp.u 32, T]) (mkArgs := fun i a => h![i, a])
    (self := self) (f := f) (fb := fb)
    (hb := hb) (Inv := inv) (inv_step := by
      intro ip i e hprefix hip_len
      have i_eq_len : (ip).length = i.toNat := by omega
      have h := inv_spec (ip := ip) (e := e) hprefix
      simpa [i_eq_len] using h)

end Lampe.Stdlib.Collections.BoundedVec
