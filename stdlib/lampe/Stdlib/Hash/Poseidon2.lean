import «std-1.0.0-beta.14».Extracted
import Lampe
import Lampe.Crypto.Poseidon2
import Stdlib.Default
import Stdlib.Tuple
import Stdlib.Vector

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.14»
open Lampe.Crypto

abbrev Poseidon2Tp : Tp :=
  «std-1.0.0-beta.14::hash::poseidon2::Poseidon2».tp h![]

abbrev Poseidon2Repr (p : Prime) : Type :=
  Tp.denote p Poseidon2Tp

abbrev Poseidon2HasherTp : Tp :=
  «std-1.0.0-beta.14::hash::poseidon2::Poseidon2Hasher».tp h![]

abbrev Poseidon2HasherRepr (p : Prime) : Type :=
  Tp.denote p Poseidon2HasherTp

def addCachePrefixToState {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (n : Nat) : List.Vector (Fp p) 4 :=
  List.Vector.ofFn fun i =>
    if hRate : i.val < 3 then
      if hActive : i.val < n ∧ i.val < cacheSize.toNat then
        state.get i + cache.get ⟨i.val, hRate⟩
      else
        state.get i
    else
      state.get i

def mkPoseidon2Repr {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (squeezeMode : Bool) : Poseidon2Repr p :=
  Tuple.mk
    (p := p)
    (memTps := [Tp.field.array (3 : U 32), Tp.field.array (4 : U 32), Tp.u 32, Tp.bool])
    h![cache, state, cacheSize, squeezeMode]

def spongeToRepr {p}
    (s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)) : Poseidon2Repr p :=
  mkPoseidon2Repr s.cache s.state (s.cacheSize : U 32) s.squeezeMode

def reprToSponge {p} (s : Poseidon2Repr p) :
    Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p) where
  cache := s.1
  state := s.2.1
  cacheSize := s.2.2.1.toNat
  squeezeMode := s.2.2.2.1

def mkPoseidon2HasherRepr {p} (inputs : List (Fp p)) : Poseidon2HasherRepr p :=
  Tuple.mk
    (p := p)
    (memTps := [Tp.field.vector])
    h![inputs]

private lemma mkPoseidon2HasherRepr_head {p} (inputs : List (Fp p)) :
    Builtin.indexTpl (mkPoseidon2HasherRepr inputs) Member.head = inputs := by
  rfl

def performDuplexRepr {p} (s : Poseidon2Repr p) : Poseidon2Repr p :=
  let cache := s.1
  let state := s.2.1
  let cacheSize := s.2.2.1
  let squeezeMode := s.2.2.2.1
  mkPoseidon2Repr cache
    (Crypto.Poseidon2.noirPermutation4 (addCachePrefixToState cache state cacheSize 3))
    cacheSize
    squeezeMode

def absorbRepr? {p} (s : Poseidon2Repr p) (input : Fp p) : Option (Poseidon2Repr p) :=
  (Crypto.Poseidon2.Sponge.absorb? (Crypto.Poseidon2.noirParams4 p)
    (reprToSponge s) input).map spongeToRepr

def squeezeRepr? {p} (s : Poseidon2Repr p) : Option (Fp p × Poseidon2Repr p) :=
  (Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p)
    (reprToSponge s)).map fun (out, sponge) => (out, spongeToRepr sponge)

private lemma vector_ext_get {α n} {v w : List.Vector α n}
    (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  apply List.Vector.eq
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    simpa [List.Vector.get] using h ⟨i, by simpa using hi₁⟩

private lemma addCachePrefixToState_succ_inactive {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (i : Nat)
    (hiRate : i < 3)
    (hinactive : cacheSize.toNat ≤ i) :
    addCachePrefixToState cache state cacheSize i =
      addCachePrefixToState cache state cacheSize (i + 1) := by
  apply vector_ext_get
  intro j
  simp [addCachePrefixToState]
  by_cases hjRate : j.val < 3
  · simp [hjRate]
    by_cases hjCache : j.val < cacheSize.toNat
    · simp [Nat.lt_of_lt_of_le hjCache hinactive, show j.val < i + 1 by omega, hjCache]
    · simp [hjCache]
  · simp [hjRate]

private lemma addCachePrefixToState_succ_active {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (i : Nat)
    (hiRate : i < 3)
    (hiState : i < 4)
    (hactive : i < cacheSize.toNat) :
    (addCachePrefixToState cache state cacheSize i).set
        ⟨i, hiState⟩
        ((addCachePrefixToState cache state cacheSize i).get
            ⟨i, hiState⟩ + cache.get ⟨i, hiRate⟩) =
      addCachePrefixToState cache state cacheSize (i + 1) := by
  apply vector_ext_get
  intro j
  let iFin : Fin 4 := ⟨i, Nat.lt_trans hiRate (by decide)⟩
  by_cases hji : iFin = j
  · subst j
    rw [List.Vector.get_set_same]
    simp [addCachePrefixToState, hactive, iFin]
    omega
  · have hval_ne : j.val ≠ i := by
      intro h
      apply hji
      ext
      exact h.symm
    rw [List.Vector.get_set_of_ne hji]
    simp [addCachePrefixToState]
    by_cases hjRate : j.val < 3
    · simp [hjRate]
      by_cases hjlt : j.val < i
      · simp [hjlt, show j.val < i + 1 by omega,
          show j.val < cacheSize.toNat by omega]
      · simp [hjlt, show ¬ j.val < i + 1 by omega]
    · simp [hjRate]

private lemma mkPoseidon2Repr_state_set_active {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (squeezeMode : Bool)
    (i : Nat)
    (hiRate : i < 3)
    (hiState : i < 4)
    (hactive : i < cacheSize.toNat) :
    Builtin.replaceTuple'
        (mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize i) cacheSize squeezeMode)
        Member.head.tail
        ((Builtin.indexTpl
            (mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize i) cacheSize squeezeMode)
            Member.head.tail).set ⟨i, hiState⟩
          ((Builtin.indexTpl
              (mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize i) cacheSize squeezeMode)
              Member.head.tail).get ⟨i, hiState⟩ +
            (Builtin.indexTpl
                (mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize i) cacheSize squeezeMode)
                Member.head).get ⟨i, hiRate⟩)) =
      mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize (i + 1)) cacheSize squeezeMode := by
  change (cache,
      (addCachePrefixToState cache state cacheSize i).set ⟨i, hiState⟩
        ((addCachePrefixToState cache state cacheSize i).get ⟨i, hiState⟩ + cache.get ⟨i, hiRate⟩),
      cacheSize, squeezeMode, ()) =
    mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize (i + 1)) cacheSize squeezeMode
  rw [addCachePrefixToState_succ_active cache state cacheSize i hiRate hiState hactive]
  rfl

private lemma mkPoseidon2Repr_cache_set_get {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (input : Fp p)
    (hspace : cacheSize.toNat < 3)
    (hmod :
      (((Lens.nil.cons (Access.tuple Member.head)).cons
          (Access.array cacheSize)).modify
          (mkPoseidon2Repr cache state cacheSize false) input).isSome = true) :
    (((Lens.nil.cons (Access.tuple Member.head)).cons
        (Access.array cacheSize)).modify
        (mkPoseidon2Repr cache state cacheSize false) input).get hmod =
      mkPoseidon2Repr (cache.set ⟨cacheSize.toNat, hspace⟩ input) state cacheSize false := by
  simp [mkPoseidon2Repr, Lens.modify, Access.modify, hspace]

private lemma addCachePrefixToState_eq_addCacheToState {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (squeezeMode : Bool) :
    addCachePrefixToState cache state cacheSize 3 =
      Crypto.Poseidon2.Sponge.addCacheToState (Crypto.Poseidon2.noirParams4 p)
        { cache := cache
          state := state
          cacheSize := cacheSize.toNat
          squeezeMode := squeezeMode } := by
  apply vector_ext_get
  intro i
  simp [addCachePrefixToState, Crypto.Poseidon2.Sponge.addCacheToState,
    Crypto.Poseidon2.noirParams4]
  by_cases hi : i.val < 3
  · simp [hi]
  · simp [hi]

private lemma noirPermutation4_addCachePrefixToState_eq_sponge {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (squeezeMode : Bool) :
    Crypto.Poseidon2.noirPermutation4 (addCachePrefixToState cache state cacheSize 3) =
      (Crypto.Poseidon2.noirParams4 p).permute
        (Crypto.Poseidon2.Sponge.addCacheToState (Crypto.Poseidon2.noirParams4 p)
          { cache := cache
            state := state
            cacheSize := cacheSize.toNat
            squeezeMode := squeezeMode }) := by
  rw [addCachePrefixToState_eq_addCacheToState cache state cacheSize squeezeMode]
  rfl

private def absorbList? {F : Type} (params : Crypto.Poseidon2.Params F) [Add F] :
    Crypto.Poseidon2.Sponge F params → List F → Option (Crypto.Poseidon2.Sponge F params)
  | s, [] => some s
  | s, x :: xs =>
      Option.bind (Crypto.Poseidon2.Sponge.absorb? params s x) (fun s' => absorbList? params s' xs)

private lemma absorbList?_append_one {F : Type} (params : Crypto.Poseidon2.Params F) [Add F]
    {s : Crypto.Poseidon2.Sponge F params} {xs : List F} {x : F} :
    absorbList? params s (xs ++ [x]) =
      Option.bind (absorbList? params s xs)
        (fun s'' => Crypto.Poseidon2.Sponge.absorb? params s'' x) := by
  induction xs generalizing s with
  | nil => simp [absorbList?]
  | cons y ys ih =>
      dsimp [absorbList?]
      cases hAbs : Crypto.Poseidon2.Sponge.absorb? params s y <;> simp [hAbs, ih]

private lemma absorbList?_take_succ {F : Type} (params : Crypto.Poseidon2.Params F) [Add F]
    {s s' : Crypto.Poseidon2.Sponge F params} {xs : List F} {i : Nat}
    (hi : i < xs.length)
    (h : absorbList? params s (xs.take i) = some s') :
    absorbList? params s (xs.take (i + 1)) =
      Crypto.Poseidon2.Sponge.absorb? params s' xs[i] := by
  rw [← List.take_append_getElem hi]
  rw [absorbList?_append_one (params := params)]
  simp [h]

private lemma absorbList?_take_succ_some {F : Type} (params : Crypto.Poseidon2.Params F) [Add F]
    {s s' s'' : Crypto.Poseidon2.Sponge F params} {xs : List F} {i : Nat}
    (hi : i < xs.length)
    (hprefix : absorbList? params s (xs.take i) = some s')
    (hAbs : Crypto.Poseidon2.Sponge.absorb? params s' xs[i] = some s'') :
    absorbList? params s (xs.take (i + 1)) = some s'' := by
  rw [absorbList?_take_succ (params := params) hi hprefix]
  exact hAbs

private lemma absorbList?_eq_absorbPrefix? {F : Type} (params : Crypto.Poseidon2.Params F) [Add F]
    {s : Crypto.Poseidon2.Sponge F params} {xs : List F} {n : Nat} :
    absorbList? params s (xs.take n) =
      Crypto.Poseidon2.Sponge.absorbPrefix? params s xs n := by
  induction xs generalizing s n with
  | nil =>
      cases n <;> simp [absorbList?, Crypto.Poseidon2.Sponge.absorbPrefix?]
  | cons x xs ih =>
      cases n with
      | zero => simp [absorbList?, Crypto.Poseidon2.Sponge.absorbPrefix?]
      | succ n =>
          simp [absorbList?, Crypto.Poseidon2.Sponge.absorbPrefix?]
          cases hAbs : Crypto.Poseidon2.Sponge.absorb? params s x <;> simp [hAbs]
          exact ih

private lemma absorbPrefix?_of_absorbList?_take {F : Type}
    (params : Crypto.Poseidon2.Params F) [Add F]
    {s s' : Crypto.Poseidon2.Sponge F params} {xs : List F} {n : Nat}
    (h : absorbList? params s (xs.take n) = some s') :
    Crypto.Poseidon2.Sponge.absorbPrefix? params s xs n = some s' := by
  rw [← absorbList?_eq_absorbPrefix? (params := params)]
  exact h

private def SpongeValid {p}
    (s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)) : Prop :=
  s.cacheSize ≤ 3 ∧ s.squeezeMode = false

private lemma SpongeValid.init {p} (iv : Fp p) :
    SpongeValid (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p) iv) := by
  simp [SpongeValid, Crypto.Poseidon2.Sponge.init, Crypto.Poseidon2.noirParams4]

private lemma reprToSponge_spongeToRepr_of_cacheSize_lt {p}
    (s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p))
    (hcache : s.cacheSize < 2 ^ 32) :
    reprToSponge (spongeToRepr s) = s := by
  rcases s with ⟨cache, state, cacheSize, squeezeMode⟩
  have hcache' : cacheSize < 4294967296 := by
    norm_num at hcache ⊢
    exact hcache
  simp [reprToSponge, spongeToRepr, mkPoseidon2Repr, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hcache']

private lemma SpongeValid.reprToSponge_spongeToRepr {p}
    {s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    (hv : SpongeValid s) :
    reprToSponge (spongeToRepr s) = s := by
  exact reprToSponge_spongeToRepr_of_cacheSize_lt s (by rcases hv with ⟨hcache, _⟩; omega)

private lemma SpongeValid.absorb?_some {p}
    {s s' : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    {input : Fp p}
    (hv : SpongeValid s)
    (h : Crypto.Poseidon2.Sponge.absorb? (Crypto.Poseidon2.noirParams4 p) s input = some s') :
    SpongeValid s' := by
  rcases s with ⟨cache, state, cacheSize, squeezeMode⟩
  rcases hv with ⟨hcache, hsqueeze⟩
  change cacheSize ≤ 3 at hcache
  change squeezeMode = false at hsqueeze
  subst squeezeMode
  simp [Crypto.Poseidon2.Sponge.absorb?, Crypto.Poseidon2.Sponge.performDuplex,
    Crypto.Poseidon2.noirParams4] at h
  by_cases hfull : cacheSize = 3
  · simp [hfull] at h
    cases h
    exact ⟨by simp, rfl⟩
  · simp [hfull] at h
    by_cases hspace : cacheSize < 3
    · simp [hspace] at h
      cases h
      simp [SpongeValid]
      omega
    · simp [hspace] at h

private lemma absorbRepr?_spongeToRepr {p}
    {s s' : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    {x : Fp p}
    (hv : SpongeValid s)
    (h : Crypto.Poseidon2.Sponge.absorb? (Crypto.Poseidon2.noirParams4 p) s x = some s') :
    absorbRepr? (spongeToRepr s) x = some (spongeToRepr s') := by
  simp [absorbRepr?, SpongeValid.reprToSponge_spongeToRepr hv, h]

private lemma squeezeRepr?_spongeToRepr {p}
    {s s' : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    {out : Fp p}
    (hv : SpongeValid s)
    (h : Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p) s = some (out, s')) :
    squeezeRepr? (spongeToRepr s) = some (out, spongeToRepr s') := by
  simp [squeezeRepr?, SpongeValid.reprToSponge_spongeToRepr hv, h]

private lemma take_min_succ_of_not_lt {α} (xs : List α) {i n : Nat} (h : ¬ i < n) :
    xs.take (Nat.min (i + 1) n) = xs.take (Nat.min i n) := by
  have hn : n ≤ i := by omega
  rw [show Nat.min (i + 1) n = n from Nat.min_eq_right (Nat.le_trans hn (Nat.le_succ i))]
  rw [show Nat.min i n = n from Nat.min_eq_right hn]

private lemma min_succ_of_lt {i n : Nat} (h : i < n) :
    Nat.min (i + 1) n = i + 1 := by
  exact Nat.min_eq_left (by omega)

private lemma min_current_of_lt {i n : Nat} (h : i < n) :
    Nat.min i n = i := by
  exact Nat.min_eq_left (by omega)

private lemma absorbList?_take_min_succ_of_lt {F : Type}
    (params : Crypto.Poseidon2.Params F) [Add F]
    {s s' s'' : Crypto.Poseidon2.Sponge F params} {xs : List F} {i n : Nat}
    (hiLen : i < n)
    (hiInput : i < xs.length)
    (hprefix : absorbList? params s (xs.take (Nat.min i n)) = some s')
    (hAbs : Crypto.Poseidon2.Sponge.absorb? params s' xs[i] = some s'') :
    absorbList? params s (xs.take (Nat.min (i + 1) n)) = some s'' := by
  have hprefixI : absorbList? params s (xs.take i) = some s' := by
    simpa [min_current_of_lt hiLen] using hprefix
  rw [min_succ_of_lt hiLen]
  rw [absorbList?_take_succ (params := params) (hi := hiInput) hprefixI]
  exact hAbs

private lemma absorbList?_take_min_succ_of_not_lt {F : Type}
    (params : Crypto.Poseidon2.Params F) [Add F]
    {s s' : Crypto.Poseidon2.Sponge F params} {xs : List F} {i n : Nat}
    (hge : n ≤ i)
    (hprefix : absorbList? params s (xs.take (Nat.min i n)) = some s') :
    absorbList? params s (xs.take (Nat.min (i + 1) n)) = some s' := by
  simpa [take_min_succ_of_not_lt xs (not_lt_of_ge hge)] using hprefix

private lemma lt_two_pow_of_lt_u32 {i : Nat} {x : U 32} (h : i < x.toNat) :
    i < 2 ^ 32 :=
  lt_trans h
    (by simpa using BitVec.toNat_lt_twoPow_of_le (m := 32) (n := 32) (x := x) (by rfl))

private lemma nat_lt_of_decide_bv_lt_trueLT {i : Nat} {x : U 32}
    (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNatLT i pf32 < x) = true) : i < x.toNat := by
  simpa [BitVec.lt_def, BitVec.toNat_ofNatLT] using of_decide_eq_true h

private lemma nat_le_of_decide_bv_lt_falseLT {i : Nat} {x : U 32}
    (pf32 : i < 2 ^ 32)
    (h : decide (BitVec.ofNatLT i pf32 < x) = false) : x.toNat ≤ i := by
  exact Nat.le_of_not_gt fun hlt => by
    have htrue : decide (BitVec.ofNatLT i pf32 < x) = true := by
      simp [BitVec.lt_def, BitVec.toNat_ofNatLT, hlt]
    rw [htrue] at h
    cases h

private lemma take_min_length_right {α} (xs : List α) (n : Nat) :
    xs.take (Nat.min xs.length n) = xs.take n := by
  by_cases hn : n ≤ xs.length
  · simp [Nat.min_eq_right hn]
  · have hlen : xs.length ≤ n := by omega
    simp [Nat.min_eq_left hlen, List.take_of_length_le hlen]

private lemma take_min_vector_length_right {α} {N : Nat} (input : List.Vector α N) (n : Nat) :
    input.toList.take (Nat.min N n) = input.toList.take n := by
  simpa using (take_min_length_right input.toList n)

private abbrev HashInternalLoopInv {p} {N : U 32}
    (input : List.Vector (Fp p) N.toNat)
    (inLen : U 32)
    (iv : Fp p)
    (spongeRef : Ref Poseidon2Tp)
    (i : Nat) : SLP (State p) :=
  ∃∃ s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p),
    [spongeRef ↦ ⟨Poseidon2Tp, spongeToRepr s⟩] ⋆
    ⟦absorbList? (Crypto.Poseidon2.noirParams4 p)
        (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p) iv)
        (input.toList.take (Nat.min i inLen.toNat)) = some s⟧ ⋆
    ⟦SpongeValid s⟧

private abbrev HasherFinishLoopInv {p}
    (inputs : List (Fp p))
    (iv : Fp p)
    (spongeRef : Ref Poseidon2Tp)
    (i : Nat) : SLP (State p) :=
  ∃∃ s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p),
    [spongeRef ↦ ⟨Poseidon2Tp, spongeToRepr s⟩] ⋆
    ⟦absorbList? (Crypto.Poseidon2.noirParams4 p)
        (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p) iv)
        (inputs.take i) = some s⟧ ⋆
    ⟦SpongeValid s⟧

theorem default_spec {p}
    : STHoare p env ⟦⟧
        (Lampe.Stdlib.Default.default h![]
          («std-1.0.0-beta.14::hash::poseidon2::Poseidon2Hasher».tp h![]) h![] h![] h![])
        (fun r => r = Tuple.mk h![([] : List (Tp.denote p .field))]) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem rate_spec {p}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::poseidon2::RATE».call h![] h![])
        (fun r => r = (3 : U 32)) := by
  enter_decl
  steps
  rename_i hrate
  simpa using hrate

theorem new_spec {p} {iv : Tp.denote p .field}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::new».call h![] h![iv])
        (fun r => r = spongeToRepr (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p) iv)) := by
  enter_decl
  steps [rate_spec]
  subst_vars
  rfl

theorem poseidon2_permutation_builtin_spec {p} {state : List.Vector (Fp p) 4}
    : STHoare p env ⟦⟧
        (.callBuiltin [Tp.field.array (4 : U 32)] (Tp.field.array (4 : U 32))
          Builtin.poseidon2Permutation h![state])
        (fun r => r = Crypto.Poseidon2.noirPermutation4 state) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.poseidon2Permutation rfl () p env h![state]

theorem perform_duplex_spec {p selfRef}
    {cache : List.Vector (Fp p) 3}
    {state : List.Vector (Fp p) 4}
    {cacheSize : U 32}
    {squeezeMode : Bool}
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2Tp, mkPoseidon2Repr cache state cacheSize squeezeMode⟩]
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::perform_duplex».call h![] h![selfRef])
        (fun _ =>
          [selfRef ↦ ⟨Poseidon2Tp,
            performDuplexRepr (mkPoseidon2Repr cache state cacheSize squeezeMode)⟩]) := by
  enter_decl
  steps [rate_spec]
  loop_inv nat (fun i _ _ =>
    [selfRef ↦ ⟨Poseidon2Tp,
      mkPoseidon2Repr cache (addCachePrefixToState cache state cacheSize i) cacheSize squeezeMode⟩])
  · simp [addCachePrefixToState, mkPoseidon2Repr]
  · simp
  · intro i hlo hhi
    steps
    apply STHoare.ite_intro
    · intro hcond
      steps
      have hactive : i < cacheSize.toNat := by
        simpa [mkPoseidon2Repr, BitVec.lt_def] using hcond
      rw [← mkPoseidon2Repr_state_set_active cache state cacheSize squeezeMode i hhi
        (Nat.lt_trans hhi (by decide)) hactive]
      simp [Lens.modify, Access.modify, mkPoseidon2Repr, Builtin.indexTpl, Builtin.replaceTuple']
    · intro hcond
      steps
      have hinactive : cacheSize.toNat ≤ i := by
        simpa [mkPoseidon2Repr, BitVec.not_lt] using hcond
      simp [mkPoseidon2Repr, Builtin.replaceTuple', Builtin.indexTpl,
        addCachePrefixToState_succ_inactive cache state cacheSize i hhi hinactive]
  · steps [poseidon2_permutation_builtin_spec]

theorem absorb_spec {p selfRef}
    {self out : Poseidon2Repr p}
    {input : Fp p}
    (hout : absorbRepr? self input = some out)
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2Tp, self⟩]
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::absorb».call h![] h![selfRef, input])
        (fun _ => [selfRef ↦ ⟨Poseidon2Tp, out⟩]) := by
  rcases self with ⟨cache, state, cacheSize, squeezeMode, unitTail⟩
  cases unitTail
  simp [absorbRepr?, reprToSponge, Crypto.Poseidon2.Sponge.absorb?,
    Crypto.Poseidon2.noirParams4] at hout
  rcases hout with ⟨modelOut, ⟨hsqueezeMode, hmodel⟩, hout⟩
  subst squeezeMode
  enter_decl
  steps [rate_spec]
  apply STHoare.ite_intro
  · intro hfull
    steps [perform_duplex_spec (cache := cache) (state := state) (cacheSize := cacheSize)
      (squeezeMode := false)]
    have hfullEq : cacheSize = (3 : U 32) := by
      simpa [mkPoseidon2Repr] using (of_decide_eq_true hfull)
    have hfullNat : cacheSize.toNat = 3 := by
      simp [hfullEq]
    simp [hfullNat] at hmodel
    cases hmodel
    rw [← hout]
    subst cacheSize
    congr
  · intro hnotFull
    have hnotFullEq : cacheSize ≠ (3 : U 32) := by
      simpa [mkPoseidon2Repr, decide_eq_false_iff_not] using hnotFull
    have hnotFullNat : cacheSize.toNat ≠ 3 := by
      intro hnat
      apply hnotFullEq
      apply BitVec.eq_of_toNat_eq
      simp [hnat]
    simp [hnotFullNat] at hmodel
    by_cases hspace : cacheSize.toNat < 3
    · simp [hspace] at hmodel
      cases hmodel
      let cacheAfter : Poseidon2Repr p :=
        mkPoseidon2Repr (cache.set ⟨cacheSize.toNat, hspace⟩ input) state cacheSize false
      apply STHoare.letIn_intro (Q := fun _ => [selfRef ↦ ⟨Poseidon2Tp, cacheAfter⟩])
      · steps
        subst i_2755
        congr
        exact mkPoseidon2Repr_cache_set_get cache state cacheSize input hspace _
      · intro _
        steps
        rw [← hout]
        congr
    · rcases hmodel with ⟨hspace', _⟩
      exact False.elim (hspace hspace')

private lemma SpongeValid.absorb?_exists {p}
    (s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p))
    (input : Fp p)
    (hv : SpongeValid s) :
    ∃ s', Crypto.Poseidon2.Sponge.absorb? (Crypto.Poseidon2.noirParams4 p) s input = some s' := by
  rcases s with ⟨cache, state, cacheSize, squeezeMode⟩
  rcases hv with ⟨hcache, hsqueeze⟩
  have hcache' : cacheSize ≤ 3 := by simpa [SpongeValid] using hcache
  have hsqueeze' : squeezeMode = false := by simpa [SpongeValid] using hsqueeze
  subst squeezeMode
  by_cases hfull : cacheSize = 3
  · simp [Crypto.Poseidon2.Sponge.absorb?, Crypto.Poseidon2.Sponge.performDuplex,
      Crypto.Poseidon2.noirParams4, hfull]
  · have hspace : cacheSize < 3 := by omega
    simp [Crypto.Poseidon2.Sponge.absorb?, Crypto.Poseidon2.noirParams4, hfull, hspace]

private lemma SpongeValid.absorb?_step {p}
    (s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p))
    (input : Fp p)
    (hv : SpongeValid s) :
    ∃ s',
      Crypto.Poseidon2.Sponge.absorb? (Crypto.Poseidon2.noirParams4 p) s input = some s' ∧
      absorbRepr? (spongeToRepr s) input = some (spongeToRepr s') ∧
      SpongeValid s' := by
  rcases SpongeValid.absorb?_exists s input hv with ⟨s', hAbs⟩
  exact ⟨s', hAbs, absorbRepr?_spongeToRepr hv hAbs, SpongeValid.absorb?_some hv hAbs⟩

private lemma SpongeValid.squeeze?_of_hash?_false {p}
    {inputs : List (Fp p)}
    {inLen : Nat}
    {s : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    {out : Fp p}
    (hprefix : Crypto.Poseidon2.Sponge.absorbPrefix? (Crypto.Poseidon2.noirParams4 p)
      (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p)
        (Crypto.Poseidon2.Sponge.noirIV inLen)) inputs inLen = some s)
    (hout : Crypto.Poseidon2.Sponge.hash?
      (Crypto.Poseidon2.noirParams4 p) inputs inLen false = some out) :
    ∃ s',
      Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p) s = some (out, s') := by
  simp [Crypto.Poseidon2.Sponge.hash?, Crypto.Poseidon2.Sponge.hashWithIV?, hprefix] at hout
  rcases hsq : Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p) s with _ | ⟨out', s'⟩
  · simp [hsq] at hout
  · simp [hsq] at hout
    subst out'
    exact ⟨s', rfl⟩

private lemma SpongeValid.squeeze?_of_hash?_true {p}
    {inputs : List (Fp p)}
    {inLen : Nat}
    {s s1 : Crypto.Poseidon2.Sponge (Fp p) (Crypto.Poseidon2.noirParams4 p)}
    {out : Fp p}
    (hprefix : Crypto.Poseidon2.Sponge.absorbPrefix? (Crypto.Poseidon2.noirParams4 p)
      (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p)
        (Crypto.Poseidon2.Sponge.noirIV inLen)) inputs inLen = some s)
    (hAbsMarker : Crypto.Poseidon2.Sponge.absorb?
      (Crypto.Poseidon2.noirParams4 p) s (1 : Fp p) = some s1)
    (hout : Crypto.Poseidon2.Sponge.hash?
      (Crypto.Poseidon2.noirParams4 p) inputs inLen true = some out) :
    ∃ s',
      Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p) s1 = some (out, s') := by
  simp [Crypto.Poseidon2.Sponge.hash?, Crypto.Poseidon2.Sponge.hashWithIV?, hprefix,
    hAbsMarker] at hout
  rcases hsq : Crypto.Poseidon2.Sponge.squeeze? (Crypto.Poseidon2.noirParams4 p) s1 with _ | ⟨out', s'⟩
  · simp [hsq] at hout
  · simp [hsq] at hout
    subst out'
    exact ⟨s', rfl⟩

theorem squeeze_spec {p selfRef}
    {self outSelf : Poseidon2Repr p}
    {out : Fp p}
    (hout : squeezeRepr? self = some (out, outSelf))
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2Tp, self⟩]
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::squeeze».call h![] h![selfRef])
        (fun r => [selfRef ↦ ⟨Poseidon2Tp, outSelf⟩] ⋆ ⟦r = out⟧) := by
  rcases self with ⟨cache, state, cacheSize, squeezeMode, unit0⟩
  simp [squeezeRepr?, reprToSponge, Crypto.Poseidon2.Sponge.squeeze?,
    Crypto.Poseidon2.Sponge.performDuplex, spongeToRepr, performDuplexRepr,
    mkPoseidon2Repr] at hout
  rcases hout with ⟨hsqueeze, houtVal, houtSelf⟩
  subst squeezeMode
  enter_decl
  steps [perform_duplex_spec
    (cache := cache) (state := state) (cacheSize := cacheSize) (squeezeMode := false)]
  · rename_i hModify ret hBound hRet
    simp [Lens.modify, Access.modify, performDuplexRepr, mkPoseidon2Repr,
      Builtin.indexTpl, Builtin.replaceTuple'] at hRet ⊢
    rw [hRet]
    rw [noirPermutation4_addCachePrefixToState_eq_sponge cache state cacheSize false]
    exact houtVal
  · rename_i hModify ret hBound hRet
    simp [Lens.modify, Access.modify, performDuplexRepr, mkPoseidon2Repr,
      Builtin.indexTpl, Builtin.replaceTuple'] at hModify ⊢
    rw [noirPermutation4_addCachePrefixToState_eq_sponge cache state cacheSize false]
    congr

theorem hash_internal_spec {p}
    {N : U 32}
    {input : Tp.denote p (Tp.field.array N)}
    {inLen : U 32}
    {isVariableLength : Bool}
    {out : Fp p}
    (hout : (Crypto.Poseidon2.Sponge.hash?
        (Crypto.Poseidon2.noirParams4 p)
        input.toList
        inLen.toNat
        isVariableLength) = some out)
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::hash_internal».call h![N]
          h![input, inLen, isVariableLength])
        (fun r => r = out) := by
  enter_decl
  steps [new_spec]
  subst_vars
  loop_inv nat (fun i _ _ =>
    HashInternalLoopInv input inLen (Crypto.Poseidon2.Sponge.noirIV inLen.toNat) sponge i)
  · dsimp [HashInternalLoopInv]
    sl
    · simp [absorbList?, Crypto.Poseidon2.Sponge.noirIV]
    · exact SpongeValid.init _
  · simp
  · intro i hlo hhi
    apply Steps.pull_exi
    intro s
    steps
    rename_i hprefix hvalid
    apply STHoare.ite_intro
    · intro hcond
      have hiLen : i < inLen.toNat :=
        nat_lt_of_decide_bv_lt_trueLT (lt_two_pow_of_lt_u32 hhi) hcond
      have hiInput : i < input.toList.length := by
        simpa [BitVec.toNat_ofNatLT] using hhi
      rcases SpongeValid.absorb?_step s input.toList[i] hvalid with ⟨s', hAbs, hrepr, hvalid'⟩
      steps [absorb_spec (selfRef := sponge) hrepr]
      dsimp [HashInternalLoopInv]
      sl
      · exact absorbList?_take_min_succ_of_lt
          (Crypto.Poseidon2.noirParams4 p) hiLen hiInput hprefix hAbs
      · exact hvalid'
    · intro hcond
      have hgeLen : inLen.toNat ≤ i :=
        nat_le_of_decide_bv_lt_falseLT (lt_two_pow_of_lt_u32 hhi) hcond
      steps
      dsimp [HashInternalLoopInv]
      sl
      · exact absorbList?_take_min_succ_of_not_lt
          (Crypto.Poseidon2.noirParams4 p) hgeLen hprefix
      · exact hvalid
  · steps_named as [hbound, s, hprefix, hvalid]
    have hprefixSem :
        Crypto.Poseidon2.Sponge.absorbPrefix? (Crypto.Poseidon2.noirParams4 p)
          (Crypto.Poseidon2.Sponge.init (Crypto.Poseidon2.noirParams4 p)
            (Crypto.Poseidon2.Sponge.noirIV inLen.toNat)) input.toList inLen.toNat = some s :=
      absorbPrefix?_of_absorbList?_take (Crypto.Poseidon2.noirParams4 p)
        (by simpa [BitVec.toNat_ofNatLT, take_min_vector_length_right input inLen.toNat] using hprefix)
    cases isVariableLength
    · rcases SpongeValid.squeeze?_of_hash?_false hprefixSem hout with ⟨s', hsq⟩
      apply STHoare.letIn_intro (Q := fun _ => [sponge ↦ ⟨Poseidon2Tp, spongeToRepr s⟩])
      · apply STHoare.ite_intro_of_false rfl
        steps
      · intro _
        steps [squeeze_spec (selfRef := sponge) (squeezeRepr?_spongeToRepr hvalid hsq)]
        subst_vars
        rfl
    · rcases SpongeValid.absorb?_step s (1 : Fp p) hvalid with
        ⟨s1, hAbsMarker, hreprMarker, hvalid1⟩
      rcases SpongeValid.squeeze?_of_hash?_true hprefixSem hAbsMarker hout with ⟨s', hsq⟩
      apply STHoare.letIn_intro (Q := fun _ => [sponge ↦ ⟨Poseidon2Tp, spongeToRepr s1⟩])
      · apply STHoare.ite_intro_of_true rfl
        steps [absorb_spec (selfRef := sponge) hreprMarker]
      · intro _
        steps [squeeze_spec (selfRef := sponge) (squeezeRepr?_spongeToRepr hvalid1 hsq)]
        subst_vars
        rfl

theorem hash_spec {p}
    {N : U 32}
    {input : Tp.denote p (Tp.field.array N)}
    {messageSize : U 32}
    {out : Fp p}
    (hout : Crypto.Poseidon2.Sponge.hash?
        (Crypto.Poseidon2.noirParams4 p)
        input.toList
        messageSize.toNat
        (messageSize ≠ N) = some out)
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::hash».call h![N]
          h![input, messageSize])
        (fun r => r = out) := by
  enter_decl
  steps [hash_internal_spec hout]
  assumption

theorem hasher_write_spec {p selfRef}
    {inputs : List (Fp p)}
    {input : Fp p}
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩]
        («std-1.0.0-beta.14::hash::Hasher».write h![] Poseidon2HasherTp h![] h![]
          h![selfRef, input])
        (fun _ => [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr (inputs ++ [input])⟩]) := by
  resolve_trait
  steps

theorem hasher_finish_spec {p}
    {inputs : List (Fp p)}
    {out : Fp p}
    (hout : Crypto.Poseidon2.Sponge.hash?
        (Crypto.Poseidon2.noirParams4 p)
        inputs
        inputs.length
        false = some out)
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.14::hash::Hasher».finish h![] Poseidon2HasherTp h![] h![]
          h![mkPoseidon2HasherRepr inputs])
        (fun r => r = out) := by
  resolve_trait
  steps [new_spec]
  subst_vars
  loop_inv nat (fun i _ _ =>
    HasherFinishLoopInv inputs (Crypto.Poseidon2.Sponge.noirIV inputs.length) sponge i)
  · dsimp [HasherFinishLoopInv]
    sl
    · simp [absorbList?, mkPoseidon2HasherRepr_head, Crypto.Poseidon2.Sponge.noirIV]
    · exact SpongeValid.init _
  · simp
  · intro i hlo hhi
    apply Steps.pull_exi
    intro s
    steps
    rename_i hprefix hvalid hidx
    simp [mkPoseidon2HasherRepr_head, BitVec.toNat_ofNatLT, List.get_eq_getElem]
    have hiInputs : i < inputs.length := by
      simpa [mkPoseidon2HasherRepr_head, BitVec.toNat_ofNatLT] using hhi
    rcases SpongeValid.absorb?_step s inputs[i] hvalid with ⟨s', hAbs, hrepr, hvalid'⟩
    steps [absorb_spec (selfRef := sponge) hrepr]
    dsimp [HasherFinishLoopInv]
    sl
    · exact absorbList?_take_succ_some (Crypto.Poseidon2.noirParams4 p) hiInputs hprefix hAbs
    · exact hvalid'
  · steps_named as [hbound, s, hprefix, hvalid]
    rcases SpongeValid.squeeze?_of_hash?_false
        (absorbPrefix?_of_absorbList?_take (Crypto.Poseidon2.noirParams4 p)
          (by simpa [mkPoseidon2HasherRepr_head, BitVec.toNat_ofNatLT] using hprefix))
        hout with ⟨s', hsq⟩
    steps [squeeze_spec (selfRef := sponge) (squeezeRepr?_spongeToRepr hvalid hsq)]
    subst_vars
    rfl

end Lampe.Stdlib.Hash.Poseidon2
