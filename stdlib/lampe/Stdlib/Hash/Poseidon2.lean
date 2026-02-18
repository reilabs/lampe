import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.12»

variable {p : Prime}

/-- Helper to construct a Poseidon2 value -/
def mkPoseidon2 {p : Prime} (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) (squeeze_mode : Bool) :
    Tp.denote p («std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![]) :=
  (cache, state, cache_size, squeeze_mode, ())

@[simp] lemma indexTpl_cache {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} :
    Builtin.indexTpl (mkPoseidon2 cache state cs sq) Builtin.Member.head = cache := rfl

@[simp] lemma indexTpl_state {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} :
    Builtin.indexTpl (mkPoseidon2 cache state cs sq) Builtin.Member.head.tail = state := rfl

@[simp] lemma indexTpl_cache_size {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} :
    Builtin.indexTpl (mkPoseidon2 cache state cs sq) Builtin.Member.head.tail.tail = cs := rfl

@[simp] lemma replaceTuple_state {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} {new_state : List.Vector (Fp p) 4} :
    Builtin.replaceTuple' (mkPoseidon2 cache state cs sq) Builtin.Member.head.tail new_state
      = mkPoseidon2 cache new_state cs sq := rfl

@[simp] lemma replaceTuple_cache {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} {new_cache : List.Vector (Fp p) 3} :
    Builtin.replaceTuple' (mkPoseidon2 cache state cs sq) Builtin.Member.head new_cache
      = mkPoseidon2 new_cache state cs sq := rfl

@[simp] lemma indexTpl_squeeze_mode {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} :
    Builtin.indexTpl (mkPoseidon2 cache state cs sq) Builtin.Member.head.tail.tail.tail = sq := rfl

@[simp] lemma replaceTuple_cache_size {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cs : U 32} {sq : Bool} {new_cs : U 32} :
    Builtin.replaceTuple' (mkPoseidon2 cache state cs sq) Builtin.Member.head.tail.tail new_cs
      = mkPoseidon2 cache state new_cs sq := rfl

theorem rate_spec :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::hash::poseidon2::RATE».call h![] h![])
    (fun r => r = (3 : U 32)) := by
  enter_decl
  steps
  rename_i h
  simp only [Nat.cast_ofNat] at h
  exact h

theorem poseidon2_hasher_default_spec :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::default::Default».default h![]
      («std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher».tp h![]) h![] h![] h![])
    (fun r => r = ([], ())) := by
  resolve_trait
  steps
  simp_all

theorem poseidon2_hasher_write_spec {s : List (Fp p)} {input : Fp p} {r : Ref} :
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher».tp h![], (s, ())⟩]
    («std-1.0.0-beta.12::hash::Hasher».write h![]
      («std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher».tp h![])
      h![] h![] h![r, input])
    (fun _ => [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher».tp h![], (s ++ [input], ())⟩]) := by
  resolve_trait
  steps

/-- Mix cache into state: for i < min(cache_size, RATE), state[i] += cache[i] -/
def mixCacheIntoState (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) : List.Vector (Fp p) 4 :=
  let s0 := if (0 : U 32) < cache_size then
      state.set ⟨0, by omega⟩ (state.get ⟨0, by omega⟩ + cache.get ⟨0, by omega⟩)
    else state
  let s1 := if (1 : U 32) < cache_size then
      s0.set ⟨1, by omega⟩ (s0.get ⟨1, by omega⟩ + cache.get ⟨1, by omega⟩)
    else s0
  let s2 := if (2 : U 32) < cache_size then
      s1.set ⟨2, by omega⟩ (s1.get ⟨2, by omega⟩ + cache.get ⟨2, by omega⟩)
    else s1
  s2

/-- State after i iterations of the cache mixing loop -/
def partialMix (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) : Nat → List.Vector (Fp p) 4
  | 0 => state
  | n + 1 =>
    let prev := partialMix cache state cache_size n
    if h : n < 3 then
      if (BitVec.ofNat 32 n) < cache_size then
        prev.set ⟨n, by omega⟩ (prev.get ⟨n, by omega⟩ + cache.get ⟨n, h⟩)
      else prev
    else prev

lemma partialMix_3_eq_mixCacheIntoState
    (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4) (cache_size : U 32) :
    partialMix cache state cache_size 3 = mixCacheIntoState cache state cache_size := by
  simp [partialMix, mixCacheIntoState]

theorem poseidon2_permutation_4_spec {state : List.Vector (Fp p) 4} :
    STHoare p env ⟦⟧
      (Expr.callBuiltin [Tp.field.array 4#32, Tp.u 32] (Tp.field.array 4#32)
        Builtin.poseidon2Permutation h![state, (4 : U 32)])
      (fun v => v = Builtin.poseidon2PermFn p 4#32 state) := by
  simpa [Builtin.poseidon2Permutation] using
    (STHoare.genericTotalPureBuiltin_intro
      (A := U 32)
      (sgn := fun n : U 32 => ⟨[.array .field n, .u 32], .array .field n⟩)
      (desc := fun n h![st, _width] => Builtin.poseidon2PermFn _ n st)
      (b := Builtin.poseidon2Permutation) rfl
      (a := (4 : U 32)) (p := p) (Γ := env) (args := h![state, (4 : U 32)]))

theorem perform_duplex_spec
    {r : Ref}
    {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cache_size : U 32} {squeeze_mode : Bool} :
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache state cache_size squeeze_mode⟩]
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::perform_duplex».call h![] h![r])
    (fun _ => [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache (Builtin.poseidon2PermFn p 4 (mixCacheIntoState cache state cache_size))
            cache_size squeeze_mode⟩]) := by
  enter_decl
  steps [rate_spec]
  loop_inv nat fun i _ _ =>
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache (partialMix cache state cache_size i) cache_size squeeze_mode⟩]
  · simp [partialMix]
  · intro i hlo hhi
    steps
    simp only [indexTpl_cache_size]
    apply STHoare.ite_intro
    · intro hcond
      have hi3 : i < 3 := by simpa [BitVec.toNat] using hhi
      have hi4 : i < 4 := by omega
      have hcond' := hcond
      simp at hcond'
      have hic : (BitVec.ofNat 32 i) < cache_size := by
        simpa [BitVec.ofNatLT_eq_ofNat] using hcond'
      steps
      simp_all [Lens.modify, Lens.get, Access.modify, Access.get,
        indexTpl_state, indexTpl_cache, replaceTuple_state, partialMix,
        Builtin.CastTp.cast, Option.bind, Option.bind_some, Option.get_some,
        hi3, hi4, hic]
    · intro hcond
      have hi3 : i < 3 := by simpa [BitVec.toNat] using hhi
      have hcond' := hcond
      simp at hcond'
      have hnic : ¬((BitVec.ofNat 32 i) < cache_size) := by
        simpa [BitVec.ofNatLT_eq_ofNat] using hcond'
      steps
      simp [partialMix, hi3, hnic]
  steps [poseidon2_permutation_4_spec]

theorem squeeze_spec
    {r : Ref}
    {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cache_size : U 32} :
    let permuted := Builtin.poseidon2PermFn p 4 (mixCacheIntoState cache state cache_size)
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache state cache_size false⟩]
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::squeeze».call h![] h![r])
    (fun result => result = permuted.get ⟨0, by simp [BitVec.toNat]⟩ ⋆
      [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
            mkPoseidon2 cache permuted cache_size true⟩]) := by
  enter_decl
  steps [perform_duplex_spec]
  subst_vars
  simp only [Builtin.indexTpl, Builtin.replaceTuple', Lens.modify, Lens.get,
    Access.modify, mkPoseidon2]
  rfl

theorem new_spec {iv : Fp p} :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::new».call h![] h![iv])
    (fun r => r = mkPoseidon2 ⟨[0, 0, 0], rfl⟩ ⟨[0, 0, 0, iv], rfl⟩ 0 false) := by
  enter_decl
  steps [rate_spec]
  subst_vars
  simp_all only [Lens.modify, Access.modify, HList.toTuple,
    List.Vector.replicate, BitVec.toNat]
  dsimp [Builtin.replaceTuple', Builtin.indexTpl]
  simp [List.Vector.set, mkPoseidon2]
  norm_cast

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem absorb_spec_not_full {r : Ref}
    {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cache_size : U 32} {input : Fp p}
    (h_not_full : cache_size.toNat < 3) :
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache state cache_size false⟩]
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::absorb».call h![] h![r, input])
    (fun _ => [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 (cache.set ⟨cache_size.toNat, h_not_full⟩ input) state (cache_size + 1) false⟩]) := by
  enter_decl
  set_option maxRecDepth 4096 in
  steps [rate_spec]
  simp only [indexTpl_cache_size]
  apply STHoare.ite_intro
  · intro hcond
    simp at hcond
    subst hcond
    simp at h_not_full
  · intro hcond
    set_option maxRecDepth 4096 in
    apply STHoare.letIn_intro (Q := fun _ =>
      [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
            mkPoseidon2 (cache.set ⟨cache_size.toNat, h_not_full⟩ input) state cache_size false⟩])
    · steps
      subst_vars
      simp only [indexTpl_cache_size, indexTpl_cache, replaceTuple_cache,
        Lens.modify, Lens.get, Access.modify, Access.get, Builtin.CastTp.cast,
        Option.bind, Option.bind_some, Option.get_some, h_not_full, dite_true,
        Bind.bind, Pure.pure, BitVec.toNat]
      simp [h_not_full]
    · intro _
      steps

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem absorb_spec_full {r : Ref}
    {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {input : Fp p} :
    let permuted := Builtin.poseidon2PermFn p 4 (mixCacheIntoState cache state 3)
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache state 3 false⟩]
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::absorb».call h![] h![r, input])
    (fun _ => [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 (cache.set ⟨0, by omega⟩ input) permuted 1 false⟩]) := by
  enter_decl
  set_option maxRecDepth 4096 in
  steps [rate_spec]
  simp only [indexTpl_cache_size]
  apply STHoare.ite_intro
  · intro hcond
    steps [perform_duplex_spec]
  · intro hcond
    simp at hcond
