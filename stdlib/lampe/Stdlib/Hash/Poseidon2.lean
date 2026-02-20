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

/-- Absorb a list of field elements into the sponge, returning (cache, state, cache_size).
    When cache_size = 3, triggers duplex before absorbing. -/
def spongeAbsorb {p : Prime}
    (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) : List (Fp p) →
    List.Vector (Fp p) 3 × List.Vector (Fp p) 4 × U 32
  | [] => (cache, state, cache_size)
  | x :: xs =>
    if cache_size = 3 then
      let permuted := Builtin.poseidon2PermFn p 4 (mixCacheIntoState cache state 3)
      spongeAbsorb (cache.set ⟨0, by omega⟩ x) permuted 1 xs
    else if h : cache_size.toNat < 3 then
      spongeAbsorb (cache.set ⟨cache_size.toNat, h⟩ x) state (cache_size + 1) xs
    else
      (cache, state, cache_size)  -- unreachable when cache_size.toNat ≤ 3

private lemma bv32_one_toNat : (1 : BitVec 32).toNat = 1 := by native_decide

private lemma cache_size_add_one_le {cache_size : U 32} (h : cache_size.toNat < 3) :
    (cache_size + 1 : BitVec 32).toNat ≤ 3 := by
  rw [BitVec.toNat_add, bv32_one_toNat]; omega

lemma spongeAbsorb_cache_size_le
    (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) (h_cs : cache_size.toNat ≤ 3) (l : List (Fp p)) :
    (spongeAbsorb cache state cache_size l).2.2.toNat ≤ 3 := by
  induction l generalizing cache state cache_size with
  | nil => simp [spongeAbsorb]; exact h_cs
  | cons x xs ih =>
    simp only [spongeAbsorb]
    split
    · apply ih; native_decide
    · split
      · exact ih _ _ _ (cache_size_add_one_le ‹_›)
      · simp; exact h_cs

lemma spongeAbsorb_append
    (cache : List.Vector (Fp p) 3) (state : List.Vector (Fp p) 4)
    (cache_size : U 32) (h_cs : cache_size.toNat ≤ 3) (l1 l2 : List (Fp p)) :
    spongeAbsorb cache state cache_size (l1 ++ l2) =
      let (c, s, cs) := spongeAbsorb cache state cache_size l1
      spongeAbsorb c s cs l2 := by
  induction l1 generalizing cache state cache_size with
  | nil => simp [spongeAbsorb]
  | cons x xs ih =>
    simp only [List.cons_append, spongeAbsorb]
    split
    · exact ih _ _ _ (by native_decide)
    · split
      · exact ih _ _ _ (cache_size_add_one_le ‹_›)
      · rename_i h1 h2
        exfalso
        have : cache_size.toNat ≠ 3 := by
          intro heq; exact h1 (BitVec.eq_of_toNat_eq (by simp_all))
        omega

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

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem absorb_spec {r : Ref}
    {cache : List.Vector (Fp p) 3} {state : List.Vector (Fp p) 4}
    {cache_size : U 32} {input : Fp p}
    (h_cs : cache_size.toNat ≤ 3) :
    let sa := spongeAbsorb cache state cache_size [input]
    STHoare p env
    [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 cache state cache_size false⟩]
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::absorb».call h![] h![r, input])
    (fun _ => [r ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 sa.1 sa.2.1 sa.2.2 false⟩]) := by
  by_cases h : cache_size = 3
  · subst h
    simp only [spongeAbsorb]
    exact absorb_spec_full
  · have h_lt : cache_size.toNat < 3 := by
      have : cache_size.toNat ≠ 3 :=
        fun heq => h (BitVec.eq_of_toNat_eq (by simp_all))
      omega
    simp only [spongeAbsorb, h, h_lt, ↓reduceDIte]
    exact absorb_spec_not_full h_lt

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem hash_internal_spec {n : U 32} {input : List.Vector (Fp p) n.toNat}
    {in_len : U 32} {is_variable_length : Bool}
    (h_len : in_len.toNat ≤ n.toNat) :
    let iv : Fp p := (in_len.toNat : Fp p) * (18446744073709551616 : Fp p)
    let init_cache : List.Vector (Fp p) 3 := ⟨[0, 0, 0], rfl⟩
    let init_state : List.Vector (Fp p) 4 := ⟨[0, 0, 0, iv], rfl⟩
    let elems := (input.toList.take in_len.toNat) ++
                 (if is_variable_length then [(1 : Fp p)] else [])
    let (fc, fs, fcs) := spongeAbsorb init_cache init_state (0 : U 32) elems
    let squeezed := Builtin.poseidon2PermFn p 4 (mixCacheIntoState fc fs fcs)
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::hash_internal».call h![n] h![input, in_len, is_variable_length])
    (fun result => result = squeezed.get ⟨0, by simp [BitVec.toNat]⟩) := by
  enter_decl
  set_option maxRecDepth 4096 in
  steps [new_spec]
  subst_vars
  loop_inv nat fun i _ _ =>
    let sa := spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
      ⟨[0, 0, 0, Builtin.CastTp.cast in_len * ↑18446744073709551616], rfl⟩
      (0 : U 32) (input.toList.take (min i in_len.toNat))
    [sponge ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
      mkPoseidon2 sa.1 sa.2.1 sa.2.2 false⟩]
  · simp [spongeAbsorb] -- base case
  · simp -- well-formedness
  · intro i hlo hhi -- step case
    steps
    apply STHoare.ite_intro
    · intro hcond -- true: i < in_len
      have h_cs : (spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
        ⟨[0, 0, 0, Builtin.CastTp.cast in_len * ↑18446744073709551616], rfl⟩
        (0 : U 32) (input.toList.take (min i in_len.toNat))).2.2.toNat ≤ 3 :=
        spongeAbsorb_cache_size_le _ _ _ (by native_decide) _
      steps [absorb_spec h_cs]
      simp only [decide_eq_true_iff, BitVec.lt_def, BitVec.toNat_ofNatLT] at hcond
      have h_min_i : min i in_len.toNat = i := Nat.min_eq_left (by omega)
      have h_min_succ : min (i + 1) in_len.toNat = i + 1 := Nat.min_eq_left (by omega)
      simp only [h_min_i, h_min_succ]
      congr 1; congr 1
      all_goals {
        have h_i_lt : i < input.toList.length := by simpa using hhi
        have h_take : input.toList.take (i + 1) = input.toList.take i ++ [input.toList.get ⟨i, h_i_lt⟩] := by
          rw [List.take_succ]; simp [List.getElem?_eq_getElem h_i_lt]
        rw [h_take, spongeAbsorb_append _ _ _ (by native_decide) _ _]
        simp [List.Vector.get_eq_get_toList]
      }
    · intro hcond -- false: i ≥ in_len
      steps
      have h_ge : in_len.toNat ≤ i := by
        simp only [decide_eq_false_iff_not, BitVec.not_lt, BitVec.le_def] at hcond
        simp [BitVec.toNat_ofNatLT] at hcond; exact hcond
      simp [Nat.min_eq_right h_ge, Nat.min_eq_right (show in_len.toNat ≤ i + 1 from by omega)]
  · -- continuation
    cases is_variable_length with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil]
      apply STHoare.letIn_intro (Q := fun _ =>
        let sa := spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
          ⟨[0, 0, 0, Builtin.CastTp.cast in_len * ↑18446744073709551616], rfl⟩
          (0 : U 32) (input.toList.take (min (BitVec.toNat ↑input.length) in_len.toNat))
        [sponge ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 sa.1 sa.2.1 sa.2.2 false⟩])
      · apply STHoare.iteFalse_intro
        steps
      · intro _
        steps [squeeze_spec]
        subst_vars
        simp_all [Builtin.CastTp.cast, BitVec.toNat_ofNatLT]
    | true =>
      simp only [↓reduceIte]
      apply STHoare.letIn_intro (Q := fun _ =>
        let sa := spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
          ⟨[0, 0, 0, Builtin.CastTp.cast in_len * ↑18446744073709551616], rfl⟩
          (0 : U 32) (input.toList.take (min (BitVec.toNat (↑input.length : U 32)) in_len.toNat) ++ [(1 : Fp p)])
        [sponge ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
          mkPoseidon2 sa.1 sa.2.1 sa.2.2 false⟩])
      · apply STHoare.iteTrue_intro
        have h_cs : (spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
          ⟨[0, 0, 0, Builtin.CastTp.cast in_len * ↑18446744073709551616], rfl⟩
          (0 : U 32) (input.toList.take (min (BitVec.toNat (↑input.length : U 32)) in_len.toNat))).2.2.toNat ≤ 3 :=
          spongeAbsorb_cache_size_le _ _ _ (by native_decide) _
        steps [absorb_spec h_cs]
        congr 1; congr 1
        all_goals simp [spongeAbsorb_append]
      · intro _
        steps [squeeze_spec]
        subst_vars
        simp_all [Builtin.CastTp.cast, BitVec.toNat_ofNatLT]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem hash_spec {n : U 32} {input : List.Vector (Fp p) n.toNat}
    {message_size : U 32}
    (h_len : message_size.toNat ≤ n.toNat) :
    let iv : Fp p := (message_size.toNat : Fp p) * (18446744073709551616 : Fp p)
    let init_cache : List.Vector (Fp p) 3 := ⟨[0, 0, 0], rfl⟩
    let init_state : List.Vector (Fp p) 4 := ⟨[0, 0, 0, iv], rfl⟩
    let is_variable_length := message_size != n
    let elems := (input.toList.take message_size.toNat) ++
                 (if is_variable_length then [(1 : Fp p)] else [])
    let (fc, fs, fcs) := spongeAbsorb init_cache init_state (0 : U 32) elems
    let squeezed := Builtin.poseidon2PermFn p 4 (mixCacheIntoState fc fs fcs)
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::hash::poseidon2::Poseidon2::hash».call h![n] h![input, message_size])
    (fun result => result = squeezed.get ⟨0, by simp [BitVec.toNat]⟩) := by
  enter_decl
  steps [hash_internal_spec h_len]
  subst_vars
  simp [bne_iff_ne]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem finish_spec {s : List (Fp p)} :
    let iv : Fp p := (s.length : Fp p) * (18446744073709551616 : Fp p)
    let init_cache : List.Vector (Fp p) 3 := ⟨[0, 0, 0], rfl⟩
    let init_state : List.Vector (Fp p) 4 := ⟨[0, 0, 0, iv], rfl⟩
    let (fc, fs, fcs) := spongeAbsorb init_cache init_state (0 : U 32) s
    let squeezed := Builtin.poseidon2PermFn p 4 (mixCacheIntoState fc fs fcs)
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::hash::Hasher».finish h![]
      («std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher».tp h![])
      h![] h![] h![(s, ())])
    (fun result => result = squeezed.get ⟨0, by simp [BitVec.toNat]⟩) := by
  resolve_trait
  set_option maxRecDepth 4096 in
  steps [new_spec]
  loop_inv nat fun i _ _ =>
    let sa := spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
      ⟨[0, 0, 0, iv], rfl⟩
      (0 : U 32) (s.take i)
    [sponge ↦ ⟨«std-1.0.0-beta.12::hash::poseidon2::Poseidon2».tp h![],
      mkPoseidon2 sa.1 sa.2.1 sa.2.2 false⟩]
  · simp [spongeAbsorb] -- base case
  · intro i hlo hhi -- step case
    simp only [Builtin.indexTpl, «std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher»,
      BitVec.toNat_ofNatLT] at hhi
    have h_cs : (spongeAbsorb (p := p) ⟨[0, 0, 0], rfl⟩
      ⟨[0, 0, 0, iv], rfl⟩
      (0 : U 32) (s.take i)).2.2.toNat ≤ 3 :=
      spongeAbsorb_cache_size_le _ _ _ (by native_decide) _
    steps [absorb_spec h_cs]
    have h_take : s.take (i + 1) = s.take i ++ [s.get ⟨i, hhi⟩] := by
      rw [List.take_succ]; simp [List.getElem?_eq_getElem hhi]
    congr 1; congr 1
    all_goals {
      rw [h_take, spongeAbsorb_append _ _ _ (by native_decide) _ _]
      simp [Builtin.indexTpl, «std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher»,
        Builtin.CastTp.cast, BitVec.toNat_ofNatLT]
    }
  · steps [squeeze_spec] -- continuation
    subst_vars
    simp only [Builtin.indexTpl, «std-1.0.0-beta.12::hash::poseidon2::Poseidon2Hasher»,
      Builtin.CastTp.cast, BitVec.toNat_ofNatLT, List.take_length]
    norm_cast
