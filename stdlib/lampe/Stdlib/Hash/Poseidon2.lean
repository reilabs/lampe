import «std-1.0.0-beta.25».Extracted
import Lampe
import Lampe.Crypto.Poseidon2
import Stdlib.Default
import Stdlib.Tuple
import Stdlib.Vector

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.25»
open Lampe.Crypto

/-!
Specs for Noir's `std::hash::poseidon2` module.

Since Noir 1.0.0-beta.25 the `Poseidon2` sponge struct (with `new`/`absorb`/`perform_duplex`/
`squeeze`/`hash`) no longer exists; the module only provides `Poseidon2Hasher`, whose `finish_ref`
absorbs the written inputs in `RATE`-sized chunks directly via the `poseidon2_permutation`
builtin. We model that algorithm directly (`chunkState`/`finishDigest`) and prove the `Hasher`
trait methods against it.
-/

abbrev Poseidon2HasherTp : Tp :=
  «std-1.0.0-beta.25::hash::poseidon2::Poseidon2Hasher».tp h![]

abbrev Poseidon2HasherRepr (p : Prime) : Type :=
  Tp.denote p Poseidon2HasherTp

def mkPoseidon2HasherRepr {p} (inputs : List (Fp p)) : Poseidon2HasherRepr p :=
  Tuple.mk
    (p := p)
    (memTps := [Tp.field.vector])
    h![inputs]

private lemma mkPoseidon2HasherRepr_head {p} (inputs : List (Fp p)) :
    Builtin.indexTpl (mkPoseidon2HasherRepr inputs) Member.head = inputs := by
  rfl

private lemma vector_ext_get {α n} {v w : List.Vector α n}
    (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  apply List.Vector.eq
  apply List.ext_get
  · simp
  · intro i hi₁ hi₂
    simpa [List.Vector.get] using h ⟨i, by simpa using hi₁⟩

/-!
## Functional model of `Poseidon2Hasher::finish_ref`

`addToState state xs` adds `xs[j]` to `state[j]` for every valid `j` (with `xs.length ≤ 4` at all
use sites). `chunkState inputs k` is the permutation state after absorbing the first `k` complete
`RATE`-sized (`RATE = 3`) chunks, and `finishDigest` additionally absorbs the tail remainder and
applies the final permutation.
-/

def addToState {p} (state : List.Vector (Fp p) 4) (xs : List (Fp p)) :
    List.Vector (Fp p) 4 :=
  List.Vector.ofFn fun j =>
    if h : j.val < xs.length then state.get j + xs[j.val]'h else state.get j

def initState {p} (len : Nat) : List.Vector (Fp p) 4 :=
  (List.Vector.replicate 4 0).set ⟨3, by decide⟩ (Crypto.Poseidon2.Sponge.noirIV len)

def chunkState {p} (inputs : List (Fp p)) : Nat → List.Vector (Fp p) 4
  | 0 => initState inputs.length
  | k + 1 =>
      Crypto.Poseidon2.noirPermutation4
        (addToState (chunkState inputs k) ((inputs.drop (3 * k)).take 3))

def finishDigest {p} (inputs : List (Fp p)) : Fp p :=
  (Crypto.Poseidon2.noirPermutation4
      (addToState (chunkState inputs (inputs.length / 3))
        (inputs.drop (3 * (inputs.length / 3))))).get ⟨0, by decide⟩

@[simp]
private lemma addToState_nil {p} (state : List.Vector (Fp p) 4) :
    addToState state [] = state := by
  apply vector_ext_get
  intro j
  simp [addToState]

private lemma take_mod_drop_eq {α} (inputs : List α) :
    (inputs.drop (3 * (inputs.length / 3))).take (inputs.length % 3) =
      inputs.drop (3 * (inputs.length / 3)) := by
  apply List.take_of_length_le
  simp only [List.length_drop]
  omega

private lemma addToState_set_step {p} (state : List.Vector (Fp p) 4) (xs : List (Fp p))
    (j : Nat) (hj4 : j < 4) (hjx : j < xs.length) :
    (addToState state (xs.take j)).set ⟨j, hj4⟩
        ((addToState state (xs.take j)).get ⟨j, hj4⟩ + xs[j]'hjx) =
      addToState state (xs.take (j + 1)) := by
  have hjtake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (Nat.le_of_lt hjx)]
  apply vector_ext_get
  intro k
  by_cases hkj : k = (⟨j, hj4⟩ : Fin 4)
  · subst hkj
    rw [List.Vector.get_set_same]
    have hnotlt : ¬ ((j : Nat) < (xs.take j).length) := by omega
    have hlt1 : (j : Nat) < (xs.take (j + 1)).length := by
      simp only [List.length_take]
      omega
    simp only [addToState, List.Vector.get_ofFn, hnotlt, dif_neg, not_false_iff, hlt1, dif_pos]
    congr 1
    simp [List.getElem_take]
  · rw [List.Vector.get_set_of_ne (by simpa [eq_comm] using hkj)]
    have hkvj : (k : Fin 4).val ≠ j := by
      intro h
      exact hkj (Fin.ext h)
    simp only [addToState, List.Vector.get_ofFn, List.length_take]
    by_cases hk : k.val < j
    · have h1 : k.val < min j xs.length := by omega
      have h2 : k.val < min (j + 1) xs.length := by omega
      simp only [h1, h2, dif_pos]
      congr 1
      rw [List.getElem_take, List.getElem_take]
    · have h1 : ¬ (k.val < min j xs.length) := by omega
      have h2 : ¬ (k.val < min (j + 1) xs.length) := by omega
      simp [h1, h2]

theorem default_spec {p}
    : STHoare p env ⟦⟧
        (Lampe.Stdlib.Default.default h![]
          («std-1.0.0-beta.25::hash::poseidon2::Poseidon2Hasher».tp h![]) h![] h![] h![])
        (fun r => r = Tuple.mk h![([] : List (Tp.denote p .field))]) := by
  resolve_trait
  steps
  subst_vars
  rfl

theorem capacity_spec {p}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::poseidon2::CAPACITY».call h![] h![])
        (fun r => r = (1 : U 32)) := by
  enter_decl
  steps
  subst_vars
  rfl

private theorem config_state_size_builtin_spec {p}
    : STHoare p env ⟦⟧
        (.callBuiltin [] (Tp.u 32) Builtin.poseidon2ConfigStateSize h![])
        (fun r => r = (4 : U 32)) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.poseidon2ConfigStateSize rfl () p env h![]

theorem config_state_size_spec {p}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::POSEIDON2_CONFIG_STATE_SIZE».call h![] h![])
        (fun r => r = (4 : U 32)) := by
  enter_decl
  steps [config_state_size_builtin_spec]
  simp_all

theorem rate_spec {p}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::poseidon2::RATE».call h![] h![])
        (fun r => r = (3 : U 32)) := by
  enter_decl
  steps [config_state_size_spec, capacity_spec]
  subst_vars
  rfl

theorem poseidon2_permutation_builtin_spec {p} {state : List.Vector (Fp p) 4}
    : STHoare p env ⟦⟧
        (.callBuiltin [Tp.field.array (4 : U 32)] (Tp.field.array (4 : U 32))
          Builtin.poseidon2Permutation h![state])
        (fun r => r = Crypto.Poseidon2.noirPermutation4 state) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.poseidon2Permutation rfl () p env h![state]

private theorem poseidon2_permutation4_spec' {p} {input : List.Vector (Fp p) 4}
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::poseidon2_permutation».call h![(4 : U 32)] h![input])
        (fun r => r = Crypto.Poseidon2.noirPermutation4 input) := by
  enter_decl
  steps [config_state_size_spec, poseidon2_permutation_builtin_spec]
  assumption

theorem hasher_write_spec {p selfRef}
    {inputs : List (Fp p)}
    {input : Fp p}
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩]
        («std-1.0.0-beta.25::hash::Hasher».write h![] Poseidon2HasherTp h![] h![]
          h![selfRef, input])
        (fun _ => [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr (inputs ++ [input])⟩]) := by
  resolve_trait
  steps

theorem hasher_finish_ref_spec {p selfRef}
    {inputs : List (Fp p)}
    (hlen : inputs.length < 2 ^ 32)
    : STHoare p env
        [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩]
        («std-1.0.0-beta.25::hash::Hasher».finish_ref h![] Poseidon2HasherTp h![] h![]
          h![selfRef])
        (fun r => [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩] ⋆
          ⟦r = finishDigest inputs⟧) := by
  resolve_trait
  steps [rate_spec]
  subst_vars
  apply STHoare.letIn_intro
    (Q := fun _ =>
      [state ↦ ⟨Tp.field.array 4, chunkState inputs (inputs.length / 3)⟩] ⋆
      [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
  ·
    loop_inv nat (fun i _ _ =>
      [state ↦ ⟨Tp.field.array 4, chunkState inputs i⟩] ⋆
      [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
    ·
      -- `0 ≤ len / RATE` loop-bound side goal.
      simp
    ·
      intro i _ hhi
      have hiLt : i < inputs.length / 3 := by
        simpa [mkPoseidon2HasherRepr_head] using hhi
      steps [rate_spec]
      subst_vars
      apply STHoare.letIn_intro
        (Q := fun _ =>
          [state ↦ ⟨Tp.field.array 4,
            addToState (chunkState inputs i) ((inputs.drop (3 * i)).take 3)⟩] ⋆
          [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
      ·
        loop_inv nat (fun j _ _ =>
          [state ↦ ⟨Tp.field.array 4,
            addToState (chunkState inputs i) ((inputs.drop (3 * i)).take j)⟩] ⋆
          [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
        ·
          -- j = 0: `take 0 = []`, `addToState_nil`.
          simp
        ·
          -- `0 ≤ RATE` loop-bound side goal.
          simp
        ·
          intro j _ hj3
          steps [rate_spec]
          have hj3' : j < 3 := by simpa using hj3
          have hj4 : j < 4 := by omega
          have hdm : inputs.length / 3 * 3 ≤ inputs.length := Nat.div_mul_le_self _ _
          have hjx : j < (inputs.drop (3 * i)).length := by
            simp only [List.length_drop]
            omega
          have hlt1 : i * 3 < 4294967296 := by omega
          have hlt2 : i * 3 + j < 4294967296 := by omega
          have hstep := addToState_set_step (chunkState inputs i) (inputs.drop (3 * i)) j hj4 hjx
          congr 1
          rw [← hstep]
          simp only [Builtin.CastTp.cast, BitVec.setWidth_eq, BitVec.toNat_ofNatLT,
            BitVec.toNat_add, BitVec.toNat_mul, mkPoseidon2HasherRepr_head,
            List.get_eq_getElem]
          simp [Lens.modify, Access.modify, hj4, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
            List.getElem_drop, Nat.mul_comm 3 i]
          rfl
      ·
        intro _
        steps [poseidon2_permutation4_spec']
  ·
    intro _
    -- `absorbed := (len / RATE) * RATE`, then the tail loop, then the final permutation.
    steps [rate_spec]
    subst_vars
    apply STHoare.letIn_intro
      (Q := fun _ =>
        [state ↦ ⟨Tp.field.array 4,
          addToState (chunkState inputs (inputs.length / 3))
            (inputs.drop (3 * (inputs.length / 3)))⟩] ⋆
        [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
    ·
      loop_inv nat (fun i _ _ =>
        [state ↦ ⟨Tp.field.array 4,
          addToState (chunkState inputs (inputs.length / 3))
            ((inputs.drop (3 * (inputs.length / 3))).take i)⟩] ⋆
        [selfRef ↦ ⟨Poseidon2HasherTp, mkPoseidon2HasherRepr inputs⟩])
      ·
        -- i = 0: `take 0 = []`, `addToState_nil`.
        simp
      ·
        -- `0 ≤ len % RATE` loop-bound side goal.
        simp
      ·
        -- postcondition: taking `len % RATE` of the tail is the whole tail.
        simp [mkPoseidon2HasherRepr_head, BitVec.toNat_umod, BitVec.toNat_ofNatLT,
          take_mod_drop_eq]
      ·
        intro i _ hiRem
        steps
        have hiRem' : i < inputs.length % 3 := by
          simpa [mkPoseidon2HasherRepr_head, BitVec.toNat_umod, BitVec.toNat_ofNatLT]
            using hiRem
        have hi4 : i < 4 := by omega
        have hdm : inputs.length / 3 * 3 ≤ inputs.length := Nat.div_mul_le_self _ _
        have hix : i < (inputs.drop (3 * (inputs.length / 3))).length := by
          simp only [List.length_drop]
          omega
        have hlt1 : inputs.length / 3 * 3 < 4294967296 := by omega
        have hlt2 : inputs.length / 3 * 3 + i < 4294967296 := by omega
        have hstep := addToState_set_step (chunkState inputs (inputs.length / 3))
          (inputs.drop (3 * (inputs.length / 3))) i hi4 hix
        congr 1
        rw [← hstep]
        simp only [Builtin.CastTp.cast, BitVec.setWidth_eq, BitVec.toNat_ofNatLT,
          BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, mkPoseidon2HasherRepr_head,
          List.get_eq_getElem]
        simp [Lens.modify, Access.modify, hi4, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2,
          List.getElem_drop, Nat.mul_comm 3 (inputs.length / 3)]
        rfl
    ·
      intro _
      steps [poseidon2_permutation4_spec']
      subst_vars
      rfl

theorem hasher_finish_spec {p}
    {inputs : List (Fp p)}
    (hlen : inputs.length < 2 ^ 32)
    : STHoare p env ⟦⟧
        («std-1.0.0-beta.25::hash::Hasher».finish h![] Poseidon2HasherTp h![] h![]
          h![mkPoseidon2HasherRepr inputs])
        (fun r => r = finishDigest inputs) := by
  resolve_trait
  steps [hasher_finish_ref_spec hlen]
  subst_vars
  rfl

end Lampe.Stdlib.Hash.Poseidon2
