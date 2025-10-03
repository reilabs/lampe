import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Slice
open «std-1.0.0-beta.12»

set_option maxRecDepth 1000

lemma for_each_inv {T Env p f fb l}
    (Inv: List (Tp.denote p T) → SLP (State p))
    (h_inv: ∀(lp: List (Tp.denote p T)) (e: T.denote p), ((lp ++ [e]) <+: l) → STHoare p env (Inv lp) (fb h![e]) (fun _ => Inv (lp ++ [e]))):
    STHoare p env (Inv [] ⋆ [λf ↦ fb]) ((«std-1.0.0-beta.12::slice::for_each».call h![T, Env] h![l, f])) (fun _ => Inv l ⋆ [λf ↦ fb]) := by
  enter_decl
  steps []
  loop_inv nat fun i _ _ => Inv (l.take i) ⋆ [λf ↦ fb]
  · simp
  · intro i ihl ihg
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.get_eq_getElem]
    generalize_proofs
    have := h_inv (l.take i) l[i] $ by
      simp [List.take_prefix]
    steps [STHoare.callLambda_intro (hlam := this)]
    simp only [List.take_append_getElem]
    sl
  steps
  simp_all
  sl

lemma slice_map_inv {T U Env p f fb l}
    (Inv: List (Tp.denote p T) → List (Tp.denote p U) → SLP (State p))
    (h_inv: ∀(ip: List (Tp.denote p T)) (rp: List (Tp.denote p U)) (e: T.denote p), ((ip ++ [e]) <+: l) → STHoare p env (Inv ip rp) (fb h![e]) (fun r => Inv (ip ++ [e]) (rp ++ [r]))):
    STHoare p env (Inv [] [] ⋆ [λf ↦ fb]) ((«std-1.0.0-beta.12::slice::map».call h![T, U, Env] h![l, f])) (fun v => Inv l v ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨U.slice, []⟩] ⋆ [λf ↦ fb] ⋆ Inv [] []) (fun _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [λf ↦ fb] ⋆ Inv l v)
  · steps
    loop_inv nat fun i _ _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [λf ↦ fb] ⋆ Inv (l.take i) v
    · sl
    · simp
    · intro i ihl ihg
      steps
      simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
        zero_le, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem]
      generalize_proofs
      rename U.slice.denote p => v
      have := h_inv (l.take i) v l[i] (by simp [List.take_prefix])
      steps [STHoare.callLambda_intro (hlam := this)]
      simp_all only [List.take_append_getElem, Lens.modify, Option.get_some]
      sl
    · steps
      simp [*]
      sl
  steps
  simp_all
  sl

lemma slice_pure_map {T U Env p f fb func l}
    (h_pure : ∀x, STHoare p env ⟦⟧ (fb h![x]) (fun r => r = func x)):
    STHoare p env [λf ↦ fb] ((«std-1.0.0-beta.12::slice::map».call h![T, U, Env] h![l, f])) (fun v => v = l.map func) := by
  steps [slice_map_inv (Inv := fun i o => o = i.map func)]
  · rfl
  · assumption
  · intros; steps [h_pure]; simp_all

theorem as_array_intro {p T} {N : BitVec 32} {input : List _} (hinput : input.length < 2 ^ 32) (hi : input.length = N) :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::slice::as_array».call h![T, N] h![input])
    fun output => (output : List.Vector (Tp.denote p T) N.toNat) = ⟨input, by
      have : input.length = input.length % 4294967296 := (Nat.mod_eq_of_lt hinput).symm
      simp [←hi, ←this]
    ⟩
  := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => ∃∃v, [array ↦ ⟨Tp.array T N, v⟩] ⋆ (v.toList = input.take i ++ List.replicate (N - i).toNat (Tp.zero p T))
  · sl; simp; rfl
  · simp only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    zero_le]
  · intro i hlo hhi
    steps
    simp_all
    conv in (occs := 1) List.replicate _ =>
      congr
      equals N.toNat - i =>
        sorry
    conv in (occs := 2) List.replicate _ =>
      congr
      equals N.toNat - (i + 1) =>
        sorry
    conv in min i input.length =>
      equals i =>
        sorry
    simp only [tsub_self]
    sorry
  · steps
    apply List.Vector.eq
    simp_all [-List.takeD_succ, List.takeD_eq_take]
    subst_vars; simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow]; omega

  -- sl
  -- · simp; rfl
  -- · simp
  -- · intro i hlo hhi
  --   steps
  --   have : i < 32 := by assumption
  --   have : 32 - i = (31 - i) + 1 := by omega
  --   simp_all only [Int.cast_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
  --     Nat.zero_mod, zero_le, BitVec.reduceToNat, List.replicate_succ, Lens.modify, Lens.get,
  --     Access.modify, BitVec.toNat_ofNatLT, Nat.reduceMod, ↓reduceDIte, Builtin.instCastTpU,
  --     BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.get_eq_getElem,
  --     Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some, Option.get_some,
  --     List.Vector.toList_set, List.length_take, min_eq_left_of_lt, le_refl, List.set_append_right,
  --     tsub_self, List.set_cons_zero, Nat.reduceSubDiff]
  --   rw [List.take_succ_eq_append_getElem]
  --   simp only [List.append_assoc, List.cons_append, List.nil_append]
  --   simp_all
  -- steps
  -- apply List.Vector.eq
  -- simp_all [-List.takeD_succ, List.takeD_eq_take]
