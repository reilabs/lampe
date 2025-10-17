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

theorem as_array_spec {p T N input}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::slice::as_array».call h![T, N] h![input])
    (fun r => r.toList = input) := by
  enter_decl
  steps
  loop_inv nat fun i hlo hhi => ∃∃v, [array ↦ ⟨T.array N, v⟩] ⋆ (v.toList.take i = input.take i)
  · sl; simp
  · simp
  · intro i _ _
    steps
    simp_all only [beq_true, decide_eq_true_eq, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, Lens.modify, Lens.get, Access.modify,
      BitVec.toNat_ofNatLT, ↓reduceDIte, Builtin.instCastTpU, BitVec.natCast_eq_ofNat,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, List.get_eq_getElem, Option.bind_eq_bind,
      Option.bind_some, Option.bind_fun_some, Option.get_some, List.Vector.toList_set]
    rename_i take_of_vec_eq_input
    rw [List.take_succ]
    rw [List.take_set]
    rw [take_of_vec_eq_input]
    simp_all only [Lens.modify, Lens.get, Access.modify, BitVec.toNat_ofNatLT, ↓reduceDIte,
      Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      List.get_eq_getElem, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.isSome_some, List.length_set, List.Vector.toList_length, getElem?_pos,
      List.getElem_set_self, Option.toList_some]

    have : i < input.length := by simp_all
    have h : (List.take i input).set i input[i] = List.take i input := by
      rw [List.set_eq_of_length_le (by simp_all)]
    rw [h, List.take_append_getElem]

  steps
  rename_i a v _
  subst_vars
  have h1 : input.length = BitVec.toNat N := by aesop
  have h2 : v.toList.length = BitVec.toNat N := by simp_all
  conv at a =>
    congr
    · arg 1; rw [←h2]
    · rw [←h1]

  rw [List.take_length] at a
  simp_all 

