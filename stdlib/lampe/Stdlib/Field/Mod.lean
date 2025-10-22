import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

abbrev toLeBitsCall (f : Nat) (N : BitVec 32) := decomposeToRadix 2 f (by linarith)
  |>.flatMap (fun a => [BitVec.ofNat 1 a])
  |>.takeD N.toNat 0

theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => r = ⟨toLeBitsCall f.val N, by simp⟩ := by
  enter_decl
  steps
  rename _ => conds
  rcases conds with ⟨h_lt, h_eq⟩

  -- if !unconstrained
  apply STHoare.letIn_intro
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pSlice
    rename pSlice = _ => pSlice_val
    rename pSlice.length < 2  ^32 => pSlice_len
    rename_i N_leq_pSlice_len _
    simp at N_leq_pSlice_len
    have bits_len_eq_N : bits.length = N.toNat := rfl
    -- Main loop
    loop_inv nat
      (fun i hlo (hhi : i ≤ N.toNat) => [ok ↦ ⟨Tp.bool,
        N.toNat ≠ pSlice.length ∨
        ∃ j : Fin i,
          (∀ k : Fin j, bits[N.toNat - 1 - k.val]? = pSlice[N.toNat - 1 - k.val]?) ∧
          bits[N.toNat - 1 - j.val]? ≠ pSlice[N.toNat - 1 - j.val]? ∧
          pSlice[N.toNat - 1 - j.val]? = some (1 : BitVec 1)
      ⟩])
    · congr
      rw [eq_iff_iff]
      constructor
      · intro h
        left
        rw [bits_len_eq_N] at h
        apply_fun BitVec.toNat (w := 32) at h
        · simp only [BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          BitVec.toNat_ofNatLT, ne_eq] at h
          exact h
        · exact fun _ _  => BitVec.toNat_inj.mp
      · rintro (h | ⟨⟨j_val, j_lt⟩, hj₁, hj₂, hj₃⟩)
        · rw [bits_len_eq_N]
          intro hh
          simp at hh
          apply h
          rw [hh]
          simp
        · simp at j_lt
    · simp
    · intros i hhi hlo
      steps
      -- If `!ok`
      apply STHoare.ite_intro <;> intro h₁ <;> steps
      -- If `bits[N.toNat - 1 - i] != pSlice[N.toNat - 1 - i]`
      · apply STHoare.ite_intro <;> intro h₂ <;> steps
        · simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
          List.length_flatMap, List.length_cons, List.length_nil, zero_add, List.map_const',
          List.sum_replicate, smul_eq_mul, mul_one, Nat.reducePow, BitVec.toNat_intCast,
          Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq,
          BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, BitVec.toNat_sub, BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one,
          Nat.add_one_sub_one, Nat.add_mod_mod, List.get_eq_getElem, beq_true, Lens.modify,
          Option.get_some, not_true_eq_false, false_or]
          congr
          sorry
        · simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
          List.length_flatMap, List.length_cons, List.length_nil, zero_add, List.map_const',
          List.sum_replicate, smul_eq_mul, mul_one, Nat.reducePow, BitVec.toNat_intCast,
          Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq,
          BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU, BitVec.ofNat_toNat,
          BitVec.setWidth_eq, BitVec.toNat_sub, BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one,
          Nat.add_one_sub_one, Nat.add_mod_mod, List.get_eq_getElem, Bool.not_false,
          not_true_eq_false, false_or]
          sorry
      · sorry
    · sorry

  -- Prove postcondition using known facts about `composeFromRadix` and `decomposeToRadix`
  · intro; steps
    sorry
    sorry

theorem to_le_radix_intro (radix_gt : radix > 1 := by bv_decide) :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_radix».call h![N] h![f, radix])
    fun r => r = ⟨decomposeToRadix radix.toNat f.val (by assumption) |>.takeD N.toNat 0, by simp⟩ := by
  sorry
  -- enter_decl
  -- steps
  -- fapply STHoare.letIn_intro
  -- · exact fun _ => ⟦⟧
  -- · apply STHoare.iteTrue_intro
  --   steps
  -- intro
  -- steps
  -- rename_i _ _ v_eq
  -- exact v_eq

theorem to_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 256 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  sorry
  -- enter_decl
  -- steps
  -- steps [to_le_radix_intro (N := N) (f := f) (radix := 256)]
  -- fapply STHoare.letIn_intro
  -- · exact fun _ => ⟦⟧
  -- · apply STHoare.iteTrue_intro
  --   steps
  --   simp_all
  --   loop_inv nat
  --     (fun _ _ _ => ∃∃b, ([ok ↦ ⟨Tp.bool, b⟩]))
  --   rotate_left
  --   simp
  --   exact ⟦⟧
  --   rotate_right
  --   simp
  --   apply SLP.exists_intro_r
  --   exact SLP.entails_self

  --   -- loop body
  --   intros i hlo hhi
  --   steps
  --   apply STHoare.ite_intro
  --   · intro h₁
  --     steps
  --     apply STHoare.ite_intro
  --     · intro h₂
  --       steps
  --     · intro h₂
  --       steps
  --   · intro
  --     steps
  --   steps
  -- intro v
  -- steps
  -- simp_all
