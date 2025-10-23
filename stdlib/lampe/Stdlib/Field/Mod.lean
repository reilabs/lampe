import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

abbrev toLeBitsCall (f : Nat) (N : BitVec 32) := decomposeToRadix 2 f (by linarith)
  |>.map (fun a => BitVec.ofNat 1 a)
  |>.takeD N.toNat 0

set_option maxHeartbeats 1000000000

theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => r = ⟨toLeBitsCall f.val N, by simp⟩ := by
  enter_decl
  steps
  rename _ => conds
  rcases conds with ⟨h_lt, h_eq⟩

  -- if !unconstrained
  apply STHoare.letIn_intro (Q := fun _ => ⟦bits = ⟨toLeBitsCall f.val N, by simp⟩⟧)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pSlice
    rename pSlice = _ => pSlice_val
    rename pSlice.length < 2  ^32 => pSlice_len
    rename_i N_leq_pSlice_len _
    simp at N_leq_pSlice_len
    have bits_len_eq_N : bits.length = N.toNat := rfl
    have : N.toNat ≤ pSlice.length := by
      rw [BitVec.le_def] at N_leq_pSlice_len
      exact N_leq_pSlice_len
    -- Main loop
    loop_inv nat
      (fun i hlo (hhi : i ≤ N.toNat) => [ok ↦ ⟨Tp.bool,
        N.toNat ≠ pSlice.length ∨
        ∃ j : Fin i,
          (∀ k : Fin j, bits[N.toNat - 1 - k.val] = pSlice[N.toNat - 1 - k.val]) ∧
          bits[N.toNat - 1 - j.val] ≠ pSlice[N.toNat - 1 - j.val] ∧
          pSlice[N.toNat - 1 - j.val] = (1 : BitVec 1)
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
        · congr
          simp_all only [List.length_map, Nat.reducePow, BitVec.toNat_intCast, Int.reducePow,
            EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq, List.getElem_map,
            BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU,
            BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_sub,
            BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one, Nat.add_one_sub_one,
            Nat.add_mod_mod, List.get_eq_getElem, beq_true, Lens.modify, Option.get_some,
            not_true_eq_false, false_or, true_eq_decide_iff]
          -- Here we need to show that if `h₁ : ok = false`, and
          -- `h₂ : bits[N - 1 -i] != pSlice[N - 1 - i]`,
          -- then the invariant holds for i + 1 given i
          -- In this case we take `j = i` as the witness
          rename_i inner_assert
          use ⟨i, Nat.lt_succ_self i⟩
          refine ⟨?_, ?_, ?_⟩
          rcases h₁ with ⟨lens_eq, rest⟩
          · rintro ⟨k, hk⟩
            -- We need to show bits[len - 1 - k] = pSlice[len - 1 - k] for k < i
            -- The negated invariant tells us there's no witness at any position < i
            -- We'll use induction or a direct argument
            sorry
          -- Here we need to use `h₂` to argue that bits[N - 1 - i] != pSlice[N - 1 - i], and
          · intro h_eq
            -- If bits[i] = pSlice[i], and pSlice[i] = 1 (from inner_assert), then bits[i] = 1
            -- But h₂ says bits[i] ≠ 1, giving us a contradiction
            set d := decomposeToRadix 2 p.val (by linarith) with hd
            have h_bound : i < d.length := by
              rcases h₁ with ⟨lens_eq, _⟩
              rw [← lens_eq]
              exact hlo
            -- First, show that bits[complex_index] = 1 using h_eq and inner_assert
            have bits_eq_one : List.Vector.get bits
                ⟨(4294967296 - i + (4294967295 + d.length)) % 4294967296, by
                  rcases h₁ with ⟨lens_eq, _⟩
                  calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
                    _ = d.length - 1 - i := by
                      calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
                        _ = (d.length + (4294967296 - i + 4294967295)) % 4294967296 := by ac_rfl
                        _ = (d.length + 8589934591 - i) % 4294967296 := by congr 2; omega
                        _ = (d.length - 1 - i + 8589934592) % 4294967296 := by omega
                        _ = (d.length - 1 - i) % 4294967296 := by rw [Nat.add_mod]; norm_num
                        _ = d.length - 1 - i := by apply Nat.mod_eq_of_lt; omega
                    _ < BitVec.toNat N := by rw [← lens_eq]; omega
                ⟩ = (1 : BitVec 1) := by
              -- Use h_eq to substitute bits[i] with pSlice[i]
              have idx_eq : (4294967296 - i + (4294967295 + d.length)) % 4294967296 = d.length - 1 - i := by
                calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
                  _ = (d.length + (4294967296 - i + 4294967295)) % 4294967296 := by ac_rfl
                  _ = (d.length + 8589934591 - i) % 4294967296 := by
                    congr 2
                    omega
                  _ = (d.length - 1 - i + 8589934592) % 4294967296 := by omega
                  _ = (d.length - 1 - i) % 4294967296 := by
                    rw [Nat.add_mod]
                    norm_num
                  _ = d.length - 1 - i := by
                    apply Nat.mod_eq_of_lt
                    omega
              rcases h₁ with ⟨lens_eq, _⟩
              -- h_eq tells us bits[d.length - 1 - i] = pSlice[d.length - 1 - i]
              -- inner_assert tells us pSlice[(idx)] = 1 where idx simplifies to d.length - 1 - i
              simp [hd.symm] at h_eq inner_assert
              simp [idx_eq] at inner_assert
              rw [inner_assert] at h_eq
              convert h_eq using 1
              congr 1
              simp [idx_eq]

            exact h₂ bits_eq_one

          -- use the `inner_assert`
          · convert inner_assert using 3
            simp only
            set d := decomposeToRadix 2 p.val (by linarith) with hd
            have h_bound : i < d.length := by
              rcases h₁ with ⟨lens_eq, _⟩
              rw [← lens_eq]
              exact hlo
            conv in _ % 4294967296 =>
              equals d.length - 1 - i =>
                calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
                  _ = (d.length + (4294967296 - i + 4294967295)) % 4294967296 := by ac_rfl
                  _ = (d.length + 8589934591 - i) % 4294967296 := by
                    congr 2
                    norm_num
                    omega
                  _ = (d.length - 1 - i + 8589934592) % 4294967296 := by omega
                  _ = (d.length - 1 - i) % 4294967296 := by
                    rw [Nat.add_mod]
                    norm_num
                  _ = d.length - 1 - i := by
                    apply Nat.mod_eq_of_lt
                    omega
        · congr 1
          simp_all only [List.length_map, Nat.reducePow, BitVec.toNat_intCast, Int.reducePow,
            EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq, List.getElem_map,
            BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
            Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
            decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU,
            BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_sub,
            BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one, Nat.add_one_sub_one,
            Nat.add_mod_mod, List.get_eq_getElem, Bool.not_false, not_true_eq_false, false_or,
            decide_eq_decide]
          -- Here we need to show that if `ok` is false, and `bits[N - 1 -i] == pSlice[N - 1 - i]`,
          -- then the invariant holds for i + 1 given i
          -- In this case we keep the same witness `j` as for `i`
          sorry
      -- Here we need to show that if `ok` is true, then the invariant holds for i + 1 given i
      · congr 2
        rw [eq_iff_iff]
        constructor <;> rintro (len_neq | ⟨⟨j_val, j_prop⟩, ⟨hj₁, hj₂, hj₃⟩⟩)
        · left; exact len_neq
        · right
          use ⟨j_val, Nat.lt_succ_of_lt j_prop⟩
        · left; exact len_neq
        · by_cases h_case : j_val < i
          · right
            use ⟨j_val, h_case⟩
          · simp at h₁
            by_cases len_eq : N.toNat = pSlice.length
            · right
              exact h₁ len_eq
            · left
              exact len_eq
    -- Here is where all the "action" is, have to prove the constraint `ok` holds => `bits` is as
    -- expected
    · steps
      rename_i ok_invariant _
      simp at ok_invariant
      sorry

    -- · intros i hhi hlo
    --   steps
    --   -- If `!ok`
    --   apply STHoare.ite_intro <;> intro h₁ <;> steps
    --   -- If `bits[N.toNat - 1 - i] != pSlice[N.toNat - 1 - i]`
    --   · apply STHoare.ite_intro <;> intro h₂ <;> steps
    --     · simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
    --       List.length_flatMap, List.length_cons, List.length_nil, zero_add, List.map_const',
    --       List.sum_replicate, smul_eq_mul, mul_one, Nat.reducePow, BitVec.toNat_intCast,
    --       Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq,
    --       BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
    --       Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    --       decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU, BitVec.ofNat_toNat,
    --       BitVec.setWidth_eq, BitVec.toNat_sub, BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one,
    --       Nat.add_one_sub_one, Nat.add_mod_mod, List.get_eq_getElem, beq_true, Lens.modify,
    --       Option.get_some, not_true_eq_false, false_or]
    --       -- Need to prove: ∃ j, (∀ k < j, bits match) ∧ (bits differ at j) ∧ (pSlice[j] = 1)
    --       -- Witness: j = i
    --       rename_i h_inv_neg h₂ pSlice_at_i
    --       congr
    --       rw [eq_comm, decide_eq_true]
    --       refine ⟨⟨i, Nat.lt_succ_self i⟩, ?_, ?_, ?_⟩
    --       · -- Goal 1: ∀ k < i, bits[N-1-k] = pSlice[N-1-k]
    --         rcases h₁ with ⟨a, b⟩
    --         rw [← a]
    --         rintro ⟨k, hk⟩
    --         simp
    --         rename pSlice = _ => pSlice_val₂
    --         simp only [List.pure_def] at pSlice_val

    --       · -- Goal 2: bits[N-1-i] ≠ pSlice[N-1-i]
    --         -- This comes from h₂✝ (the condition that bits differ)
    --         sorry
    --       · -- Goal 3: pSlice[N-1-i] = some 1
    --         -- This should follow from pSlice_at_i after index arithmetic
    --         sorry
    --     · simp_all only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
    --       List.length_flatMap, List.length_cons, List.length_nil, zero_add, List.map_const',
    --       List.sum_replicate, smul_eq_mul, mul_one, Nat.reducePow, BitVec.toNat_intCast,
    --       Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq,
    --       BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
    --       Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    --       decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU, BitVec.ofNat_toNat,
    --       BitVec.setWidth_eq, BitVec.toNat_sub, BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one,
    --       Nat.add_one_sub_one, Nat.add_mod_mod, List.get_eq_getElem, Bool.not_false,
    --       not_true_eq_false, false_or]
    --       sorry
    --   · sorry
    -- · sorry

  · intro
    steps
    subst_vars
    rfl

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
