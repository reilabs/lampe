import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

abbrev toLeBitsCall (f : Nat) (N : BitVec 32) := decomposeToRadix 2 f (by linarith)
  |>.map (fun a => BitVec.ofNat 1 a)
  |>.takeD N.toNat 0

set_option maxHeartbeats 1000000000

-- Helper lemma for index calculation in to_le_bits proof
private lemma complex_index_eq (i : Nat) (d_len : Nat) (h : i < d_len) (h_len : d_len < 4294967296) :
    (4294967296 - i + (4294967295 + d_len)) % 4294967296 = d_len - 1 - i := by
  calc (4294967296 - i + (4294967295 + d_len)) % 4294967296
    _ = (d_len + (4294967296 - i + 4294967295)) % 4294967296 := by ac_rfl
    _ = (d_len + 8589934591 - i) % 4294967296 := by congr 2; omega
    _ = (d_len - 1 - i + 8589934592) % 4294967296 := by omega
    _ = (d_len - 1 - i) % 4294967296 := by rw [Nat.add_mod]; norm_num
    _ = d_len - 1 - i := by apply Nat.mod_eq_of_lt; omega

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
    rename_i N_leq_pSlice_len
    have bits_len_eq_N : bits.length = N.toNat := rfl
    have : N.toNat ≤ pSlice.length := by
      simp at N_leq_pSlice_len
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
            suffices ∀ k' < i, bits[N.toNat - 1 - k'] = pSlice[N.toNat - 1 - k'] by
              have := this k hk
              simp only [lens_eq, pSlice_val, List.getElem_map] at this ⊢
              exact this

            intro k'
            refine Nat.strong_induction_on k' fun m ih hm => ?_

            have h_all_match : ∀ j < m, bits[N.toNat - 1 - j] = pSlice[N.toNat - 1 - j] := by
              intro j hj
              have : j < i := Nat.lt_trans hj hm
              exact ih j hj this

            specialize rest ⟨m, hm⟩
            have : (∀ (k : Fin m), bits[BitVec.toNat N - 1 - ↑k] =
              BitVec.ofNat 1 (decomposeToRadix 2 p.natVal Builtin.fModLeBits._proof_1)[BitVec.toNat N - 1 - ↑k]) := by
              intro ⟨k_val, hk_val⟩
              -- Use h_all_match which says bits[N-1-k] = pSlice[N-1-k]
              have := h_all_match k_val hk_val
              -- Rewrite pSlice using pSlice_val
              simp only [pSlice_val, List.getElem_map] at this
              exact this
            specialize rest this

            by_contra h_neq

            simp [pSlice_val] at h_neq
            specialize rest h_neq

            set dTRp := decomposeToRadix 2 p.natVal Builtin.fModLeBits._proof_1 with hdTRp

            have pSlice_m_eq_zero : BitVec.ofNat 1 dTRp[BitVec.toNat N - 1 - m] = 0#1 := by
              -- pSlice[m] is a 1-bit value, so it's either 0 or 1
              -- rest says it's not 1, so it must be 0
              have : BitVec.toNat (BitVec.ofNat 1 dTRp[BitVec.toNat N - 1 - m]) < 2 := by
                have := BitVec.isLt (BitVec.ofNat 1 dTRp[BitVec.toNat N - 1 - m])
                simp at this
                exact this
              interval_cases h_case : BitVec.toNat (BitVec.ofNat 1 dTRp[BitVec.toNat N - 1 - m])
              · apply BitVec.eq_of_toNat_eq
                simpa using h_case
              · exfalso
                apply rest
                apply BitVec.eq_of_toNat_eq
                simpa using h_case

            -- Now we have pSlice[m] = 0 and bits[m] ≠ pSlice[m], so bits[m] = 1
            have bits_m_eq_one : bits[BitVec.toNat N - 1 - m] = 1#1 := by
              have bits_neq_zero : bits[BitVec.toNat N - 1 - m] ≠ 0#1 := by
                rw [pSlice_m_eq_zero] at h_neq
                exact h_neq
              -- bits is a 1-bit value, so it's either 0 or 1
              have bits_bound : BitVec.toNat bits[BitVec.toNat N - 1 - m] < 2 := by
                have := BitVec.isLt bits[BitVec.toNat N - 1 - m]
                simp at this
                exact this
              interval_cases h_case : BitVec.toNat bits[BitVec.toNat N - 1 - m]
              · exfalso
                apply bits_neq_zero
                apply_fun BitVec.toNat
                convert h_case
                exact fun _ _  => BitVec.toNat_inj.mp
              · apply BitVec.eq_of_toNat_eq
                simpa using h_case

            sorry

          -- Here we need to use `h₂` to argue that `bits[N - 1 - i] != pSlice[N - 1 - i]`, and
          · intro h_eq
            set d := decomposeToRadix 2 p.natVal (by linarith) with hd
            have h_bound : i < d.length := by
              rcases h₁ with ⟨lens_eq, _⟩
              rw [← lens_eq]
              exact hlo
            have bits_eq_one : List.Vector.get bits
                ⟨(4294967296 - i + (4294967295 + d.length)) % 4294967296, by
                  rcases h₁ with ⟨lens_eq, _⟩
                  calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
                    _ = d.length - 1 - i := complex_index_eq i d.length h_bound pSlice_len
                    _ < BitVec.toNat N := by rw [← lens_eq]; omega
                ⟩ = (1 : BitVec 1) := by
              have idx_eq : (4294967296 - i + (4294967295 + d.length)) % 4294967296 = d.length - 1 - i :=
                complex_index_eq i d.length h_bound pSlice_len
              rcases h₁ with ⟨lens_eq, _⟩
              simp [hd.symm] at h_eq inner_assert
              simp [idx_eq] at inner_assert
              rw [inner_assert] at h_eq
              convert h_eq using 1
              congr 1
              simp [idx_eq]

            exact h₂ bits_eq_one

          -- Here we need to use the `inner_assert`
          · convert inner_assert using 3
            simp only
            set d := decomposeToRadix 2 p.natVal (by linarith) with hd
            have h_bound : i < d.length := by
              rcases h₁ with ⟨lens_eq, _⟩
              rw [← lens_eq]
              exact hlo
            conv in _ % 4294967296 =>
              rw [complex_index_eq i d.length h_bound pSlice_len]
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
          constructor
          · rintro ⟨⟨j_val, hj_prop⟩, hj₁, hj₂, hj₃⟩
            use ⟨j_val, Nat.lt_succ_of_lt hj_prop⟩, hj₁, hj₂, hj₃
          · rintro ⟨⟨j_val, hj_prop⟩, hj₁, hj₂, hj₃⟩
            by_cases h_case : j_val < i
            · use ⟨j_val, h_case⟩, hj₁, hj₂, hj₃
            · exfalso
              apply hj₂
              convert h₂ using 2
              · congr 1
                set d := decomposeToRadix 2 p.natVal (by linarith) with hd
                have h_bound : j_val < d.length := by
                  rw [← h₁.1]
                  omega
                convert complex_index_eq j_val d.length h_bound pSlice_len |>.symm
                omega
              · congr 1
                set d := decomposeToRadix 2 p.natVal (by linarith) with hd
                have h_bound : j_val < d.length := by
                  rw [← h₁.1]
                  omega
                convert complex_index_eq j_val d.length h_bound pSlice_len |>.symm
                omega
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
    -- expected. This should follow from the
    · steps
      rename_i ok_invariant _
      simp at ok_invariant
      sorry

  -- wrap it up
  · intro
    steps
    subst_vars
    rfl

theorem to_le_radix_intro (radix_gt : radix > 1 := by bv_decide) :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_radix».call h![N] h![f, radix])
    fun r => r = ⟨decomposeToRadix radix.toNat f.val (by assumption) |>.takeD N.toNat 0, by simp⟩ := by
  sorry

theorem to_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 256 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  sorry
