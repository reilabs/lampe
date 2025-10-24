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

-- pub fn to_le_bits<let N: u32>(self: Self) -> [u1; N] {
--     // docs:end:to_le_bits
--     let bits = __to_le_bits(self);
--
--     if !is_unconstrained() {
--         // Ensure that the byte decomposition does not overflow the modulus
--         let p = modulus_le_bits();
--         assert(bits.len() <= p.len());
--         let mut ok = bits.len() != p.len();
--         for i in 0..N {
--             if !ok {
--                 if (bits[N - 1 - i] != p[N - 1 - i]) {
--                     assert(p[N - 1 - i] == 1);
--                     ok = true;
--                 }
--             }
--         }
--         assert(ok);
--     }
--     bits
-- }

set_option Lampe.pp.Expr true in 
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
    rename pSlice.length < 2^32 => pSlice_len
    rename_i N_leq_pSlice_len _
    simp at N_leq_pSlice_len
    have bits_len_eq_N : bits.length = N.toNat := rfl
    have : N.toNat ≤ pSlice.length := by
      rw [BitVec.le_def] at N_leq_pSlice_len
      exact N_leq_pSlice_len

    -- Abstract out the computation of the 'ok' value for the loop invariant
    let ok_val_at := fun ix (hhi : ix ≤ N.toNat) =>
      -- The initial value of ok is as follows
      let initial_ok := N.toNat ≠ pSlice.length

      -- If ok is FALSE then a check is made which must hold for 
      let loop_body_check := ∃j : Fin ix, 
        let prev_bits_eq := ∀k : Fin j, bits[N.toNat - 1 - k.val] = pSlice[N.toNat - 1 - k.val]
        let current_bit_ne := bits[N.toNat - 1 - j.val] ≠ pSlice[N.toNat - 1 - j.val]
        let assert := pSlice[N.toNat - 1 - j.val] = 1

        prev_bits_eq ∧ current_bit_ne ∧ assert

      -- If ok is TRUE then the loop is a no-op.
      -- So it is an or
      initial_ok ∨ loop_body_check

    -- Main loop
    loop_inv nat (fun i hlo (hhi : i ≤ N.toNat) => [ok ↦ ⟨Tp.bool, ok_val_at i hhi⟩])
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
    · intros i hlo hhi
      steps
      -- If `!ok`
      apply STHoare.ite_intro <;> intro h₁ <;> steps
      -- If `bits[N.toNat - 1 - i] != pSlice[N.toNat - 1 - i]`
      · apply STHoare.ite_intro <;> intro h₂ <;> steps
        · congr

          generalize dp_def : decomposeToRadix 2 p.natVal Builtin.fModLeBits._proof_1 = dp at *
          simp_all only [ok_val_at, List.length_map, Lens.modify, EuclideanDomain.zero_mod,
            Int.toNat_zero, zero_le, ne_eq, List.getElem_map, BitVec.ofNat_toNat, decide_not,
            Bool.decide_or, Bool.not_or, Bool.not_not, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_exists, not_and, 
            not_true_eq_false, beq_true, true_eq_decide_iff, false_or, Builtin.instCastTpU,
            Option.get_some, BitVec.natCast_eq_ofNat, BitVec.setWidth_eq, BitVec.toNat_ofNatLT,
            Int.reduceMod, Int.toNat_one, Nat.add_one_sub_one, Nat.add_mod_mod, List.get_eq_getElem]

          -- Here we need to show that if `h₁ : ok = false`, and
          -- `h₂ : bits[N - 1 -i] != pSlice[N - 1 - i]`,
          -- then the invariant holds for i + 1 given i
          -- In this case we take `j = i` as the witness
          rename_i inner_assert
          use ⟨i, Nat.lt_succ_self i⟩
          refine ⟨?_, ?_, ?_⟩
          rcases h₁ with ⟨lengths_eq, rest⟩
          · rintro ⟨k, hk⟩

            -- We need to show `bits[N.toNat - 1 - k] = pSlice[N.toNat - 1 - k]` for all k < i
            --
            -- The proof strategy: We know from h₁ that `ok` was false at iteration i,
            -- meaning NO witness j < i exists such that:
            --   - All positions k < j match, AND
            --   - Position j differs, AND
            --   - pSlice[j] = 1
            --
            -- We're now showing that i IS such a witness (from h₂ and inner_assert).
            -- This means all positions k < i must match, otherwise there would be an earlier witness.
            --
            -- Formally: If any k < i didn't match, let k_min be the smallest such k.
            -- Then k_min would be a witness (all positions before it match vacuously or by minimality,
            -- k_min differs by assumption, and we can show pSlice[k_min] = 1 from the field constraint).
            -- This contradicts that the invariant was false.
            
            rename_i v
            generalize ib_def : @BitVec.ofNatLT 32 i (by linarith) = ib at *
            rename_i v₀ v₁ v₂ 
            simp only [Builtin.instCastTpU] at v₀ v₁ v₂
            simp only [BitVec.toNat_sub_of_le v] at inner_assert h₂ v₀ v₁ v₂ 

            rename BitVec.ofInt 32 1 ≤ N => one_le_n
            conv at inner_assert => enter [1, 2, 2, 1]; apply BitVec.toNat_sub_of_le one_le_n
            conv at h₂ => enter [1, 1, 2, 1, 1]; apply BitVec.toNat_sub_of_le one_le_n
            conv at v₀ => enter [1, 1, 1, 1]; apply BitVec.toNat_sub_of_le one_le_n
            conv at v₁ => enter [1, 1, 1, 1]; apply BitVec.toNat_sub_of_le one_le_n
            conv at v₂ => enter [1, 1, 1, 1]; apply BitVec.toNat_sub_of_le one_le_n

            simp only [BitVec.toNat_intCast] at inner_assert h₂ v₀ v₁ v₂ 
            norm_num at inner_assert h₂ v₀ v₁ v₂
            have : ib.toNat = i := by subst ib_def; simp
            simp only [this] at inner_assert h₂ v₀ v₁ v₂
            have : (BitVec.toNat N - 1 - i) % 4294967296 = BitVec.toNat N - 1 - i := by omega
            simp only [this] at v₀ v₁ v₂
            simp only [lengths_eq] at *
            rw [←inner_assert] at h₂ 
            have : i > 0 := by linarith
            have rest := rest ⟨0, by linarith⟩

             

            all_goals sorry
          all_goals sorry
        all_goals sorry
      all_goals sorry
    all_goals sorry
  all_goals sorry
--           -- Here we need to use `h₂` to argue that `bits[N - 1 - i] != pSlice[N - 1 - i]`, and
--           · intro h_eq
--             set d := decomposeToRadix 2 p.val (by linarith) with hd
--             have h_bound : i < d.length := by
--               rcases h₁ with ⟨lens_eq, _⟩
--               rw [← lens_eq]
--               exact hlo
--             have bits_eq_one : List.Vector.get bits
--                 ⟨(4294967296 - i + (4294967295 + d.length)) % 4294967296, by
--                   rcases h₁ with ⟨lens_eq, _⟩
--                   calc (4294967296 - i + (4294967295 + d.length)) % 4294967296
--                     _ = d.length - 1 - i := complex_index_eq i d.length h_bound pSlice_len
--                     _ < BitVec.toNat N := by rw [← lens_eq]; omega
--                 ⟩ = (1 : BitVec 1) := by
--               have idx_eq : (4294967296 - i + (4294967295 + d.length)) % 4294967296 = d.length - 1 - i :=
--                 complex_index_eq i d.length h_bound pSlice_len
--               rcases h₁ with ⟨lens_eq, _⟩
--               simp [hd.symm] at h_eq inner_assert
--               simp [idx_eq] at inner_assert
--               rw [inner_assert] at h_eq
--               convert h_eq using 1
--               congr 1
--               simp [idx_eq]
--
--             exact h₂ bits_eq_one
--
--           -- Here we need to use the `inner_assert`
--           · convert inner_assert using 3
--             simp only
--             set d := decomposeToRadix 2 p.val (by linarith) with hd
--             have h_bound : i < d.length := by
--               rcases h₁ with ⟨lens_eq, _⟩
--               rw [← lens_eq]
--               exact hlo
--             conv in _ % 4294967296 =>
--               rw [complex_index_eq i d.length h_bound pSlice_len]
--         · congr 1
--           simp_all only [List.length_map, Nat.reducePow, BitVec.toNat_intCast, Int.reducePow,
--             EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, ne_eq, List.getElem_map,
--             BitVec.ofNat_eq_ofNat, Bool.decide_or, decide_not, Bool.not_or, Bool.not_not,
--             Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
--             decide_eq_false_iff_not, not_exists, not_and, Builtin.instCastTpU,
--             BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.toNat_sub,
--             BitVec.toNat_ofNatLT, Int.reduceMod, Int.toNat_one, Nat.add_one_sub_one,
--             Nat.add_mod_mod, List.get_eq_getElem, Bool.not_false, not_true_eq_false, false_or,
--             decide_eq_decide]
--           -- Here we need to show that if `ok` is false, and `bits[N - 1 -i] == pSlice[N - 1 - i]`,
--           -- then the invariant holds for i + 1 given i
--           -- In this case we keep the same witness `j` as for `i`
--           constructor
--           · rintro ⟨⟨j_val, hj_prop⟩, hj₁, hj₂, hj₃⟩
--             use ⟨j_val, Nat.lt_succ_of_lt hj_prop⟩, hj₁, hj₂, hj₃
--           · rintro ⟨⟨j_val, hj_prop⟩, hj₁, hj₂, hj₃⟩
--             by_cases h_case : j_val < i
--             · use ⟨j_val, h_case⟩, hj₁, hj₂, hj₃
--             · exfalso
--               apply hj₂
--               convert h₂ using 2
--               · congr 1
--                 set d := decomposeToRadix 2 p.val (by linarith) with hd
--                 have h_bound : j_val < d.length := by
--                   rw [← h₁.1]
--                   omega
--                 convert complex_index_eq j_val d.length h_bound pSlice_len |>.symm
--                 omega
--               · congr 1
--                 set d := decomposeToRadix 2 p.val (by linarith) with hd
--                 have h_bound : j_val < d.length := by
--                   rw [← h₁.1]
--                   omega
--                 convert complex_index_eq j_val d.length h_bound pSlice_len |>.symm
--                 omega
--       -- Here we need to show that if `ok` is true, then the invariant holds for i + 1 given i
--       · congr 2
--         rw [eq_iff_iff]
--         constructor <;> rintro (len_neq | ⟨⟨j_val, j_prop⟩, ⟨hj₁, hj₂, hj₃⟩⟩)
--         · left; exact len_neq
--         · right
--           use ⟨j_val, Nat.lt_succ_of_lt j_prop⟩
--         · left; exact len_neq
--         · by_cases h_case : j_val < i
--           · right
--             use ⟨j_val, h_case⟩
--           · simp at h₁
--             by_cases len_eq : N.toNat = pSlice.length
--             · right
--               exact h₁ len_eq
--             · left
--               exact len_eq
--     -- Here is where all the "action" is, have to prove the constraint `ok` holds => `bits` is as
--     -- expected
--     · steps
--       rename_i ok_invariant _
--       simp at ok_invariant
--       sorry
--
--   -- wrap it up
--   · intro
--     steps
--     subst_vars
--     rfl
--
-- theorem to_le_radix_intro (radix_gt : radix > 1 := by bv_decide) :
--     STHoare p env ⟦⟧
--     («std-1.0.0-beta.12::field::to_le_radix».call h![N] h![f, radix])
--     fun r => r = ⟨decomposeToRadix radix.toNat f.val (by assumption) |>.takeD N.toNat 0, by simp⟩ := by
--   sorry
--   -- enter_decl
--   -- steps
--   -- fapply STHoare.letIn_intro
--   -- · exact fun _ => ⟦⟧
--   -- · apply STHoare.iteTrue_intro
--   --   steps
--   -- intro
--   -- steps
--   -- rename_i _ _ v_eq
--   -- exact v_eq
--
-- theorem to_le_bytes_intro :
--     STHoare p env ⟦⟧
--     («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
--     fun r => r = ⟨decomposeToRadix 256 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
--   sorry
--   -- enter_decl
--   -- steps
--   -- steps [to_le_radix_intro (N := N) (f := f) (radix := 256)]
--   -- fapply STHoare.letIn_intro
--   -- · exact fun _ => ⟦⟧
--   -- · apply STHoare.iteTrue_intro
--   --   steps
--   --   simp_all
--   --   loop_inv nat
--   --     (fun _ _ _ => ∃∃b, ([ok ↦ ⟨Tp.bool, b⟩]))
--   --   rotate_left
--   --   simp
--   --   exact ⟦⟧
--   --   rotate_right
--   --   simp
--   --   apply SLP.exists_intro_r
--   --   exact SLP.entails_self
--
--   --   -- loop body
--   --   intros i hlo hhi
--   --   steps
--   --   apply STHoare.ite_intro
--   --   · intro h₁
--   --     steps
--   --     apply STHoare.ite_intro
--   --     · intro h₂
--   --       steps
--   --     · intro h₂
--   --       steps
--   --   · intro
--   --     steps
--   --   steps
--   -- intro v
--   -- steps
--   -- simp_all
