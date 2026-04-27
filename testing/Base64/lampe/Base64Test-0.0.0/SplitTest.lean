-- Incremental test for split_six_bit_with_pad_spec
import «Base64Test-0.0.0».Extracted
import Lampe
import Stdlib.Field.Mod
import Mathlib.Tactic.IntervalCases

open Lampe

set_option linter.unusedTactic false
set_option maxRecDepth 131072
set_option maxHeartbeats 32000000

theorem BYTES_PER_CHUNK_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::defaults::BYTES_PER_CHUNK».call h![] h![])
      fun v => v = (30 : U 32) := by
  enter_decl; steps; simpa

theorem BASE64_ELEMENTS_PER_CHUNK_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::defaults::BASE64_ELEMENTS_PER_CHUNK».call h![] h![])
      fun v => v = (40 : U 32) := by
  enter_decl; steps; simpa

private abbrev numChunks : BitVec 32 := BitVec.udiv 3 30 + if decide ((3 : BitVec 32) % 30 ≠ 0) = true then 1 else 0

-- Helper lemmas for copy loop bound checks (top level so native_decide can evaluate)
private abbrev copyBound : BitVec 32 := 4 - (numChunks - 1) * 40
private abbrev b64Off : BitVec 32 := (numChunks - 1) * 40

private lemma iter0_lt : (0 : BitVec 32) < copyBound := by native_decide
private lemma iter1_lt : (0 : BitVec 32) + 1 < copyBound := by native_decide
private lemma iter2_lt : (0 : BitVec 32) + 1 + 1 < copyBound := by native_decide
private lemma iter3_lt : (0 : BitVec 32) + 1 + 1 + 1 < copyBound := by native_decide
private lemma iter_done : (0 : BitVec 32) + 1 + 1 + 1 + 1 = copyBound := by native_decide

private lemma b64Off_eq : b64Off = (0 : BitVec 32) := by native_decide

-- Normalize ↑0 and ↑1 coercions to concrete BitVec literals
private lemma nc0 : (↑(0 : Nat) : BitVec 32) = (0 : BitVec 32) := rfl
private lemma nc1 : (↑(1 : Nat) : BitVec 32) = (1 : BitVec 32) := rfl
private lemma ic0 : (↑(0 : Int) : BitVec 32) = (0 : BitVec 32) := rfl
private lemma ic1 : (↑(1 : Int) : BitVec 32) = (1 : BitVec 32) := rfl
-- Direct computation of inner if-then-else and index values
private lemma inner_ite : (if decide ((3 : BitVec 32) % 30 ≠ (0 : BitVec 32)) = true then (1 : BitVec 32) else 0) = 1 := by native_decide
private lemma idx_eq_0 : (BitVec.udiv (3 : BitVec 32) 30 + 1 - 1) * 40 + 0 = (0 : BitVec 32) := by native_decide
private lemma idx_eq_1 : (BitVec.udiv (3 : BitVec 32) 30 + 1 - 1) * 40 + (0 + 1) = (1 : BitVec 32) := by native_decide
private lemma idx_eq_2 : (BitVec.udiv (3 : BitVec 32) 30 + 1 - 1) * 40 + (0 + 1 + 1) = (2 : BitVec 32) := by native_decide
private lemma idx_eq_3 : (BitVec.udiv (3 : BitVec 32) 30 + 1 - 1) * 40 + (0 + 1 + 1 + 1) = (3 : BitVec 32) := by native_decide

-- ite condition facts
private lemma b64off_add_0_lt : decide (b64Off + (0 : BitVec 32) < 4 - (0 : BitVec 32)) = true := by native_decide
private lemma b64off_add_1_lt : decide (b64Off + ((0 : BitVec 32) + 1) < 4 - (0 : BitVec 32)) = true := by native_decide
private lemma b64off_add_2_lt : decide (b64Off + ((0 : BitVec 32) + 1 + 1) < 4 - (0 : BitVec 32)) = true := by native_decide
private lemma b64off_add_3_lt : decide (b64Off + ((0 : BitVec 32) + 1 + 1 + 1) < 4 - (0 : BitVec 32)) = true := by native_decide

private lemma zmod_val_eq {lp : Lampe.Prime} [Lampe.Prime.BitsGT lp 240] :
    ZMod.val ((6713199 : Fp lp) * 256 ^ 27) = 6713199 * 256 ^ 27 := by
  have h1 : (6713199 : Fp lp) * 256 ^ 27 = ((6713199 * 256 ^ 27 : ℕ) : Fp lp) := by push_cast; ring
  rw [h1, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  calc 6713199 * 256 ^ 27 < 2 ^ 240 := by norm_num
    _ < lp.natVal := Lampe.Prime.BitsGT.lt_prime

private abbrev expectedResult : List.Vector (BitVec 8) 40 :=
  ⟨[25, 38, 61, 47] ++ List.replicate 36 0, by decide⟩

private abbrev concreteBytes : List.Vector (BitVec 8) 30 :=
  ⟨List.replicate 27 0 ++ [111, 111, 102], by decide⟩

private lemma byte2_cond_true (i : Nat) (hi : i < 40) :
    ∀ (h : i < 2 ^ 32),
    (BitVec.ofNatLT i h).udiv (4 : BitVec 32) * (3 : BitVec 32) + (2 : BitVec 32) < (30 : BitVec 32) := by
  intro h; revert h; interval_cases i <;> decide

-- mod4=0 lemmas
private lemma val_m0_0 : concreteBytes.get ⟨0, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨39, by omega⟩ := by native_decide
private lemma val_m0_4 : concreteBytes.get ⟨3, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨35, by omega⟩ := by native_decide
private lemma val_m0_8 : concreteBytes.get ⟨6, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨31, by omega⟩ := by native_decide
private lemma val_m0_12 : concreteBytes.get ⟨9, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨27, by omega⟩ := by native_decide
private lemma val_m0_16 : concreteBytes.get ⟨12, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨23, by omega⟩ := by native_decide
private lemma val_m0_20 : concreteBytes.get ⟨15, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨19, by omega⟩ := by native_decide
private lemma val_m0_24 : concreteBytes.get ⟨18, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨15, by omega⟩ := by native_decide
private lemma val_m0_28 : concreteBytes.get ⟨21, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨11, by omega⟩ := by native_decide
private lemma val_m0_32 : concreteBytes.get ⟨24, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨7, by omega⟩ := by native_decide
private lemma val_m0_36 : concreteBytes.get ⟨27, by omega⟩ % (64 : BitVec 8) = expectedResult.get ⟨3, by omega⟩ := by native_decide

-- mod4=1 lemmas
private lemma val_m1_1 : concreteBytes.get ⟨0, by omega⟩ / 64 + (concreteBytes.get ⟨1, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨38, by omega⟩ := by native_decide
private lemma val_m1_5 : concreteBytes.get ⟨3, by omega⟩ / 64 + (concreteBytes.get ⟨4, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨34, by omega⟩ := by native_decide
private lemma val_m1_9 : concreteBytes.get ⟨6, by omega⟩ / 64 + (concreteBytes.get ⟨7, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨30, by omega⟩ := by native_decide
private lemma val_m1_13 : concreteBytes.get ⟨9, by omega⟩ / 64 + (concreteBytes.get ⟨10, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨26, by omega⟩ := by native_decide
private lemma val_m1_17 : concreteBytes.get ⟨12, by omega⟩ / 64 + (concreteBytes.get ⟨13, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨22, by omega⟩ := by native_decide
private lemma val_m1_21 : concreteBytes.get ⟨15, by omega⟩ / 64 + (concreteBytes.get ⟨16, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨18, by omega⟩ := by native_decide
private lemma val_m1_25 : concreteBytes.get ⟨18, by omega⟩ / 64 + (concreteBytes.get ⟨19, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨14, by omega⟩ := by native_decide
private lemma val_m1_29 : concreteBytes.get ⟨21, by omega⟩ / 64 + (concreteBytes.get ⟨22, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨10, by omega⟩ := by native_decide
private lemma val_m1_33 : concreteBytes.get ⟨24, by omega⟩ / 64 + (concreteBytes.get ⟨25, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨6, by omega⟩ := by native_decide
private lemma val_m1_37 : concreteBytes.get ⟨27, by omega⟩ / 64 + (concreteBytes.get ⟨28, by omega⟩ % 64 * 4) % 64 = expectedResult.get ⟨2, by omega⟩ := by native_decide

-- mod4=2 lemmas
private lemma val_m2_2 : concreteBytes.get ⟨1, by omega⟩ / 16 + ((concreteBytes.get ⟨2, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨37, by omega⟩ := by native_decide
private lemma val_m2_6 : concreteBytes.get ⟨4, by omega⟩ / 16 + ((concreteBytes.get ⟨5, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨33, by omega⟩ := by native_decide
private lemma val_m2_10 : concreteBytes.get ⟨7, by omega⟩ / 16 + ((concreteBytes.get ⟨8, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨29, by omega⟩ := by native_decide
private lemma val_m2_14 : concreteBytes.get ⟨10, by omega⟩ / 16 + ((concreteBytes.get ⟨11, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨25, by omega⟩ := by native_decide
private lemma val_m2_18 : concreteBytes.get ⟨13, by omega⟩ / 16 + ((concreteBytes.get ⟨14, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨21, by omega⟩ := by native_decide
private lemma val_m2_22 : concreteBytes.get ⟨16, by omega⟩ / 16 + ((concreteBytes.get ⟨17, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨17, by omega⟩ := by native_decide
private lemma val_m2_26 : concreteBytes.get ⟨19, by omega⟩ / 16 + ((concreteBytes.get ⟨20, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨13, by omega⟩ := by native_decide
private lemma val_m2_30 : concreteBytes.get ⟨22, by omega⟩ / 16 + ((concreteBytes.get ⟨23, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨9, by omega⟩ := by native_decide
private lemma val_m2_34 : concreteBytes.get ⟨25, by omega⟩ / 16 + ((concreteBytes.get ⟨26, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨5, by omega⟩ := by native_decide
private lemma val_m2_38 : concreteBytes.get ⟨28, by omega⟩ / 16 + ((concreteBytes.get ⟨29, by omega⟩ % 64 * 4) % 64 * 4) % 64 = expectedResult.get ⟨1, by omega⟩ := by native_decide

-- mod4=3 lemmas
private lemma val_m3_3 : concreteBytes.get ⟨2, by omega⟩ / 4 = expectedResult.get ⟨36, by omega⟩ := by native_decide
private lemma val_m3_7 : concreteBytes.get ⟨5, by omega⟩ / 4 = expectedResult.get ⟨32, by omega⟩ := by native_decide
private lemma val_m3_11 : concreteBytes.get ⟨8, by omega⟩ / 4 = expectedResult.get ⟨28, by omega⟩ := by native_decide
private lemma val_m3_15 : concreteBytes.get ⟨11, by omega⟩ / 4 = expectedResult.get ⟨24, by omega⟩ := by native_decide
private lemma val_m3_19 : concreteBytes.get ⟨14, by omega⟩ / 4 = expectedResult.get ⟨20, by omega⟩ := by native_decide
private lemma val_m3_23 : concreteBytes.get ⟨17, by omega⟩ / 4 = expectedResult.get ⟨16, by omega⟩ := by native_decide
private lemma val_m3_27 : concreteBytes.get ⟨20, by omega⟩ / 4 = expectedResult.get ⟨12, by omega⟩ := by native_decide
private lemma val_m3_31 : concreteBytes.get ⟨23, by omega⟩ / 4 = expectedResult.get ⟨8, by omega⟩ := by native_decide
private lemma val_m3_35 : concreteBytes.get ⟨26, by omega⟩ / 4 = expectedResult.get ⟨4, by omega⟩ := by native_decide
private lemma val_m3_39 : concreteBytes.get ⟨29, by omega⟩ / 4 = expectedResult.get ⟨0, by omega⟩ := by native_decide

set_option pp.all false in
theorem to_be_radix_64_spec {lp} [Lampe.Prime.BitsGT lp 240] :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::encoder::to_be_radix::to_be_radix_64».call h![40] h![(6713199 : Fp lp) * 256 ^ 27])
      fun (v : List.Vector (BitVec 8) 40) => ⟦v = expectedResult⟧ := by
  enter_decl
  steps [Lampe.Stdlib.Field.to_le_bytes_intro]
  rename_i bytes hlt hbytes
  have hv := zmod_val_eq (lp := lp)
  have hlt' : (6713199 * 256 ^ 27 : ℕ) < 256 ^ 30 := by norm_num
  have hsub : (⟨ZMod.val ((6713199 : Fp lp) * 256 ^ 27), hlt⟩ : Fin (256 ^ 30)) =
              ⟨6713199 * 256 ^ 27, hlt'⟩ := Fin.ext hv
  simp only [hsub] at hbytes
  have hconcrete : bytes = concreteBytes := by
    rw [hbytes]
    change (List.Vector.map BitVec.ofFin (@RadixVec.toDigitsBE R256 30
      ⟨6713199 * 256 ^ 27, by norm_num⟩)).reverse = concreteBytes
    native_decide
  subst hconcrete
  clear hbytes hsub hv hlt hlt'
  apply STHoare.letIn_intro (Q := fun (_result : List.Vector (BitVec 8) 40) => ⟦True⟧)
  · steps; enter_decl; apply STHoare.fresh_intro
  · intro result
    steps
    apply STHoare.letIn_intro (Q := fun _ => ⟦result = expectedResult⟧)
    · loop_inv nat fun i _ _ =>
        ⟦∀ (j : Fin 40), j.val ≥ 40 - i → result.get j = expectedResult.get j⟧
      · intro j hj; simp [BitVec.toNat_ofNat] at hj; omega
      · simp [BitVec.toNat_ofNat]
      · rename_i _ h_inv_final
        have : BitVec.toNat (↑(List.Vector.length result) : BitVec 32) = 40 := by
          simp [List.Vector.length, BitVec.toNat_ofNat]
        simp only [this, Nat.sub_self] at h_inv_final
        exact List.Vector.ext (fun i => h_inv_final i (Nat.zero_le _))
      · intro i hlo hhi
        have hi_lt : i < 40 := by simpa [BitVec.toNat_ofNat] using hhi
        apply Lampe.Steps.pluck_final_pure_destructively
        intro h_inv
        steps
        -- byte2 if-then-else: carry the value
        apply STHoare.letIn_intro
          (Q := fun byte2 => ⟦byte2 = concreteBytes.get ⟨(i / 4) * 3 + 2, by omega⟩⟧)
        · apply STHoare.ite_intro_of_true
          · subst_vars
            simp only [concreteBytes, List.Vector.length]
            exact decide_eq_true (byte2_cond_true i hi_lt (by omega))
          · steps
            subst_vars; simp [Builtin.CastTp.cast]
            congr 1; omega
        · intro byte2
          apply Lampe.Steps.pluck_final_pure_destructively
          intro hbyte2
          subst hbyte2
          steps
          -- mod4=0 branch
          apply STHoare.ite_intro
          · intro hmod; steps
            subst_vars; simp only [beq_iff_eq, decide_eq_true_eq] at *
            intro j hj; by_cases hjj : j.val ≥ 40 - i
            · exact h_inv j hjj
            · have hjeq : j.val = 40 - i - 1 := by omega
              rw [show j = ⟨40 - i - 1, by omega⟩ from Fin.ext hjeq]
              interval_cases i <;>
                first
                | (simp_all (config := { decide := true }) [];
                   first | exact val_m0_0 | exact val_m0_4 | exact val_m0_8 | exact val_m0_12
                         | exact val_m0_16 | exact val_m0_20 | exact val_m0_24 | exact val_m0_28
                         | exact val_m0_32 | exact val_m0_36)
                | (simp_all (config := { decide := true }) []; rfl)
                | (exfalso; have hmn := congrArg BitVec.toNat hmod;
                   simp [BitVec.toNat_ofNatLT] at hmn)
          · intro hnot0
            steps
            -- mod4=1 branch
            apply STHoare.ite_intro
            · intro hmod; steps
              subst_vars; simp only [beq_iff_eq, decide_eq_true_eq] at *
              intro j hj; by_cases hjj : j.val ≥ 40 - i
              · exact h_inv j hjj
              · have hjeq : j.val = 40 - i - 1 := by omega
                rw [show j = ⟨40 - i - 1, by omega⟩ from Fin.ext hjeq]
                interval_cases i <;>
                  first
                  | (simp_all (config := { decide := true }) [];
                     first | exact val_m1_1 | exact val_m1_5 | exact val_m1_9 | exact val_m1_13
                           | exact val_m1_17 | exact val_m1_21 | exact val_m1_25 | exact val_m1_29
                           | exact val_m1_33 | exact val_m1_37)
                  | (simp_all (config := { decide := true }) []; rfl)
                  | (exfalso; have hmn := congrArg BitVec.toNat hmod;
                     simp [BitVec.toNat_ofNatLT] at hmn)
            · intro hnot1
              steps
              -- mod4=2 branch
              apply STHoare.ite_intro
              · intro hmod; steps
                subst_vars; simp only [beq_iff_eq, decide_eq_true_eq] at *
                intro j hj; by_cases hjj : j.val ≥ 40 - i
                · exact h_inv j hjj
                · have hjeq : j.val = 40 - i - 1 := by omega
                  rw [show j = ⟨40 - i - 1, by omega⟩ from Fin.ext hjeq]
                  interval_cases i <;>
                    first
                    | (simp_all (config := { decide := true }) [];
                       first | exact val_m2_2 | exact val_m2_6 | exact val_m2_10 | exact val_m2_14
                             | exact val_m2_18 | exact val_m2_22 | exact val_m2_26 | exact val_m2_30
                             | exact val_m2_34 | exact val_m2_38)
                    | (simp_all (config := { decide := true }) []; rfl)
                    | (exfalso; have hmn := congrArg BitVec.toNat hmod;
                       simp [BitVec.toNat_ofNatLT] at hmn)
              -- mod4=3 branch (else)
              · intro hnot2; steps
                subst_vars
                intro j hj; by_cases hjj : j.val ≥ 40 - i
                · exact h_inv j hjj
                · have hjeq : j.val = 40 - i - 1 := by omega
                  rw [show j = ⟨40 - i - 1, by omega⟩ from Fin.ext hjeq]
                  interval_cases i <;>
                    first
                    | (simp only [beq_iff_eq, decide_eq_true_eq] at *;
                       simp_all (config := { decide := true }) [];
                       first | exact val_m3_3 | exact val_m3_7 | exact val_m3_11 | exact val_m3_15
                             | exact val_m3_19 | exact val_m3_23 | exact val_m3_27 | exact val_m3_31
                             | exact val_m3_35 | exact val_m3_39)
                    | (simp only [beq_iff_eq, decide_eq_true_eq] at *;
                       simp_all (config := { decide := true }) []; rfl)
                    -- TODO: close mod4=3 contradiction for i ∈ {0..38} where i%4 ≠ 3
                    | (exfalso; sorry)
    · intro _
      apply Lampe.Steps.pluck_final_pure_destructively
      intro heq; subst heq; steps; assumption

set_option pp.all false in
theorem split_test {lp} [Lampe.Prime.BitsGT lp 240] :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::encoder::split_into_six_bit_chunks».call h![3, 4, 1] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[25, 38, 61, 47], rfl⟩ := by
  enter_decl
  steps [BYTES_PER_CHUNK_spec, BASE64_ELEMENTS_PER_CHUNK_spec]
  subst_vars
  -- 1. num_padding_chars ite chain
  apply STHoare.letIn_intro (Q := fun npc => ⟦npc = (0 : U 32)⟧)
  · apply STHoare.ite_intro_of_true (show decide (1 = ↑1) = true from rfl)
    steps
    apply STHoare.ite_intro_of_false (show decide ((3 : BitVec 32) % 3 = ↑1) = false from rfl)
    steps
    apply STHoare.ite_intro_of_false (show decide ((3 : BitVec 32) % 3 = ↑2) = false from rfl)
    steps; subst_vars; rfl
  · intro npc; subst_vars
    steps [BYTES_PER_CHUNK_spec, BASE64_ELEMENTS_PER_CHUNK_spec]
    subst_vars
    -- 2. letIn(ite(num_chunks > 0, then, skip), fun _ => readRef(result))
    apply STHoare.letIn_intro
      (Q := fun _ => [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 61, 47], rfl⟩⟩])
    · simp only [Builtin.CastTp.cast]
      apply STHoare.ite_intro_of_true (show decide ((0 : BitVec 32) + (if true then 1 else 0) > 0) = true from rfl)
      steps [BYTES_PER_CHUNK_spec, BASE64_ELEMENTS_PER_CHUNK_spec]
      subst_vars
      -- 3. Empty full-chunks loop (0..numChunks-1 = 0..0)
      have hfinal : numChunks - 1 = (0 : BitVec 32) := by native_decide
      apply STHoare.letIn_intro
        (Q := fun _ => [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
      · change STHoare _ _ _ (Expr.loop 0 (numChunks - 1) _) _
        rw [hfinal]
        apply STHoare.consequence_frame
          (P := [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
          STHoare.loopDone_intro
        · simp; apply SLP.entails_self
        · intro; simp
      · -- 4. Final chunk processing
        intro _
        -- steps processes: byte_offset, base64_offset, bytes_in_final_chunk,
        -- num_elements_in_final_chunk, slice = ref(0), and stops at byte packing loop
        steps [BYTES_PER_CHUNK_spec, BASE64_ELEMENTS_PER_CHUNK_spec]
        subst_vars
        -- 5. Byte packing loop 0..3 + padding + to_be_radix_64 + copy
        -- All remaining loops and calls
        apply STHoare.letIn_intro
          (Q := fun _ => [slice ↦ ⟨Tp.field, (6713199 : Fp lp)⟩] ⋆
                         [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
        · -- Byte packing: 3 iterations
          -- Normalize loop bound
          have hbfc : (3 : BitVec 32) - (numChunks - 1) * 30 = (3 : BitVec 32) := by native_decide
          change STHoare _ _ _ (Expr.loop ↑0 ((3 : BitVec 32) - (numChunks - 1) * 30) _) _
          rw [hbfc]
          -- iter 0: slice = 0*256 + 102 = 102
          apply STHoare.loopNext_intro
            (Q := [slice ↦ ⟨Tp.field, (102 : Fp lp)⟩] ⋆
                  [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
            (show (0 : BitVec 32) < 3 from by decide)
          · steps [BYTES_PER_CHUNK_spec]; subst_vars
            simp only [Lens.modify, Lens.get, Option.get_some]; congr 1
            simp only [show @Int.cast (BitVec 32) BitVec.instIntCast (0 : Int) = (0 : BitVec 32) from rfl,
                        show @Int.cast (BitVec 32) BitVec.instIntCast (1 : Int) = (1 : BitVec 32) from rfl,
                        Builtin.CastTp.cast]
            push_cast; ring_nf; norm_cast; simp [List.Vector.head, List.Vector.get]
          -- iter 1: slice = 102*256 + 111 = 26223
          apply STHoare.loopNext_intro
            (Q := [slice ↦ ⟨Tp.field, (26223 : Fp lp)⟩] ⋆
                  [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
            (show (1 : BitVec 32) < 3 from by decide)
          · steps [BYTES_PER_CHUNK_spec]; subst_vars
            simp only [Lens.modify, Lens.get, Option.get_some]; congr 1
            simp only [show @Int.cast (BitVec 32) BitVec.instIntCast (0 : Int) = (0 : BitVec 32) from rfl,
                        show @Int.cast (BitVec 32) BitVec.instIntCast (1 : Int) = (1 : BitVec 32) from rfl,
                        Builtin.CastTp.cast]
            push_cast; ring_nf; norm_cast; simp [List.Vector.head, List.Vector.get]
          -- iter 2: slice = 26223*256 + 111 = 6713199
          apply STHoare.loopNext_intro
            (Q := [slice ↦ ⟨Tp.field, (6713199 : Fp lp)⟩] ⋆
                  [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
            (show (2 : BitVec 32) < 3 from by decide)
          · steps [BYTES_PER_CHUNK_spec]; subst_vars
            simp only [Lens.modify, Lens.get, Option.get_some]; congr 1
            simp only [show @Int.cast (BitVec 32) BitVec.instIntCast (0 : Int) = (0 : BitVec 32) from rfl,
                        show @Int.cast (BitVec 32) BitVec.instIntCast (1 : Int) = (1 : BitVec 32) from rfl,
                        Builtin.CastTp.cast]
            push_cast; ring_nf; norm_cast; simp [List.Vector.head, List.Vector.get]
          -- loop done (2+1 = 3)
          have h23 : (2 : BitVec 32) + 1 = 3 := by decide
          rw [h23]
          apply STHoare.consequence_frame
            (P := [slice ↦ ⟨Tp.field, (6713199 : Fp lp)⟩] ⋆
                  [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
            STHoare.loopDone_intro
          · simp; apply SLP.entails_self
          · intro; sl
        · -- 6. Continuation: padding + to_be_radix_64 + copy
          intro _
          steps [BYTES_PER_CHUNK_spec]
          subst_vars
          -- 7. Padding loop (3..30): slice *= 256 each iteration
          apply STHoare.letIn_intro
            (Q := fun _ => [slice ↦ ⟨Tp.field, (6713199 : Fp lp) * 256 ^ 27⟩] ⋆
                           [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
          · -- Normalize padding loop lo bound
            have hpad_lo : (3 : BitVec 32) - (numChunks - 1) * 30 = (3 : BitVec 32) := by native_decide
            show STHoare _ _ _ (Expr.loop ((3 : BitVec 32) - (numChunks - 1) * 30) 30 _) _
            rw [hpad_lo]
            loop_inv nat fun i _ _ =>
              [slice ↦ ⟨Tp.field, (6713199 : Fp lp) * 256 ^ (i - 3)⟩] ⋆
              [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩]
            · -- Initial: 6713199 = 6713199 * 256^(3-3)
              simp
            · -- Bounds: 3 ≤ 30
              simp [BitVec.toNat_ofNat]
            · -- Body: slice = old*256 → slice = old*256^(i+1-3)
              intro i hi1 hi2; steps; subst_vars
              simp only [Lens.modify, Lens.get, Option.get_some]
              congr 1
              have h3 : 3 ≤ i := by simpa [BitVec.toNat_ofNat] using hi1
              have h : i + 1 - 3 = i - 3 + 1 := by omega
              rw [h, pow_succ]; push_cast; ring
          · -- 8. to_be_radix_64 call + copy loop
            intro _
            steps [BYTES_PER_CHUNK_spec]
            subst_vars
            -- Apply letIn_intro for to_be_radix_64 call
            apply STHoare.letIn_intro
              (Q := fun (slice_base64_chunks : List.Vector (BitVec 8) 40) =>
                ⟦slice_base64_chunks = ⟨[25, 38, 61, 47] ++ List.replicate 36 0, by decide⟩⟧ ⋆
                [result ↦ ⟨(Tp.u 8).array 4, List.Vector.replicate (BitVec.toNat 4) 0⟩])
            · -- to_be_radix_64 spec
              steps [@to_be_radix_64_spec lp _]; assumption
            · -- Copy loop with known values
              intro slice_base64_chunks
              apply Lampe.Steps.pluck_pures_destructively
              intro hsbc; subst hsbc
              -- Process letIn wrappers
              steps
              subst_vars
              -- Split letIn(loop, skip)
              apply STHoare.letIn_intro
                (Q := fun _ => [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 61, 47], rfl⟩⟩])
              · -- Copy loop: 4 iterations
                -- iter 0: result[0] = 25
                apply STHoare.loopNext_intro
                  (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 0, 0, 0], rfl⟩⟩])
                  iter0_lt
                · steps; subst_vars
                  apply STHoare.ite_intro_of_true (show decide ((1 : BitVec 32) = 1) = true from rfl)
                  steps; subst_vars
                  apply STHoare.ite_intro_of_true b64off_add_0_lt
                  steps; subst_vars
                  simp only [ic0, ic1, inner_ite, idx_eq_0, idx_eq_1, idx_eq_2, idx_eq_3,
                    Lens.modify, Lens.get, Access.modify, Builtin.CastTp.cast,
                    BitVec.setWidth_eq, BitVec.toNat_ofNatLT, ↓reduceDIte,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
                    Option.get_some, List.Vector.toList_set]
                  congr 1
                -- iter 1: result[1] = 38
                apply STHoare.loopNext_intro
                  (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 0, 0], rfl⟩⟩])
                  iter1_lt
                · steps; subst_vars
                  apply STHoare.ite_intro_of_true (show decide ((1 : BitVec 32) = 1) = true from rfl)
                  steps; subst_vars
                  apply STHoare.ite_intro_of_true b64off_add_1_lt
                  steps; subst_vars
                  simp only [ic0, ic1, inner_ite, idx_eq_0, idx_eq_1, idx_eq_2, idx_eq_3,
                    Lens.modify, Lens.get, Access.modify, Builtin.CastTp.cast,
                    BitVec.setWidth_eq, BitVec.toNat_ofNatLT, ↓reduceDIte,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
                    Option.get_some, List.Vector.toList_set]
                  congr 1
                -- iter 2: result[2] = 61
                apply STHoare.loopNext_intro
                  (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 61, 0], rfl⟩⟩])
                  iter2_lt
                · steps; subst_vars
                  apply STHoare.ite_intro_of_true (show decide ((1 : BitVec 32) = 1) = true from rfl)
                  steps; subst_vars
                  apply STHoare.ite_intro_of_true b64off_add_2_lt
                  steps; subst_vars
                  simp only [ic0, ic1, inner_ite, idx_eq_0, idx_eq_1, idx_eq_2, idx_eq_3,
                    Lens.modify, Lens.get, Access.modify, Builtin.CastTp.cast,
                    BitVec.setWidth_eq, BitVec.toNat_ofNatLT, ↓reduceDIte,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
                    Option.get_some, List.Vector.toList_set]
                  congr 1
                -- iter 3: result[3] = 47
                apply STHoare.loopNext_intro
                  (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 61, 47], rfl⟩⟩])
                  iter3_lt
                · steps; subst_vars
                  apply STHoare.ite_intro_of_true (show decide ((1 : BitVec 32) = 1) = true from rfl)
                  steps; subst_vars
                  apply STHoare.ite_intro_of_true b64off_add_3_lt
                  steps; subst_vars
                  simp only [ic0, ic1, inner_ite, idx_eq_0, idx_eq_1, idx_eq_2, idx_eq_3,
                    Lens.modify, Lens.get, Access.modify, Builtin.CastTp.cast,
                    BitVec.setWidth_eq, BitVec.toNat_ofNatLT, ↓reduceDIte,
                    Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
                    Option.get_some, List.Vector.toList_set]
                  congr 1
                -- loop done
                rw [iter_done]
                apply STHoare.consequence_frame
                  (P := [result ↦ ⟨(Tp.u 8).array 4, ⟨[25, 38, 61, 47], rfl⟩⟩])
                  STHoare.loopDone_intro
                · simp; apply SLP.entails_self
                · intro; simp
              · intro _; steps
    · intro _; steps; simp_all
