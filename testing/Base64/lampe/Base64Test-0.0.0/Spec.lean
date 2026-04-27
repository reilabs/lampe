-- Regression test for https://github.com/reilabs/lampe/issues/274

import «Base64Test-0.0.0».Extracted
import Lampe

open Lampe

set_option linter.unusedTactic false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

-- Helpers: specs for noir_base64 global constants so `steps [...]` can
-- automatically step through their calls inside letIn.
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

theorem BASE64_PADDING_CHAR_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::defaults::BASE64_PADDING_CHAR».call h![] h![])
      fun v => v = (61 : U 8) := by
  enter_decl; steps; simpa

theorem BASE64_ENCODE_BE_TABLE_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::tables::BASE64_ENCODE_BE_TABLE».call h![] h![])
      fun (v : List.Vector (BitVec 8) 64) => v = ⟨[65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80,
        81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102,
        103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118,
        119, 120, 121, 122, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 43, 47], rfl⟩ := by
  enter_decl; steps; simpa

-- Specs for the two key sub-functions at concrete sizes.
-- split_into_six_bit_chunks<3, 4, 1>: "foo" bytes → 6-bit chunks
theorem split_six_bit_with_pad_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::encoder::split_into_six_bit_chunks».call h![3, 4, 1] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[25, 38, 61, 47], rfl⟩ := by
  sorry

-- split_into_six_bit_chunks<3, 4, 0>: same computation, no-pad variant
theorem split_six_bit_no_pad_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::encoder::split_into_six_bit_chunks».call h![3, 4, 0] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[25, 38, 61, 47], rfl⟩ := by
  sorry

-- encode_elements<4, 0>: look up base64 table for each 6-bit value
private abbrev iteElseTable : decide ((0 : BitVec 1) = (1 : BitVec 1)) = false := rfl
theorem encode_elements_spec {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («noir_base64-0.0.0::encoder::encode_elements».call h![4, 0] h![⟨[25, 38, 61, 47], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[90, 109, 57, 118], rfl⟩ := by
  enter_decl; steps
  -- Goal: letIn(loop 0 4 body, fun _ => readRef(result))
  apply STHoare.letIn_intro
    (Q := fun _ => [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 57, 118], rfl⟩⟩])
  · -- Iteration 0: input[0]=25, table[25]=90='Z'
    apply STHoare.loopNext_intro
      (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 0, 0, 0], rfl⟩⟩])
      (show (0 : BitVec 32) < 4 from by decide)
    · steps [BASE64_ENCODE_BE_TABLE_spec]
      apply STHoare.letIn_intro
        (Q := fun token => ⟦token = (90 : BitVec 8)⟧ ⋆
          [result ↦ ⟨(Tp.u 8).array 4, ⟨[0, 0, 0, 0], rfl⟩⟩])
      · apply STHoare.consequence_frame_left
        · apply STHoare.ite_intro_of_false iteElseTable
          steps [BASE64_ENCODE_BE_TABLE_spec]; subst_vars; rfl
        · sl
      · intro token; steps; subst_vars; rfl
    -- Iteration 1: input[1]=38, table[38]=109='m'
    apply STHoare.loopNext_intro
      (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 0, 0], rfl⟩⟩])
      (show (1 : BitVec 32) < 4 from by decide)
    · steps [BASE64_ENCODE_BE_TABLE_spec]
      apply STHoare.letIn_intro
        (Q := fun token => ⟦token = (109 : BitVec 8)⟧ ⋆
          [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 0, 0, 0], rfl⟩⟩])
      · apply STHoare.consequence_frame_left
        · apply STHoare.ite_intro_of_false iteElseTable
          steps [BASE64_ENCODE_BE_TABLE_spec]; subst_vars; rfl
        · sl
      · intro token; steps; subst_vars; rfl
    -- Iteration 2: input[2]=61, table[61]=57='9'
    apply STHoare.loopNext_intro
      (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 57, 0], rfl⟩⟩])
      (show (2 : BitVec 32) < 4 from by decide)
    · steps [BASE64_ENCODE_BE_TABLE_spec]
      apply STHoare.letIn_intro
        (Q := fun token => ⟦token = (57 : BitVec 8)⟧ ⋆
          [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 0, 0], rfl⟩⟩])
      · apply STHoare.consequence_frame_left
        · apply STHoare.ite_intro_of_false iteElseTable
          steps [BASE64_ENCODE_BE_TABLE_spec]; subst_vars; rfl
        · sl
      · intro token; steps; subst_vars; rfl
    -- Iteration 3: input[3]=47, table[47]=118='v'
    apply STHoare.loopNext_intro
      (Q := [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 57, 118], rfl⟩⟩])
      (show (3 : BitVec 32) < 4 from by decide)
    · steps [BASE64_ENCODE_BE_TABLE_spec]
      apply STHoare.letIn_intro
        (Q := fun token => ⟦token = (118 : BitVec 8)⟧ ⋆
          [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 57, 0], rfl⟩⟩])
      · apply STHoare.consequence_frame_left
        · apply STHoare.ite_intro_of_false iteElseTable
          steps [BASE64_ENCODE_BE_TABLE_spec]; subst_vars; rfl
        · sl
      · intro token; steps; subst_vars; rfl
    -- Loop done (3+1 = 4, zero iterations remaining)
    have h31 : (3 : BitVec 32) + 1 = 4 := by decide
    rw [h31]
    apply STHoare.consequence_frame
      (P := [result ↦ ⟨(Tp.u 8).array 4, ⟨[90, 109, 57, 118], rfl⟩⟩])
      STHoare.loopDone_intro
    · simp; apply SLP.entails_self
    · intro; simp
  · -- readRef continuation
    intro _; steps; simp_all

-- Input: "foo" = [102, 111, 111]
-- Expected output: "Zm9v" = [90, 109, 57, 118]
theorem encode_with_padding_correct {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («Base64Test-0.0.0::encode_with_padding».call h![3] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[90, 109, 57, 118], rfl⟩ := by
  enter_decl; steps
  enter_decl; steps
  enter_decl; steps
  exact ()
  simp
  steps [split_six_bit_with_pad_spec, encode_elements_spec, BASE64_PADDING_CHAR_spec]
  -- Remaining: letIn (ite padding_check ...) (fun _ => readRef(result))
  -- result already holds [90, 109, 57, 118]. Padding is no-op since rem=0.
  apply STHoare.letIn_intro
  · -- Head: ite (UsePadding == 1) padding_body skip
    apply STHoare.ite_intro_of_true rfl
    -- Then-branch: compute rem = 3%3 = 0, then ite (rem==1) then ... else ite (rem==2) then ... else skip
    steps
    -- Stuck at ite (rem == 1). rem=0 so condition is false.
    -- Need to subst rem first so condition reduces
    subst_vars
    apply STHoare.ite_intro_of_false (show decide (3#32 % 3#32 = 1#32) = false from rfl)
    -- else: ite (rem == 2). rem=0 so condition is false.
    steps
    apply STHoare.ite_intro_of_false (show decide (3#32 % 3#32 = 2#32) = false from rfl)
    apply STHoare.consequence_frame_left STHoare.skip_intro
    sl
  -- Continuation: readRef(result)
  intro _
  steps
  simp_all

-- Same for the no-padding variant (UsePadding=0).
theorem encode_no_padding_correct {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («Base64Test-0.0.0::encode_no_padding».call h![3] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[90, 109, 57, 118], rfl⟩ := by
  enter_decl; steps
  enter_decl; steps
  enter_decl; steps
  exact ()
  simp
  steps [split_six_bit_no_pad_spec, encode_elements_spec]
  -- Remaining: letIn (ite padding_check ...) (fun _ => readRef(result))
  -- UsePadding=0, so ite takes false branch (skip). result holds [90, 109, 57, 118].
  apply STHoare.letIn_intro
  · apply STHoare.ite_intro_of_false (show decide (0#32 = 1#32) = false from rfl)
    apply STHoare.consequence_frame_left STHoare.skip_intro
    sl
  intro _
  steps
  simp_all
