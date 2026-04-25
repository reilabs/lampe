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
  apply STHoare.letIn_intro
  · enter_decl
    steps
    apply STHoare.letIn_intro
    · apply STHoare.iteTrue_intro
      steps
      subst rem
      simp [Tp.denote, Int.cast, IntCast.intCast]
      apply STHoare.iteFalse_intro
      steps
      apply STHoare.iteFalse_intro
      apply STHoare.litU_intro
    intro v
    steps
    subst v
    apply STHoare.letIn_intro
    · enter_decl
      steps
      apply STHoare.consequence_frame_left STHoare.litU_intro
      sl
    intro v
    steps
    subst v



-- Same for the no-padding variant (UsePadding=0).
theorem encode_no_padding_correct {lp} :
    STHoare lp «Base64Test-0.0.0».env ⟦⟧
      («Base64Test-0.0.0::encode_no_padding».call h![3] h![⟨[102, 111, 111], rfl⟩])
      fun (v : List.Vector (BitVec 8) 4) => v = ⟨[90, 109, 57, 118], rfl⟩ := by
  enter_decl; steps
  enter_decl; steps
  enter_decl; steps
  deep_steps
