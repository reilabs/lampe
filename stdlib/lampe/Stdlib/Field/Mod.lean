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
  rename bits = _ => bits_val
  simp at bits_val
  -- `if !is_unconstrained()
  fapply STHoare.letIn_intro (Q := fun _ => ⟦⟧)
  apply STHoare.ite_intro_of_true
  · rfl
  · steps
    -- start of loop
    loop_inv nat (fun _ _ _=> ∃∃b , ([ok ↦ ⟨Tp.bool, b⟩]))
    rotate_left
    simp
    exact ⟦⟧
    rotate_right
    simp
    apply SLP.exists_intro_r
    exact SLP.entails_self

    -- loop body
    intros i hlo hhi
    steps
    apply STHoare.ite_intro
    · intro h₁
      steps
      apply STHoare.ite_intro
      · intro h₂
        steps
      · intro h₂
        steps
    · intro
      steps
    steps
  intro ; steps ; subst_vars ; rfl

theorem to_le_radix_intro (radix_gt : radix > 1 := by bv_decide) :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_radix».call h![N] h![f, radix])
    fun r => r = ⟨decomposeToRadix radix.toNat f.val (by assumption) |>.takeD N.toNat 0, by simp⟩ := by
  enter_decl
  steps
  fapply STHoare.letIn_intro
  · exact fun _ => ⟦⟧
  · apply STHoare.iteTrue_intro
    steps
  intro
  steps
  rename_i _ _ v_eq
  exact v_eq

theorem to_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 256 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  enter_decl
  steps
  steps [to_le_radix_intro (N := N) (f := f) (radix := 256)]
  fapply STHoare.letIn_intro
  · exact fun _ => ⟦⟧
  · apply STHoare.iteTrue_intro
    steps
    simp_all
    loop_inv nat
      (fun _ _ _ => ∃∃b, ([ok ↦ ⟨Tp.bool, b⟩]))
    rotate_left
    simp
    exact ⟦⟧
    rotate_right
    simp
    apply SLP.exists_intro_r
    exact SLP.entails_self

    -- loop body
    intros i hlo hhi
    steps
    apply STHoare.ite_intro
    · intro h₁
      steps
      apply STHoare.ite_intro
      · intro h₂
        steps
      · intro h₂
        steps
    · intro
      steps
    steps
  intro v
  steps
  simp_all
