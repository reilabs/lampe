import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

set_option Lampe.pp.Expr true

open «std-1.0.0-beta.12» (env)

theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 2 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  enter_decl
  steps
  simp only [Bool.not_false]
  fapply STHoare.letIn_intro
  · exact fun _ => ⟦⟧
  apply STHoare.ite_intro_of_true
  · rfl
  · steps
    simp_all
    rename' p => p_slice
    rename p_slice = _ => p_slice_val
    rename p_slice.length < _ => p_slice_len
    rename bits = _ => bits_val
    rename N ≤ _ => N_le
    loop_inv nat (fun i hhi (hlo : i ≤ N.toNat) => [ok ↦
      ⟨Tp.bool, (decomposeToRadix 2 p.val (by linarith)).length != N.toNat ∨
      decide (∃ (j : Fin i),
        (decomposeToRadix 2 f.val (by linarith)).get ⟨j, by
          rcases j with ⟨j, hj⟩
          simp only
          rw [BitVec.le_def] at N_le
          simp at N_le
          sorry -- This should reduce to just a linarith, but I might be missing some hypotheses?
        ⟩ != (decomposeToRadix 2 p.val (by linarith)).get ⟨j, by
          rcases j with ⟨j, hj⟩
          simp only
          rw [BitVec.le_def] at N_le
          simp at N_le
          sorry -- Also just a linarith
        ⟩ )⟩])
    · congr
      simp
      conv in decide (∃ j, _) =>
        equals false =>
          simp
          rintro ⟨x, hx⟩
          simp [BitVec.toNat_ofNat _] at hx
      simp
      constructor <;> {intro h; simp [h]}
    · simp
    · intro i hlo hhi
      steps
      apply STHoare.ite_intro
      · intro h
        steps
        apply STHoare.ite_intro
        · intro h₁
          steps
          congr 1
          simp_all
          use ⟨i, by linarith⟩
          rename_i h₂
          -- This is the `ok == false` and `bits[N - 1 -i] = p[N - 1 - i]` case, so it should be that
          -- we use `h₁` and `h₂` to show that `f.val` and `p.val` differ at position `i`.
          sorry
        · intro h₁
          steps
          congr 5
          simp
          constructor
          · rintro ⟨⟨x, hhx⟩, hhx⟩
            use ⟨x, (by linarith)⟩
          · rintro ⟨⟨x, hhx⟩, hhx'⟩
            -- This is the `ok == false` and `bits[N - 1 - i] != p[N - 1 - i]`
            sorry
      · intro h
        steps
        congr 5
        simp
        constructor
        · rintro ⟨⟨x, hhx⟩, hhx'⟩
          use ⟨x, (by linarith)⟩
        · rintro ⟨⟨x, hhx⟩, hhx'⟩
          -- This is the `ok == true` case, so we should have already gotten a case where
          -- `bits[N - 1 - i] != p[N - 1 - i]`.
          sorry
    steps
  intro v
  steps
  simp_all

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
    sorry
  intro v
  steps
  simp_all
