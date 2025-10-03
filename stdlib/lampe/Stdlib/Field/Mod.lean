import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

set_option Lampe.pp.Expr true

open «std-1.0.0-beta.12» (env)

theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 2 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  sorry
  -- enter_decl
  -- steps
  -- simp only [Bool.not_false]
  -- fapply STHoare.letIn_intro
  -- · rename_i a b
  --   exact fun _ => bits = ⟨decomposeToRadix 2 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩
  -- apply STHoare.ite_intro_of_true
  -- · rfl
  -- · steps
  --   simp_all
  --   subst_vars
  --   loop_inv nat (fun i hi hlo => [ok ↦ ⟨Tp.bool, if f.val < p.val then true else false⟩])
    -- · congr
    --   simp_all
    -- · intros i hi hlo
    --   steps
  -- · apply STHoare.ite_intro_of_false
  --   rfl
  --   steps
  --   assumption
  -- intro v
  -- steps
  -- simp_all

theorem to_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
    fun r => r = ⟨decomposeToRadix 256 f.val (by linarith) |>.takeD N.toNat 0, by simp⟩ := by
  sorry

open «std-1.0.0-beta.12»
