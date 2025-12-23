import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

-- idk where to put this one cuz i don't want to create circular dependency
-- but bn254 depends on it as does mod
theorem assert_max_bit_size_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::assert_max_bit_size».call h![BIT_SIZE] h![f])
    (fun r => ∃∃ h : f.val < 2 ^ BIT_SIZE.toNat, r = ()) := by
  enter_decl
  steps
  all_goals
    simp_all

end Lampe.Stdlib.Field
