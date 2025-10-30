import Lampe
import «skyscraper-0.0.0».Extracted

open Lampe

open «std-1.0.0-beta.12» (env)

namespace Stdlib.Field

theorem to_le_bytes_intro {input} : STHoare lp env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![32] h![input])
    fun v => v = Fp.toBytesLE 32 input := by
  sorry

theorem from_le_bytes_intro {input} : STHoare lp env ⟦⟧
    («std-1.0.0-beta.12::field::from_le_bytes».call h![32] h![input])
    fun output => output = Lampe.Fp.ofBytesLE input.toList := by
  sorry
