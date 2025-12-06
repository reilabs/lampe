import Lampe
import «skyscraper-0.0.0».Extracted

open Lampe

open «std-1.0.0-beta.12» (env)

namespace Stdlib.Slice

set_option maxRecDepth 1000 in
theorem as_array_intro input (hi : input.length = 32) : STHoare lp env ⟦⟧
    («std-1.0.0-beta.12::slice::as_array».call h![Tp.u 8, 32] h![input])
    fun output => output = ⟨input, hi⟩ := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => ∃∃v, [array ↦ ⟨Tp.array (Tp.u 8) 32, v⟩] ⋆ (v.toList = input.take i ++ List.replicate (32 - i) 0#8)
  sl
  · simp; rfl
  · simp
  · intro i hlo hhi
    steps
    have : i < 32 := by assumption
    have : 32 - i = (31 - i) + 1 := by omega
    simp_all only [Int.cast_zero, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.zero_mod, zero_le, BitVec.reduceToNat, List.replicate_succ, Lens.modify, Lens.get,
      Access.modify, BitVec.toNat_ofNatLT, Nat.reduceMod, ↓reduceDIte, Builtin.instCastTpU,
      BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.get_eq_getElem,
      Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some, Option.get_some,
      List.Vector.toList_set, List.length_take, min_eq_left_of_lt, le_refl, List.set_append_right,
      tsub_self, List.set_cons_zero, Nat.reduceSubDiff]
    rw [List.take_succ_eq_append_getElem]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    simp_all
  steps
  apply List.Vector.eq
  simp_all [-List.takeD_succ, List.takeD_eq_take]
