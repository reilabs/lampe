import «std-1.0.0-beta.12».Extracted.Array.Mod
import «std-1.0.0-beta.12».Extracted.«std-1.0.0-beta.12»
import Lampe

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.12».Extracted (
  «std::array::map»
  «std::array::mapi»
  «std::array::for_each»
  «std::array::for_eachi»
  «std::array::fold»
  «std::array::reduce»
  «std::array::all»
  «std::array::any»
  «std::array::concat»
  «std::array::sort»
  «std::array::sort_via»
  «std::array::test::map_empty»
  Array.Mod.env
)

open «std-1.0.0-beta.12».Extracted

namespace Array

theorem concat_spec: STHoare p env ⟦⟧
    («std::array::concat».call h![T, M, N] h![a₁, a₂])
    (fun r => r.toList = a₁.toList ++ a₂.toList) := by
  enter_decl
  steps

  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨T.array (M + N), v⟩] ⋆ (v.toList.take i = a₁.toList.take i)
  · sl
    simp
  · simp
  · intro i hil hiu
    steps
    rename Option.isSome _ = true => hp
    simp at hp
    rw [List.take_succ_eq_append_getElem ?lt1, List.take_succ_eq_append_getElem ?lt2]
    case lt1 => simp_all
    case lt2 => simp_all
    simp only [BitVec.toNat_add, Nat.reducePow, BitVec.add_eq, Lens.modify, Lens.get, Access.modify,
      BitVec.toNat_ofNatLT, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.get_dite, List.Vector.toList_set, le_refl, List.take_set_of_le, List.getElem_set_self]
    congr

  steps

  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨T.array (M + N), v⟩] ⋆ (v.toList.take (M.toNat + i) = a₁.toList ++ a₂.toList.take i)
  · sl
    simp_all
  · simp
  · intro i hil hiu
    steps
    rw [←add_assoc, List.take_succ, List.take_succ, ←List.append_assoc]
    have : i_3710.toNat = M.toNat + i := by
      subst i_3710
      simp only [BitVec.toNat_add]
      rw [Nat.mod_eq_of_lt (by assumption), add_comm]
      rfl
    congr 1
    · simp [this]
      rw [List.take_set_of_le (by simp)]
      assumption
    simp only [BitVec.toNat_add, Nat.reducePow, BitVec.add_eq, Lens.modify, Lens.get, Access.modify,
      Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.get_dite, List.Vector.toList_set]

    rw [List.getElem?_set, this]
    rename Option.isSome _ = true => hp
    simp [this] at hp
    simp [*]
    rfl
  steps
  rename List.take _ _ = _ ++ _ => hp
  rw [List.take_of_length_le ?le1, List.take_of_length_le ?le2] at hp
  case le1 => simp [Nat.mod_le]
  case le2 => simp
  simp_all
