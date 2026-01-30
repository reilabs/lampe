import Lampe
import ProvenZk
import «skyscraper-0.0.0».Extracted
import «skyscraper-0.0.0».Field
import «skyscraper-0.0.0».Ref

import Stdlib.Stdlib
import Mathlib.Data.Vector.Defs

open Lampe

namespace Skyscraper

open Skyscraper.Field (lp)
open «skyscraper-0.0.0» (env)

section utils

def _root_.List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
| 0, _ => List.Vector.nil
| d+1, 0 => pad ::ᵥ List.Vector.pad v d pad
| d+1, _+1 => v.head ::ᵥ List.Vector.pad v.tail d pad

@[simp]
theorem List.Vector.toList_pad {v : List.Vector α n} {pad} : (v.pad d pad).toList = v.toList.takeD d pad := by
  rcases v with ⟨l, prop⟩
  induction d generalizing l n with
  | zero => simp
  | succ d ih =>
    cases n
    · simp [List.Vector.pad, ih, List.replicate_succ]
    · rcases (List.exists_of_length_succ _ prop) with ⟨h, t, ⟨rfl⟩⟩
      simp at prop
      simp [List.Vector.pad, List.Vector.head, List.Vector.tail, ih]

theorem List.takeD_eq_take_append : List.takeD n l pad = List.take n l ++ List.replicate (n - l.length) pad := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l
    · simp [List.replicate]
    · simp [List.takeD, List.take, ih]

lemma List.Vector.getElem_toList {v : List.Vector α n} {i : Nat} (hi : i < n) :
    v[i] = v.toList[i]'(by simpa [List.Vector.toList_length] using hi) := by
  simp [List.Vector.getElem_def]

end utils

section globals

theorem sigma_intro : STHoare lp env (⟦⟧) («skyscraper-0.0.0::globals::SIGMA».call h![] h![])
    fun output => output = Ref.SIGMA := by
  enter_decl
  steps []
  unfold Ref.SIGMA
  assumption

theorem rc_intro : STHoare lp env (⟦⟧) («skyscraper-0.0.0::globals::RC».call h![] h![])
    fun output => output = ⟨Ref.RC.toList, by rfl⟩ := by
  enter_decl
  steps []
  subst_vars
  unfold Ref.RC
  rfl

end globals

section components

theorem rl_intro : STHoare lp env ⟦⟧
    («skyscraper-0.0.0::components::rl».call h![] h![input])
    fun output => output = Ref.rl input := by
  enter_decl
  steps
  subst_vars
  rfl

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
      («skyscraper-0.0.0::components::rotate_left».call h![] h![input, N])
      fun output => output = Ref.rotateLeft input N := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Ref.rl i input⟩]
  change 0 ≤ N
  · bv_decide
  · intros i hlo hhi
    steps [rl_intro]
  · steps
    simp_all [Ref.rotateLeft]

theorem sbox_intro : STHoare lp env ⟦⟧
    («skyscraper-0.0.0::components::sbox».call h![] h![input])
    fun output => output = Ref.sbox input := by
  enter_decl
  steps [rotate_left_intro]
  · subst_vars; rfl
  all_goals decide

theorem square_intro : STHoare lp env (⟦⟧)
    («skyscraper-0.0.0::components::square».call h![] h![input])
    fun output => output = Ref.square input := by
  enter_decl
  steps [sigma_intro]
  unfold Ref.square
  subst_vars
  rfl

end components

section bar

set_option maxHeartbeats 800000 in
open Lampe.Stdlib.Field Lampe.Stdlib.Slice in
theorem bar_intro : STHoare lp env ⟦⟧ («skyscraper-0.0.0::bar::bar».call h![] h![input])
    fun output => output = Ref.bar input := by
  enter_decl
  simp only [«skyscraper-0.0.0::bar::bar»]
  steps [Lampe.Stdlib.Field.to_le_bytes_intro]
  rename_i hlt bytes_def
  have hlt' : ZMod.val input < 256 ^ 32 := by
    simpa [BitVec.toNat_ofNat] using hlt
  have hbytes : Fp.toBytesLE 32 input = bytes := by
      simpa [bytes_def, List.map_reverse] using (Fp.toBytesLE_eq_toDigitsLE_of_lt (x := input) (n := 32) hlt')
  step_as
    ([new_left ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take 16 |>.map Ref.sbox⟩])
  · loop_inv fun i _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Ref.sbox |>.pad 16 (0:U 8)⟩]
    · decide
    · congr 1
      apply List.Vector.eq
      simp [-List.takeD_succ, List.takeD_eq_take_append, Int.cast, IntCast.intCast]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps [sbox_intro]
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      have : i + 1 < 4294967296 := by
        linarith
      congr 1
      apply List.Vector.eq
      simp [-List.takeD_zero, -List.takeD_succ, Access.modify, List.Vector.get, Fin.add_def, Nat.mod_eq_of_lt, this]
      have i₁ : i ≤ 32 := by linarith
      have i₂ : i + 1 ≤ 32 := by linarith
      have i₃ : i ≤ 16 := by linarith
      have i₄ : i + 1 ≤ 16 := by linarith
      have i₅ : i < 32 := by linarith
      simp [-List.takeD_zero, -List.takeD_succ,
        List.takeD_eq_take_append,
        List.take_take,
        i₁, i₂, i₃, i₄]
      simp only [List.take_succ, List.append_assoc]
      have : (16 - i) = (15 - i) + 1 := by omega
      simp only [this, List.replicate_succ, getElem?, decidableGetElem?, i₅, List.Vector.toList]
      simp_all only [Int.cast_zero, BitVec.ofNat_eq_ofNat, Nat.reducePow, BitVec.le_ofFin,
      BitVec.toFin_ofNat, Fin.ofNat_eq_cast, Nat.cast_zero, Fin.isValue, Fin.zero_le, Lens.modify,
      Lens.get, BitVec.toNat_ofFin, BitVec.reduceToNat, Builtin.instCastTpU,
      BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, Option.bind_eq_bind,
      Option.bind_some, Nat.reduceLeDiff, List.set_cons_zero, List.get?Internal_eq_getElem?,
      List.length_map, List.Vector.length_val, BitVec.toNat_ofNat, Nat.reduceMod,
      List.getElem?_eq_getElem, List.getElem_map, Option.toList_some, List.cons_append,
      List.nil_append]

  steps

  step_as
    ([new_right ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.map Ref.sbox⟩])

  · loop_inv fun i _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Ref.sbox |>.pad 16 (0:U 8)⟩]
    · decide
    · congr 1
      apply List.Vector.eq
      simp [-List.takeD_succ, Int.cast, IntCast.intCast, List.takeD_eq_take_append, List.take_take]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps [sbox_intro]
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      simp [-List.takeD_zero, -List.takeD_succ, Builtin.CastTp.cast, Access.modify]
      congr 1
      apply List.Vector.eq
      simp [-List.takeD_zero, -List.takeD_succ, -List.map_drop, List.Vector.get, Fin.add_def, Int.cast, IntCast.intCast, OfNat.ofNat]
      have : 16 + i < 4294967296 := by linarith
      have : i + 1 < 4294967296 := by linarith
      simp only [Nat.mod_eq_of_lt, *, List.getElem_drop']
      simp only [List.takeD_eq_take_append]
      have i₁ : i ≤ 16 := by linarith
      have i₂ : i + 1 ≤ 16 := by linarith
      simp [i₁, i₂, List.take_take]
      simp only [List.take_succ, List.append_assoc]
      congr 1
      have : (16 - i) = (15 - i) + 1 := by omega
      simp only [this, List.replicate_succ, List.set_cons_zero, decidableGetElem?,
      List.length_drop, List.length_map, List.Vector.toList_length, Nat.reduceSub,
      List.getElem_drop, List.getElem_map]

      have : (List.drop 16 (List.map Ref.sbox (List.Vector.toList bytes)))[i]? =
        (if h : i < 16 then
          have : 16 + i < (List.Vector.toList bytes).length := by simp; linarith
          some (Ref.sbox (List.Vector.toList bytes)[16 + i] : U 8) else none)
        := by
          simp_all only [Int.cast_zero, BitVec.ofNat_eq_ofNat, Nat.reducePow, BitVec.le_ofFin, BitVec.toFin_ofNat,
            Fin.ofNat_eq_cast, Nat.cast_zero, Fin.isValue, Fin.zero_le, Int.cast_ofNat, BitVec.reduceToInt,
            Int.reducePow, Lens.modify, Lens.get, BitVec.toNat_ofFin, BitVec.reduceToNat, Nat.reduceSub,
            Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_ofFin,
            Nat.cast_ofNat, Option.bind_eq_bind, Option.bind_some, Nat.reduceLeDiff, List.length_drop,
            List.length_map, List.Vector.toList_length, List.getElem?_eq_getElem, List.getElem_drop,
            List.getElem_map, ↓reduceDIte]

      rw [this]

      simp only [hlt, dite_true, Option.toList]
      simp [List.cons_append, List.nil_append, List.Vector.toList]
      have hidx : 16 + i < 32 := by linarith
      have hidx' : 16 + i < (List.Vector.toList bytes).length := by
        simpa [List.Vector.toList_length] using hidx
      have hget : bytes[16 + i] = bytes.toList[16 + i] := by
        simpa [List.get_eq_getElem, hidx'] using
          (List.Vector.getElem_toList (v := bytes) (i := 16 + i) (hi := hidx))
      simpa using congrArg Ref.sbox hget


  steps

  step_as v =>
    ( [new_bytes ↦ ⟨(Tp.u 8).slice, List.Vector.toList v⟩ ] ⋆
    [ new_right ↦ ⟨(Tp.u 8).array 16, List.Vector.map Ref.sbox (List.Vector.drop 16 bytes)⟩ ] ⋆
      [ new_left ↦ ⟨(Tp.u 8).array 16, List.Vector.map Ref.sbox (List.Vector.take 16 bytes)⟩ ])
    (fun _ => [new_bytes ↦ ⟨(Tp.u 8).slice, v.toList ++ (List.Vector.map Ref.sbox (List.Vector.take 16 bytes)).toList⟩])
  steps

  · loop_inv fun i _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice,  (List.Vector.map Ref.sbox (List.Vector.drop 16 bytes)).toList ++ ζi0.toList.take i.toNat⟩]
    · subst_vars; simp
    · simp [*]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps
      simp
      congr 1
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      have : i + 1 < 4294967296 := by
        simp_all
        linarith
      simp [Nat.mod_eq_of_lt, this, List.take_succ]
      have hlt' : i < 16 := by simp_all
      simp_all [List.Vector.toList_length, hlt', ↓reduceDIte, Option.toList_some, List.cons.injEq, and_true, List.Vector.get_eq_get_toList]
    · subst_vars
      steps
  steps [Lampe.Stdlib.Slice.as_array_spec, Lampe.Stdlib.Field.from_le_bytes_intro]

  all_goals subst_vars
  show Fp.ofBytesLE (List.Vector.toList new_bytes_array) = Ref.bar input
  unfold Ref.bar
  rw [hbytes]
  congr 1

end bar

section permute

theorem permute_intro : STHoare lp env ⟦⟧
    («skyscraper-0.0.0::permute::permute».call h![] h![i])
    fun output =>
      output = (Ref.State.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Ref.State.permute ⟨i[0], i[1]⟩).2 ::ᵥ .nil
    := by
  enter_decl
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn
  steps [bar_intro, square_intro, rc_intro]
  simp [Builtin.indexTpl, Nat.mod_eq_of_lt, Field.lp] at *
  subst_vars
  rfl

end permute
