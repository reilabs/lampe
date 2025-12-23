import «std-1.0.0-beta.12».Extracted
import Lampe
import Lampe.Builtin.Helpers
import Stdlib.Field.Basic
import Stdlib.Field.Bn254
import Stdlib.Compat
import Stdlib.Ext

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

lemma bits_lt_of_lex_lt {data pdata : List (BitVec 1)}
    (hlen : data.length = pdata.length)
    (hlt : data < pdata)
    (hpdata : pdata = List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop)
      (RadixVec.toDigitsBE' 2 p)) :
    RadixVec.ofDigitsBE' (data.map (fun i => (i.toFin : Digit 2))) < p := by
  rw [←RadixVec.ofDigitsBE'_toDigitsBE' (r := 2) (n := p)]
  apply RadixVec.ofDigitsBE'_mono
  · simp [hlen, hpdata, List.length_map]
  · have hself : RadixVec.toDigitsBE' 2 p =
        List.map (fun (i : BitVec 1) => (i.toFin : Digit 2))
          (List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop)
            (RadixVec.toDigitsBE' 2 p)) := by
      rw [List.map_map, eq_comm]
      convert List.map_id _
    rw [hself]
    apply List.map_lt
    · intro x y h
      rw [BitVec.lt_def] at h
      rw [Fin.lt_def]
      exact h
    · rw [hpdata] at hlt
      exact hlt

lemma bytes_lt_of_lex_lt {data pdata : List (BitVec 8)}
    (hlen : data.length = pdata.length)
    (hlt : data < pdata)
    (hpdata : pdata = List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop)
      (RadixVec.toDigitsBE' ⟨256, by decide⟩ p)) :
    RadixVec.ofDigitsBE' (data.map (fun i => (i.toFin : Digit ⟨256, by decide⟩))) < p := by
  rw [←RadixVec.ofDigitsBE'_toDigitsBE' (r := ⟨256, by decide⟩) (n := p)]
  apply RadixVec.ofDigitsBE'_mono
  · simp [RadixVec.toDigitsBE', hlen, hpdata, List.length_map]
  · have hself : RadixVec.toDigitsBE' ⟨256, by decide⟩ p =
        List.map (fun (i : BitVec 8) => i.toFin)
          (List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop)
            (RadixVec.toDigitsBE' ⟨256, by decide⟩ p)) := by
      simp only [List.map_map]
      rw [eq_comm]
      convert List.map_id _
    rw [hself]
    apply List.map_lt
    · intro x y h
      rw [BitVec.lt_def] at h
      rw [Fin.lt_def]
      exact h
    · rw [hpdata] at hlt
      exact hlt

lemma ofDigitsBE'_lt_of_shorter_than_modulus {r : Radix} {data : List (Digit r)} {P : Prime}
    (hlen : data.length < (RadixVec.toDigitsBE' r P.natVal).length) :
    RadixVec.ofDigitsBE' data < P.natVal := by
  have hr : 1 < r.val := r.prop
  calc RadixVec.ofDigitsBE' data
      < r.val ^ data.length := RadixVec.ofDigitsBE'_lt
    _ ≤ r.val ^ ((RadixVec.toDigitsBE' r P.natVal).length - 1) := by
      apply Nat.pow_le_pow_right (Nat.le_of_lt hr)
      apply Nat.le_pred_of_lt hlen
    _ = r.val ^ Nat.log r.val P.natVal := by simp [RadixVec.toDigitsBE']
    _ ≤ P.natVal := by
      apply Nat.pow_log_le_self
      simp [Prime.natVal]

theorem to_be_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_be_bits».call h![N] h![f])
    fun r => ∃∃(lt : f.val < (2 ^ N.toNat)),
      r = (RadixVec.toDigitsBE (d := N.toNat) (r := 2)
        ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin) := by
  rcases N with ⟨⟨N,_⟩⟩
  enter_decl
  steps
  · exact ()
  step_as (⟦⟧)
    (fun _ => RadixVec.ofDigitsBE' (bits.toList.map (fun i => (i.toFin : Digit 2))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbits
    by_cases h: bits.length = pbits.length
    · cases' bits with bits bitsLen
      simp only [BitVec.toNat_ofFin] at bitsLen
      cases bitsLen
      loop_inv nat fun i _ _ =>
        (bits.take i ≤ pbits.take i) ⋆ [ok ↦ ⟨_, decide <| bits.take i < (pbits.take i)⟩]
      · simp
      · simp only [h]
        simp [BitVec.ofNatLT_eq_ofNat]
      · simp
      · intro i _ _
        steps
        by_cases h: bits.take i < pbits.take i
        · simp only [h]
          apply STHoare.iteFalse_intro
          have : bits.take (i + 1) < pbits.take (i + 1) :=
            List.take_succ_lt_of_take_lt (by simp_all) (by simp_all) h
          steps
          · exact List.le_of_lt this
          · simp_all
        · simp only [h]
          apply STHoare.iteTrue_intro
          rename bits.take i ≤ pbits.take i => hle
          have : bits.take i = pbits.take i := by
            rw [List.le_iff_lt_or_eq] at hle
            tauto
          steps
          by_cases hi : bits[i] = pbits[i]
          · convert STHoare.iteFalse_intro _
            · simp [List.Vector.get, hi]
            · rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [this, hi]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp [List.Vector.get, hi]
            · steps 7
              have hpbit : pbits[i] = 1 := by simp_all [Int.cast, IntCast.intCast]
              have hbit : bits[i] = 0 := by have := U.cases_one bits[i]; simp_all
              have bitle : bits[i] < pbits[i] := by simp [hpbit, hbit]
              have : bits.take (i + 1) < pbits.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt (by assumption) (by assumption) this bitle
              steps
              · exact List.le_of_lt this
              · congr
                simp [this]
      steps
      rename decide _ = true => hlt
      have : bits.length = pbits.length := by simp_all
      simp only [BitVec.toNat_ofFin, List.take_length, beq_true, decide_eq_true_eq] at hlt
      simp only [this, List.take_length] at hlt
      apply bits_lt_of_lex_lt this hlt
      subst pbits
      rfl
    · loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [
          BitVec.toNat_ne, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
          List.Vector.length,
        ]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bits.length < pbits.length := by
        apply lt_of_le_of_ne
        · simp only [
            BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
            List.Vector.length,
          ] at *
          simp_all
        · assumption
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      subst pbits
      simp_all
  steps
  rotate_left
  · rename_i v _
    subst_vars
    simp
    rw [ZMod.val_natCast]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    apply RadixVec.ofDigitsBE_lt
  · rename_i h v _
    subst_vars
    simp only [←List.Vector.toList_map, RadixVec.ofDigitsBE'_toList] at h
    conv_rhs =>
      enter [2, 1, 1]
      rw [ZMod.val_natCast]
      rw [Nat.mod_eq_of_lt h]
    apply List.Vector.eq
    rw [eq_comm]
    simp only [
      BitVec.toNat_ofFin, Fin.eta, RadixVec.toDigitsBE_ofDigitsBE,
      List.Vector.toList_map, List.map_map
    ]
    convert List.map_id _

theorem to_be_radix_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_be_radix».call h![N] h![f, 256])
    fun o =>
      ∃∃ (v : List.Vector (Digit ⟨256, by decide⟩) N.toNat),
      o = v.map BitVec.ofFin ⋆
      f = RadixVec.ofDigitsBE v := by
  enter_decl
  steps
  · exact ()
  apply STHoare.letIn_intro
  apply STHoare.iteTrue_intro
  · steps
    apply STHoare.skip_intro
  intro _
  steps
  case v =>
    rename_i v _
    exact v.map BitVec.toFin
  · apply List.Vector.eq
    simp
    rw [eq_comm]
    exact List.map_id _
  · subst_vars
    rw [RadixVec.ofDigitsBE]
    congr 2
    apply List.Vector.eq
    simp

theorem to_le_radix_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_radix».call h![N] h![f, 256])
    fun o =>
      ∃∃ (v : List.Vector (Digit ⟨256, by decide⟩) N.toNat),
      o = v.reverse.map BitVec.ofFin ⋆
      f = RadixVec.ofDigitsBE v := by
  enter_decl
  steps
  · exact ()
  apply STHoare.letIn_intro
  apply STHoare.iteTrue_intro
  · steps
    apply STHoare.skip_intro
  intro _
  steps
  case v =>
    rename_i v _
    exact v.reverse.map BitVec.toFin
  · apply List.Vector.eq
    simp [List.Vector.toList_reverse, Function.comp_def]
  · subst_vars
    simp only [BitVec.ofNat_eq_ofNat]
    congr 2
    apply List.Vector.eq
    simp [List.Vector.toList_reverse, BitVec.toFin, Fin.val_mk]

theorem to_be_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_be_bytes».call h![N] h![f])
    fun o =>
      ∃∃(lt : f.val < (256 ^ N.toNat)), o = (RadixVec.toDigitsBE
        (d := N.toNat)
        (r := ⟨256,  by decide⟩)
        ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin) := by
  rcases N with ⟨⟨N, _⟩⟩
  enter_decl
  steps [to_be_radix_intro]
  · exact ()
  step_as (⟦⟧) (fun _ =>
    RadixVec.ofDigitsBE' (bytes.toList.map (fun i => (i.toFin : Digit ⟨256, by decide⟩)))
      < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbytes  -- pbytes is the modulus bytes slice
    by_cases h: bytes.length = pbytes.length
    · cases' bytes with bytes bytesLen
      simp only [BitVec.toNat_ofFin] at bytesLen
      cases bytesLen
      loop_inv nat fun i _ _ =>
        (bytes.take i ≤ pbytes.take i) ⋆
          [ok ↦ ⟨_, decide <| bytes.take i < (pbytes.take i)⟩]
      · simp
      · simp only [h]
        simp [BitVec.ofNatLT_eq_ofNat]
      · simp
      · intro i _ _
        steps
        by_cases h: bytes.take i < pbytes.take i
        · simp only [h]
          apply STHoare.iteFalse_intro
          have : bytes.take (i + 1) < pbytes.take (i + 1) :=
            List.take_succ_lt_of_take_lt (by simp_all) (by simp_all) h
          steps
          · exact List.le_of_lt this
          · simp_all
        · simp only [h]
          apply STHoare.iteTrue_intro
          rename bytes.take i ≤ pbytes.take i => hle
          have heq : bytes.take i = pbytes.take i := by
            rw [List.le_iff_lt_or_eq] at hle
            tauto
          steps
          by_cases hi : bytes[i] = pbytes[i]
          · convert STHoare.iteFalse_intro _
            · simp [List.Vector.get, hi]
            · rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [List.take_succ_eq_append_getElem (by assumption)]
              rw [heq, hi]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp [List.Vector.get, hi]
            · steps 7
              rename_i hlt_byte
              have hbyte_lt : bytes[i] < pbytes[i] := by
                simp only [beq_true, decide_eq_true_eq, BitVec.lt_def] at hlt_byte ⊢
                convert hlt_byte using 2
              have : bytes.take (i + 1) < pbytes.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt (by assumption) (by assumption) heq hbyte_lt
              steps
              · exact List.le_of_lt this
              · congr
                simp [this]
      steps
      rename decide _ = true => hlt
      have hlen : bytes.length = pbytes.length := by simp_all
      simp [BitVec.toNat_ofFin] at hlt
      simp [hlen] at hlt
      have hpbytes_eq : pbytes =
          List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop)
            (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal) := by
        subst pbytes
        simp only [RadixVec.toDigitsBE', List.do_pure_eq_map]
        congr 1
        funext x
        simp [BitVec.ofNatLT, BitVec.ofFin]
      apply bytes_lt_of_lex_lt hlen hlt hpbytes_eq
    · loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [BitVec.toNat_ne, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bytes.length < pbytes.length := by
        apply lt_of_le_of_ne
        · simp_all
        · assumption
      have hpbytes_len :
          pbytes.length = (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal).length := by
        subst pbytes
        simp [RadixVec.toDigitsBE']
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      simp [List.Vector.toList_length, hpbytes_len] at hlen_lt ⊢
      exact hlen_lt
  steps
  rotate_left
  · rename_i v _
    subst_vars
    simp
    rw [ZMod.val_natCast]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    apply RadixVec.ofDigitsBE_lt
  · rename_i h v _
    subst_vars
    simp only [←List.Vector.toList_map, RadixVec.ofDigitsBE'_toList] at h
    rw [List.Vector.map_toFin_map_ofFin] at h
    conv_rhs =>
      enter [2, 1, 1]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]
    apply List.Vector.eq
    simp [RadixVec.toDigitsBE_ofDigitsBE]

set_option maxHeartbeats 300000
theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => ∃∃(lt : f.val < (2 ^ N.toNat)),
      r = (RadixVec.toDigitsBE (d := N.toNat) (r := 2)
        ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin |>.reverse) := by
  rcases N with ⟨⟨N,_⟩⟩
  enter_decl
  steps
  · exact ()
  step_as (⟦⟧) (fun _ =>
    RadixVec.ofDigitsBE' (bits.toList.reverse.map (fun i => (i.toFin : Digit 2))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbits
    by_cases h: bits.length = pbits.length
    · cases' bits with bits bitsLen
      simp only [BitVec.toNat_ofFin] at bitsLen
      cases bitsLen
      loop_inv nat fun i _ _ =>
        (bits.reverse.take i ≤ pbits.reverse.take i) ⋆
          [ok ↦ ⟨_, decide <| bits.reverse.take i < (pbits.reverse.take i)⟩]
      · simp
      · simp only [h]
        simp [BitVec.ofNatLT_eq_ofNat]
      · simp
      · intro i _ _
        steps
        by_cases hlt: bits.reverse.take i < pbits.reverse.take i
        · simp only [hlt]
          apply STHoare.iteFalse_intro
          have : bits.reverse.take (i + 1) < pbits.reverse.take (i + 1) :=
            List.take_succ_lt_of_take_lt (by simp_all) (by simp_all) hlt
          steps
          · exact List.le_of_lt this
          · simp_all
        · simp only [hlt]
          apply STHoare.iteTrue_intro
          rename bits.reverse.take i ≤ pbits.reverse.take i => hle
          have heq : bits.reverse.take i = pbits.reverse.take i := by
            rw [List.le_iff_lt_or_eq] at hle
            tauto
          have hi_lt_bits : i < bits.reverse.length := by simp_all [List.length_reverse]
          have hi_lt_pbits : i < pbits.reverse.length := by simp_all [List.length_reverse]
          steps
          have hi_lt : i < bits.length := by simp_all [List.length_reverse]
          have hlen_eq : bits.length = pbits.length := by simp_all
          have hlen32 : bits.length < 2^32 := by simp_all
          have hi32 : i < 2^32 := Nat.lt_trans hi_lt hlen32
          have hidx := U32.index_toNat bits.length i hlen32 hi32 hi_lt
          by_cases hi : bits.reverse[i]'hi_lt_bits = pbits.reverse[i]'hi_lt_pbits
          · convert STHoare.iteFalse_intro _
            · simp [List.Vector.get, h, hlen_eq] at hi ⊢
              simp_all [List.get_eq_getElem]
            · rw [
                List.take_succ_eq_append_getElem hi_lt_bits,
                List.take_succ_eq_append_getElem hi_lt_pbits,
                heq, hi
              ]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp [List.Vector.get, List.length_reverse, h, hlen_eq] at hi ⊢
              simp_all [List.get_eq_getElem]
            · steps 9
              rename_i hassert
              have hpbit : pbits[pbits.length - 1 - i] = 1 := by
                simp only [beq_true, decide_eq_true_eq, List.get_eq_getElem] at hassert
                convert hassert using 2
                rw [←hlen_eq]
                exact hidx.symm
              have hbit : bits[bits.length - 1 - i] = 0 := by
                have := U.cases_one bits[bits.length - 1 - i]
                simp_all
              have hbit_lt : bits.reverse[i]'hi_lt_bits < pbits.reverse[i]'hi_lt_pbits := by
                simp [hpbit, hbit]
              have : bits.reverse.take (i + 1) < pbits.reverse.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt hi_lt_bits hi_lt_pbits heq hbit_lt
              steps
              · exact List.le_of_lt this
              · simp [this]
      steps
      rename decide _ = true => hlt_final
      have hlen : bits.length = pbits.length := by simp_all
      simp [
        BitVec.toNat_ofFin, List.take_length, List.length_reverse
      ] at hlt_final
      simp only [hlen, List.take_length, List.length_reverse] at hlt_final
      have hlt_full : bits.reverse < pbits.reverse :=
        List.lt_of_take_lt (by simp [hlen]) (by simp) hlt_final
      have hpbits_rev : pbits.reverse =
          List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop)
            (RadixVec.toDigitsBE' 2 p.natVal) := by
        subst pbits
        simp only [
          RadixVec.toDigitsBE', RadixVec.of,
          List.do_pure_eq_map, List.map_map,
          List.map_reverse, List.reverse_reverse
        ]
        congr 1
        funext x
        simp [BitVec.ofNatLT, BitVec.ofFin]
      have hlen_rev : bits.reverse.length = pbits.reverse.length := by
        simp [List.length_reverse, hlen]
      apply bits_lt_of_lex_lt hlen_rev (hpbits_rev ▸ hlt_full) hpbits_rev
    ·
      loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [
          BitVec.toNat_ne, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat
        ]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bits.length < pbits.length := by
        apply lt_of_le_of_ne
        · simp only [
            BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq
          ] at *
          simp_all
        · assumption
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      subst pbits
      simp [RadixVec.toDigitsBE'] at hlen_lt ⊢
      exact hlen_lt
  steps
  rotate_left
  · rename_i v _
    subst_vars
    simp
    rw [ZMod.val_natCast]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    apply RadixVec.ofDigitsBE_lt
  ·
    rename_i h v _
    subst_vars
    simp [
      ←List.Vector.toList_map, List.Vector.toList_reverse,
      ←RadixVec.ofDigitsBE'_toList,
    ] at h
    conv_rhs =>
      enter [1, 2, 1, 1]
      rw [ZMod.val_natCast]
      simp [
        ←List.Vector.toList_map, List.Vector.toList_reverse,
        ←RadixVec.ofDigitsBE'_toList
      ]
      rw [Nat.mod_eq_of_lt h]
    conv_rhs =>
      enter [1, 2, 1, 1]
      rw [← List.Vector.toList_reverse]
    conv_rhs =>
      rw [
        RadixVec.ofDigitsBE'_subtype_eq, RadixVec.toDigitsBE_ofDigitsBE,
        List.Vector.reverse_map, List.Vector.reverse_reverse,
      ]
      apply List.Vector.eq
      simp only [
        List.Vector.toList_map, List.map_map, List.map_id,
        BitVec.ofFin_toFin_comp
      ]


set_option maxHeartbeats 500000
theorem to_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bytes».call h![N] h![f])
    fun o =>
      ∃∃(lt : f.val < (256 ^ N.toNat)), o = (RadixVec.toDigitsBE
        (d := N.toNat)
        (r := ⟨256, by decide⟩)
        ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin |>.reverse) := by
  rcases N with ⟨⟨N, _⟩⟩
  enter_decl
  steps [to_le_radix_intro]
  · exact ()
  step_as (⟦⟧) (fun _ =>
    RadixVec.ofDigitsBE'
      (bytes.toList.reverse.map (fun i => (i.toFin : Digit ⟨256, by decide⟩))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbytes
    by_cases h: bytes.length = pbytes.length
    · cases' bytes with bytes bytesLen
      simp only [BitVec.toNat_ofFin] at bytesLen
      cases bytesLen
      loop_inv nat fun i _ _ =>
        (bytes.reverse.take i ≤ pbytes.reverse.take i) ⋆
          [ok ↦ ⟨_, decide <| bytes.reverse.take i < (pbytes.reverse.take i)⟩]
      · simp
      · simp only [h]
        simp [BitVec.ofNatLT_eq_ofNat]
      · simp
      · intro i _ _
        steps
        by_cases hlt: bytes.reverse.take i < pbytes.reverse.take i
        · simp only [hlt]
          apply STHoare.iteFalse_intro
          have : bytes.reverse.take (i + 1) < pbytes.reverse.take (i + 1) :=
            List.take_succ_lt_of_take_lt (by simp_all) (by simp_all) hlt
          steps
          · exact List.le_of_lt this
          · simp_all
        · simp only [hlt]
          apply STHoare.iteTrue_intro
          rename bytes.reverse.take i ≤ pbytes.reverse.take i => hle
          have heq : bytes.reverse.take i = pbytes.reverse.take i := by
            rw [List.le_iff_lt_or_eq] at hle
            tauto
          have hi_lt_bytes : i < bytes.reverse.length := by simp_all [List.length_reverse]
          have hi_lt_pbytes : i < pbytes.reverse.length := by simp_all [List.length_reverse]
          steps
          have hi_lt : i < bytes.length := by simp_all [List.length_reverse]
          have hlen_eq : bytes.length = pbytes.length := by simp_all
          have hlen32 : bytes.length < 2^32 := by simp_all
          have hi32 : i < 2^32 := Nat.lt_trans hi_lt hlen32
          have hidx := U32.index_toNat bytes.length i hlen32 hi32 hi_lt
          by_cases hi : bytes.reverse[i]'hi_lt_bytes = pbytes.reverse[i]'hi_lt_pbytes
          · convert STHoare.iteFalse_intro _
            · simp [
                List.Vector.get, List.getElem_reverse, List.length_reverse,
                h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · rw [
                List.take_succ_eq_append_getElem hi_lt_bytes,
                List.take_succ_eq_append_getElem hi_lt_pbytes, heq, hi
              ]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp only [
                List.Vector.get, List.getElem_reverse, List.length_reverse, h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · steps 14
              rename_i hassert_lt
              have hbyte_lt : bytes.reverse[i]'hi_lt_bytes < pbytes.reverse[i]'hi_lt_pbytes := by
                simp only [List.getElem_reverse, h, List.length_reverse, hlen_eq]
                simp only [List.Vector.get, List.get_eq_getElem] at hassert_lt
                convert hassert_lt using 2
                simp_all
              have : bytes.reverse.take (i + 1) < pbytes.reverse.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt hi_lt_bytes hi_lt_pbytes heq hbyte_lt
              steps
              · exact List.le_of_lt this
              · simp [this]
      steps
      rename decide _ = true => hlt_final
      have hlen : bytes.length = pbytes.length := by simp_all
      simp [hlen] at hlt_final
      have hlt_full : bytes.reverse < pbytes.reverse :=
        List.lt_of_take_lt (by simp [hlen]) (by simp) hlt_final
      have hpbytes_rev : pbytes.reverse =
          List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop)
            (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal) := by
        subst pbytes
        simp only [
          RadixVec.toDigitsBE', RadixVec.of, List.do_pure_eq_map, List.map_map,
          List.map_reverse, List.reverse_reverse
        ]
        congr 1
        funext x
        simp [BitVec.ofNatLT, BitVec.ofFin]
      have hlen_rev : bytes.reverse.length = pbytes.reverse.length := by
        simp [List.length_reverse, hlen]
      apply bytes_lt_of_lex_lt hlen_rev (hpbytes_rev ▸ hlt_full) hpbytes_rev
    ·
      loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [BitVec.toNat_ne, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bytes.length < pbytes.length := by
        apply lt_of_le_of_ne
        · simp_all
        · assumption
      have hpbytes_len :
          pbytes.length = (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal).length := by
        subst pbytes
        simp [RadixVec.toDigitsBE', RadixVec.of, List.do_pure_eq_map]
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      simp only [
        List.length_map, List.length_reverse, List.Vector.toList_length,
        hpbytes_len
      ] at hlen_lt ⊢
      exact hlen_lt
  steps
  rotate_left
  · rename_i v _
    subst_vars
    simp
    rw [ZMod.val_natCast]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    apply RadixVec.ofDigitsBE_lt
  · rename_i hbound vDigits hvDigits
    rename_i v hbytes hf
    rw [hbytes] at hbound
    have hbound' : RadixVec.ofDigitsBE v < p.natVal := by
      simp [List.Vector.toList_reverse, BitVec.toFin_ofFin_comp 8] at hbound
      rw [RadixVec.ofDigitsBE'_toList] at hbound
      exact hbound
    subst hvDigits hbytes hf
    have hval_eq :
        ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal) = (RadixVec.ofDigitsBE v).val := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound']
    have hlt256N : ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal) < 256^N := by
      rw [hval_eq]
      exact (RadixVec.ofDigitsBE v).isLt
    have hSubtype :
        (⟨ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal), hlt256N⟩ :
          RadixVec ⟨256, by decide⟩ N) = RadixVec.ofDigitsBE v := by
      ext
      simp only [hval_eq]
    simp only [hSubtype, RadixVec.toDigitsBE_ofDigitsBE, List.Vector.reverse_map]

lemma Nat.sub_sub_succ {n i : Nat} (hi : 1 ≤ i) :
    n - 1 - (i - 1) = n - i := by
  omega

set_option maxHeartbeats 2000000
theorem pow_32_intro {p self exponent} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::pow_32».call h![] h![self, exponent])
      (fun r => ∃∃ hlt : exponent.val < 2^32, r = self ^ exponent.val) := by
  enter_decl
  steps [to_le_bits_intro]
  simp [SLP.exists_pure] at *
  rename_i hlt hb
  set digits :=
    RadixVec.toDigitsBE (d := 32) (r := 2) ⟨exponent.val, hlt⟩ with hdigits
  have hb : b = (digits.map BitVec.ofFin).reverse := by simp [digits, hb]
  have hb_rev : b.reverse = digits.map BitVec.ofFin := by simp [(congrArg List.Vector.reverse hb)]
  have hb_digits_vec :
      List.Vector.map (fun i => (i.toFin : Digit 2)) b.reverse = digits := by
    simp [hb_rev, (List.Vector.map_toFin_map_ofFin (n := 1) (v := digits))]
  have hb_digits :
      b.toList.reverse.map (fun i => (i.toFin : Digit 2)) = digits.toList := by
    simpa [List.Vector.toList_map, List.Vector.toList_reverse] using
      congrArg List.Vector.toList hb_digits_vec
  loop_inv nat fun i _ _ =>
    [r ↦ ⟨.field, self ^ (RadixVec.ofDigitsBE' (digits.toList.take (i - 1)))⟩]
  · simp
  · intro i hi_lo hhi
    simp [] at hhi
    steps
    · congr 1
      have hi_lt32 : i - 1 < 32 := by
        cases i with
        | zero =>
            simp
        | succ i =>
            have : i < 32 := by
              have : i.succ < 33 := by simpa using hhi
              exact Nat.lt_of_succ_lt_succ this
            simpa
      have hi_lt : i - 1 < digits.toList.length := by
        simpa [digits, List.Vector.toList_length] using hi_lt32
      have hi_lt_b : i - 1 < b.toList.length := by
        simpa [List.Vector.toList_length] using hi_lt32
      have hi_lt_rev : i - 1 < b.toList.reverse.length := by
        simpa [List.length_reverse] using hi_lt_b
      have hidx :
          (b.toList.reverse[i - 1]'hi_lt_rev).toFin =
            digits.toList[i - 1]'hi_lt := by
        have hmap :
            (b.toList.reverse[i - 1]'hi_lt_rev).toFin =
              (b.toList.reverse.map (fun i => (i.toFin : Digit 2)))[i - 1]'(by
                simp []
                omega
              ) := by
          simp [
            (List.getElem_map_rev (f := fun i => (i.toFin : Digit 2))
              (l := b.toList.reverse) (n := i - 1) (h := hi_lt_rev))
          ]
        simpa [hb_digits] using hmap
      set a := RadixVec.ofDigitsBE' (digits.toList.take (i - 1)) with ha
      have hi_lo : 1 ≤ i := by simpa [hi_lo]
      have hi_le : i ≤ 32 := by
        have : i < 33 := by simp [hhi]
        exact Nat.lt_succ_iff.mp this
      have hindex_lt : 32 - i < b.toList.length := by
        have hle : 32 - i ≤ 31 := by
          simp [Nat.sub_le_sub_left hi_lo 32]
        have hlt : 31 < 32 := by decide
        have : 32 - i < 32 := lt_of_le_of_lt hle hlt
        simp [List.Vector.toList_length, this]
      have hsub : b.toList.length - 1 - (i - 1) = 32 - i := by
        simp [List.Vector.toList_length, Nat.sub_sub_succ (n := 32) hi_lo]
      have hmod : (4294967296 - i + 32) % 4294967296 = 32 - i := by
        have hle : i ≤ 4294967296 := by
          exact le_trans hi_le (by decide)
        have h32_lt : 32 < 4294967296 := by decide
        have hcalc : 4294967296 - i + 32 = 4294967296 + (32 - i) := by
          calc
            4294967296 - i + 32 = 4294967296 + 32 - i := by
              symm
              exact Nat.sub_add_comm hle
            _ = 4294967296 + (32 - i) := by
              exact (Nat.add_sub_assoc hi_le 4294967296)
        calc
          (4294967296 - i + 32) % 4294967296
              = (4294967296 + (32 - i)) % 4294967296 := by
                  simp [hcalc]
          _ = ((4294967296 % 4294967296) + (32 - i) % 4294967296) % 4294967296 := by
                  simp [Nat.add_mod]
          _ = (32 - i) % 4294967296 := by simp
          _ = 32 - i := by
                  apply Nat.mod_eq_of_lt
                  have : 32 - i ≤ 32 := Nat.sub_le _ _
                  exact lt_of_le_of_lt this h32_lt
      have hindex_lt32 : 32 - i < 32 := by
        simp []
        omega
      have hindex_fin :
          (⟨(4294967296 - i + 32) % 4294967296, by
              simp [hmod, hindex_lt32]⟩ : Fin 32) =
            ⟨32 - i, hindex_lt32⟩ := by
        apply Fin.ext
        simp [hmod]
      have htake :
          digits.toList.take i =
            digits.toList.take (i - 1) ++ [digits.toList[i - 1]'hi_lt] := by
        have hi_eq : i = i - 1 + 1 := by
          exact (Nat.sub_add_cancel hi_lo).symm
        have htake' :
            digits.toList.take (i - 1 + 1) =
              digits.toList.take (i - 1) ++ [digits.toList[i - 1]'hi_lt] := by
          exact List.take_succ_eq_append_getElem hi_lt
        conv_lhs => rw [hi_eq]
        exact htake'
      have hdigits_take :
          RadixVec.ofDigitsBE' (digits.toList.take i) =
            RadixVec.ofDigitsBE' (digits.toList.take (i - 1)) * 2 +
              digits.toList[i - 1]'hi_lt := by
        rw [htake, RadixVec.ofDigitsBE'_append, RadixVec.ofDigitsBE'_cons]
        have hradix : (↑(2 : Radix) : Nat) = 2 := rfl
        simp [
          List.length, RadixVec.ofDigitsBE'_cons, RadixVec.ofDigitsBE'_nil,
          Nat.pow_one, Nat.pow_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one, Nat.mul_zero,
          hradix
        ]
      have hpow2 :
          self ^ (a * 2) = self ^ a * self ^ a := by
        simpa [ha, pow_two] using (pow_mul self a 2)
      by_cases hbit : b.toList.reverse[i - 1]'(by
          simpa [List.length_reverse] using hi_lt_b) = 0
      · have hbit_rev : b.toList.reverse[i - 1]'hi_lt_rev = 0 := by
          simpa using hbit
        have hbit_index : b.toList[32 - i]'hindex_lt = 0 := by
          simpa [
            List.getElem_reverse, List.length_reverse, List.Vector.toList_length,
            Nat.sub_sub_succ (n := 32) hi_lo
          ] using hbit_rev
        have hbit_nat :
            (↑(BitVec.toNat (List.Vector.get b ⟨32 - i, hindex_lt32⟩)) : Fp p) = 0 := by
          simpa [List.Vector.get, List.get_eq_getElem] using
            (congrArg (fun x => (↑x.toNat : Fp p)) hbit_index)
        have hbit_digit : digits.toList[i - 1]'hi_lt = 0 := by
          have hbit_fin :
              (b.toList.reverse[i - 1]'hi_lt_rev).toFin = 0 := by
            exact congrArg (fun x => (x.toFin : Digit 2)) hbit_rev
          exact hidx.symm.trans hbit_fin
        have hdigits_zero :
            RadixVec.ofDigitsBE' (digits.toList.take i) =
              RadixVec.ofDigitsBE' (digits.toList.take (i - 1)) * 2 := by
          simp [hdigits_take, hbit_digit]
        calc
          ↑(BitVec.toNat (List.Vector.get b ⟨(4294967296 - i + 32) % 4294967296, by
              simpa [hmod, List.Vector.toList_length] using hindex_lt⟩)) *
                (self ^ a * self ^ a * self) +
              (1 - ↑(BitVec.toNat (List.Vector.get b ⟨(4294967296 - i + 32) % 4294967296, by
                  simpa [hmod, List.Vector.toList_length] using hindex_lt⟩))) *
                (self ^ a * self ^ a)
              = self ^ a * self ^ a := by
                simp [hindex_fin, hbit_nat]
          _ = self ^ (a * 2) := by
                symm
                exact hpow2
          _ = self ^ RadixVec.ofDigitsBE' (digits.toList.take i) := by
                simp [ha, hdigits_zero]
      · have hbit' : b.toList.reverse[i - 1]'(by
            simpa [List.length_reverse] using hi_lt_b) = 1 := by
          have := U.cases_one (b.toList.reverse[i - 1]'(by
            simpa [List.length_reverse] using hi_lt_b))
          tauto
        have hbit_rev : b.toList.reverse[i - 1]'hi_lt_rev = 1 := by simp [hbit']
        have hbit_index : b.toList[32 - i]'hindex_lt = 1 := by
          simpa [
            List.getElem_reverse, List.length_reverse, List.Vector.toList_length,
            Nat.sub_sub_succ (n := 32) hi_lo
          ] using hbit_rev
        have hbit_nat :
            (↑(BitVec.toNat (List.Vector.get b ⟨32 - i, hindex_lt32⟩)) : Fp p) = 1 := by
          simpa [List.Vector.get, List.get_eq_getElem] using
            (congrArg (fun x => (↑x.toNat : Fp p)) hbit_index)
        have hbit_digit : digits.toList[i - 1]'hi_lt = 1 := by
          have hbit_fin :
              (b.toList.reverse[i - 1]'hi_lt_rev).toFin = 1 := by
            exact congrArg (fun x => (x.toFin : Digit 2)) hbit_rev
          exact hidx.symm.trans hbit_fin
        have hdigits_one :
            RadixVec.ofDigitsBE' (digits.toList.take i) =
              RadixVec.ofDigitsBE' (digits.toList.take (i - 1)) * 2 + 1 := by
          have hmod1 : (1 % (2 : Nat)) = 1 := by
            exact Nat.mod_eq_of_lt (by decide)
          have hradix : (↑(2 : Radix) : Nat) = 2 := rfl
          simp [hdigits_take, hbit_digit, hmod1, hradix]
        calc
          ↑(BitVec.toNat (List.Vector.get b ⟨(4294967296 - i + 32) % 4294967296, by
              simpa [hmod, List.Vector.toList_length] using hindex_lt⟩)) *
                (self ^ a * self ^ a * self) +
              (1 - ↑(BitVec.toNat (List.Vector.get b ⟨(4294967296 - i + 32) % 4294967296, by
                  simpa [hmod, List.Vector.toList_length] using hindex_lt⟩))) *
                (self ^ a * self ^ a)
              = self ^ a * self ^ a * self := by
                simp [hindex_fin, hbit_nat]
          _ = self ^ (a * 2) * self := by
                simp [hpow2]
          _ = self ^ (a * 2 + 1) := by
                simp [pow_add, pow_one]
          _ = self ^ RadixVec.ofDigitsBE' (digits.toList.take i) := by
                simp [ha, hdigits_one]
  ·
    have htake32 : List.take 32 digits.toList = digits.toList := by
      simp [List.Vector.toList_length, List.take_length (l := digits.toList)]
    have hdigits_val : RadixVec.ofDigitsBE' digits.toList = exponent.val := by
      have hdigits_eq : RadixVec.ofDigitsBE digits = ⟨exponent.val, hlt⟩ := by
        simpa [hdigits] using (RadixVec.ofDigitsBE_toDigitsBE (n := ⟨exponent.val, hlt⟩))
      have := RadixVec.ofDigitsBE'_toList (l := digits)
      simp [hdigits_eq, this]
    have hpow_val :
        self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList) = self ^ exponent.val := by
      simp [htake32, hdigits_val]
    have hlt32 : ZMod.val exponent < 4294967296 := by simpa [hlt]
    refine STHoare.consequence
      (H₁ :=
        [r ↦ ⟨Tp.field, self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList)⟩])
      (Q₁ := fun v =>
        ⟦v = self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList)⟧ ⋆
          [r ↦ ⟨Tp.field, self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList)⟩])
      ?_ ?_ ?_
    · exact SLP.entails_self
    · intro v
      simp [SLP.star_assoc]
      apply SLP.pure_left
      intro hv
      apply SLP.pure_right
      · refine And.intro hlt32 ?_
        calc
          v = self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList) := hv
          _ = self ^ exponent.val := hpow_val
      · exact SLP.entails_top
    · simpa using (STHoare.readRef_intro (p := p) (Γ := env) (r := r)
        (tp := Tp.field)
        (v := self ^ RadixVec.ofDigitsBE' (List.take 32 digits.toList)))

theorem lt_intro {p self another} [Prime.BitsGT p 129]
    (hmod : p.natVal = Lampe.Stdlib.Field.Bn254.ploNat +
      Lampe.Stdlib.Field.Bn254.pow128 * Lampe.Stdlib.Field.Bn254.phiNat) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.12::field::lt».call h![] h![self, another])
      (fun r => r = decide (self.val < another.val)) := by
  enter_decl
  steps [Lampe.Stdlib.Compat.is_bn254_spec]
  apply STHoare.iteTrue_intro
  steps [Lampe.Stdlib.Field.Bn254.lt_intro (p := p) (hmod := hmod)]
  rename_i hlt
  simp [hlt]

theorem from_le_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::from_le_bytes».call h![N] h![bytes])
    fun output => output = Fp.ofBytesLE (P := p) bytes.toList := by
  rcases N with ⟨⟨N, hN⟩⟩
  enter_decl
  steps
  loop_inv nat fun i _ _ =>
    [v ↦ ⟨.field, (256 ^ i : Fp p)⟩] ⋆
      [result ↦ ⟨.field, Fp.ofBytesLE (P := p) (bytes.toList.take i)⟩]
  · simp
  · intro i _ hhi
    steps
    · congr 1
      conv at hhi => rhs; whnf
      simp only [
        Lens.modify, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, Builtin.instCastTpUField,
        Builtin.instCastTpU, BitVec.natCast_eq_ofNat, List.take_succ, getElem?, decidableGetElem?,
        List.Vector.toList_length
      ]
      simp only [hhi, Fp.ofBytesLE, List.map_append, ofBaseLE_append]
      have hi_le : i ≤ N := by linarith
      have hi_mod : i % 4294967296 = i := by
        apply Nat.mod_eq_of_lt
        linarith [hi_le, hN]
      simp [*, List.Vector.get, ofBaseLE]
      rw [mul_comm]
      rfl
  steps
  simp_all
  rw [List.take_of_length_le]
  · simp

theorem from_be_bytes_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::from_be_bytes».call h![N] h![bytes])
    fun output => output = Fp.ofBytesLE (P := p) bytes.toList.reverse := by
  rcases N with ⟨⟨N, hN⟩⟩
  enter_decl
  steps
  loop_inv nat fun i _ _ =>
    [v ↦ ⟨.field, (256 ^ i : Fp p)⟩] ⋆
      [result ↦ ⟨.field, Fp.ofBytesLE (P := p) (bytes.toList.reverse.take i)⟩]
  · simp
  · intro i _ hhi
    steps
    · congr 1
      conv at hhi => rhs; whnf
      simp only [
        Lens.modify, BitVec.ofNat_eq_ofNat, Builtin.instCastTpUField, Builtin.instCastTpU,
        BitVec.natCast_eq_ofNat, List.take_succ, getElem?, decidableGetElem?,
        List.Vector.toList_length, List.length_reverse
      ]
      simp only [hhi, Fp.ofBytesLE, List.map_append, ofBaseLE_append]
      have hi_le : i ≤ N := by linarith
      have hi_mod : i % 4294967296 = i := by
        apply Nat.mod_eq_of_lt
        linarith [hi_le, hN]
      have hlen32 : N < 2^32 := by simp [hN]
      have hi32 : i < 2^32 := Nat.lt_trans hhi hlen32
      have hidx := U32.index_toNat N i hlen32 hi32 hhi
      simp_all [List.Vector.get, ofBaseLE, List.getElem_reverse]
      rw [mul_comm]
      rfl
  steps
  simp_all
  rw [List.take_of_length_le]
  · simp [List.length_reverse]

theorem sgn0_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::sgn0».call h![] h![f])
    (fun r => r = @Builtin.CastTp.cast Tp.field (Tp.u 1) _ p f) := by
  enter_decl
  simpa using
    (Lampe.STHoare.cast_intro (p := p) (Γ := env) (tp := Tp.field) (tp' := Tp.u 1) (v := f))
