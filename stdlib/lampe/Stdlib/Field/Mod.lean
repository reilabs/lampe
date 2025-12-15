import «std-1.0.0-beta.12».Extracted
import Lampe
import Lampe.Builtin.Helpers

namespace Lampe.Stdlib.Field

open «std-1.0.0-beta.12» (env)

theorem List.lt_append_of_lt [DecidableEq α] [LT α] [DecidableLT α]
  (l₁ l₂ l₃ l₄: List α):
    l₁.length = l₂.length → l₁ < l₂ → l₁ ++ l₃ < l₂ ++ l₄ := by
  intro hl hlt
  rw [List.lt_iff_exists] at hlt
  simp only [hl, List.take_length, lt_self_iff_false, and_false, exists_idem, false_or] at hlt
  rcases hlt with ⟨i, h, _⟩
  rw [List.lt_iff_exists]
  right
  exists
    i,
    (by simp only [List.length_append]; linarith),
    (by simp only [List.length_append]; linarith)
  apply And.intro
  · intro j hj
    have : j < l₁.length := by linarith
    have : j < l₂.length := by linarith
    simp_all
  · simp_all

theorem List.take_succ_lt_of_take_lt [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α}
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) (hlt : l₁.take i < l₂.take i) :
    l₁.take (i + 1) < l₂.take (i + 1) := by
  rw [List.take_succ_eq_append_getElem hi₁, List.take_succ_eq_append_getElem hi₂]
  apply List.lt_append_of_lt
  · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi₁), Nat.min_eq_left (Nat.le_of_lt hi₂)]
  · exact hlt

theorem List.take_succ_lt_of_getElem_lt [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α}
  (hi₁ : i < l₁.length) (hi₂ : i < l₂.length)
  (heq : l₁.take i = l₂.take i) (hlt : l₁[i] < l₂[i]) :
    l₁.take (i + 1) < l₂.take (i + 1) := by
  rw [
    List.take_succ_eq_append_getElem hi₁,
    List.take_succ_eq_append_getElem hi₂,
    heq
  ]
  exact List.append_left_lt (List.cons_lt_cons_iff.mpr (Or.inl hlt))

theorem List.lt_of_take_lt [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α} {n : ℕ}
  (hlen₁ : l₁.length = n) (hlen₂ : l₂.length = n)
  (hlt : l₁.take n < l₂.take n) : l₁ < l₂ := by
  rw [←List.take_length (l := l₁), ←List.take_length (l := l₂), hlen₁, hlen₂]
  exact hlt

instance : Std.Total (fun (x1: U s) x2 => ¬x1 < x2) := { total := by simp [BitVec.le_total] }
instance : Std.Antisymm (fun (x1: U s) x2 => ¬x1 < x2) where
  antisymm _ _ _ _ := by
    simp_all only [BitVec.not_lt]
    apply BitVec.le_antisymm <;> assumption
instance : Std.Irrefl (fun (x1: U s) x2 => x1 < x2) where
  irrefl _ := BitVec.lt_irrefl _

lemma U.cases_one (i : U 1) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

theorem BitVec.toFin_ofFin_comp (n : ℕ) : (fun (i : BitVec n) => i.toFin) ∘ BitVec.ofFin = id := by
  funext x
  simp [BitVec.toFin_ofFin]

theorem BitVec.ofFin_toFin_comp (n : ℕ) : BitVec.ofFin ∘ (fun (i : BitVec n) => i.toFin) = id := by
  funext x
  rfl

theorem List.Vector.map_toFin_map_ofFin {n d : ℕ} (v : List.Vector (Fin (2^n)) d) :
    List.Vector.map (fun (i : BitVec n) => i.toFin) (List.Vector.map BitVec.ofFin v) = v := by
  apply List.Vector.eq
  simp only [List.Vector.toList_map, List.map_map, BitVec.toFin_ofFin_comp, List.map_id]

theorem List.Vector.map_ofFin_map_toFin {n d : ℕ} (v : List.Vector (BitVec n) d) :
    List.Vector.map BitVec.ofFin (List.Vector.map (fun (i : BitVec n) => i.toFin) v) = v := by
  apply List.Vector.eq
  simp only [List.Vector.toList_map, List.map_map, BitVec.ofFin_toFin_comp, List.map_id]

theorem List.Vector.reverse_map {α β : Type} {d : ℕ} (v : List.Vector α d) (f : α → β) :
    (v.map f).reverse = v.reverse.map f := by
  apply List.Vector.eq
  simp only [List.Vector.toList_reverse, List.Vector.toList_map, List.map_reverse]

theorem List.do_pure_eq_map {α β : Type} (l : List α) (f : α → β) :
    (do let a ← l; pure (f a)) = List.map f l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show List.flatMap _ (x :: xs) = _
    simp only [List.flatMap_cons, Pure.pure, List.singleton_append, List.map_cons]
    congr 1

theorem RadixVec.toDigitsBE'_bytes_eq_map_toFin_map_ofNatLT (hr : 1 < 256) (m : ℕ) :
    RadixVec.toDigitsBE' ⟨256, hr⟩ m =
      List.map (fun (i : BitVec 8) => i.toFin)
        (List.map (fun (d : Digit ⟨256, hr⟩) => BitVec.ofNatLT d.val d.prop)
          (RadixVec.toDigitsBE' ⟨256, hr⟩ m)) := by
  simp only [List.map_map]
  rw [eq_comm]
  convert List.map_id _

@[simp]
theorem List.Vector.toList_reverse {α : Type} {n : ℕ} (v : List.Vector α n) :
    v.reverse.toList = v.toList.reverse := rfl

lemma U32.index_toNat (len i : ℕ) (hlen : len < 2^32) (hi : i < 2^32) (hi_lt : i < len) :
    (({ toFin := ⟨len, hlen⟩ } : U 32) - 1 - (BitVec.ofNatLT i hi)).toNat = len - 1 - i := by
  have h1 : ({ toFin := ⟨len, hlen⟩ } : U 32).toNat = len := by simp
  have h2 : (BitVec.ofNatLT i hi : U 32).toNat = i := by simp
  have h3 : (1 : U 32).toNat = 1 := by decide
  simp only [BitVec.toNat_sub, h1, h2, h3, Nat.reducePow]
  omega

/-- Key lemma for bound proofs (bits version): if `data < pdata` lexicographically and
    `pdata = toDigitsBE' 2 p` mapped to BitVec, then `ofDigitsBE' (data.map toFin) < p`.
    Works for both BE (with data) and LE (with data.reverse). -/
theorem bits_lt_of_lex_lt {data pdata : List (BitVec 1)}
    (hlen : data.length = pdata.length)
    (hlt : data < pdata)
    (hpdata : pdata = List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' 2 p)) :
    RadixVec.ofDigitsBE' (data.map (fun i => (i.toFin : Digit 2))) < p := by
  rw [←RadixVec.ofDigitsBE'_toDigitsBE' (r := 2) (n := p)]
  apply RadixVec.ofDigitsBE'_mono
  · simp [RadixVec.toDigitsBE', hlen, hpdata, List.length_map]
  · have hself : RadixVec.toDigitsBE' 2 p =
        List.map (fun (i : BitVec 1) => (i.toFin : Digit 2))
          (List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' 2 p)) := by
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

theorem bytes_lt_of_lex_lt {data pdata : List (BitVec 8)}
    (hlen : data.length = pdata.length)
    (hlt : data < pdata)
    (hpdata : pdata = List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' ⟨256, by decide⟩ p)) :
    RadixVec.ofDigitsBE' (data.map (fun i => (i.toFin : Digit ⟨256, by decide⟩))) < p := by
  rw [←RadixVec.ofDigitsBE'_toDigitsBE' (r := ⟨256, by decide⟩) (n := p)]
  apply RadixVec.ofDigitsBE'_mono
  · simp [RadixVec.toDigitsBE', hlen, hpdata, List.length_map]
  · rw [RadixVec.toDigitsBE'_bytes_eq_map_toFin_map_ofNatLT (by decide) p]
    apply List.map_lt
    · intro x y h
      rw [BitVec.lt_def] at h
      rw [Fin.lt_def]
      exact h
    · rw [hpdata] at hlt
      exact hlt

theorem ofDigitsBE'_lt_of_shorter_than_modulus {r : Radix} {data : List (Digit r)} {P : Prime}
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
    fun r => ∃∃(lt : f.val < (2 ^ N.toNat)), r = (RadixVec.toDigitsBE (d := N.toNat) (r := 2) ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin) := by
  rcases N with ⟨⟨N,_⟩⟩
  enter_decl
  steps
  · exact ()
  step_as (⟦⟧) (fun _ => RadixVec.ofDigitsBE' (bits.toList.map (fun i => (i.toFin : Digit 2))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbits
    by_cases h: bits.length = pbits.length
    · cases' bits with bits bitsLen
      simp only [BitVec.toNat_ofFin] at bitsLen
      cases bitsLen
      loop_inv nat fun i _ _ => (bits.take i ≤ pbits.take i) ⋆ [ok ↦ ⟨_, decide $ bits.take i < (pbits.take i)⟩]
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
    simp only [List.Vector.toList_map, List.map_map]
    rw [eq_comm]
    exact List.map_id _
  · subst_vars
    simp only [
      BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      RadixVec.ofDigitsBE,
      Nat.reducePow, Nat.reduceMod
    ]
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
    simp only [
      List.Vector.toList_map, List.Vector.toList_reverse,
      List.map_map, List.map_reverse, List.reverse_reverse
    ]
    rw [eq_comm]
    convert List.map_id _
  · subst_vars
    simp only [BitVec.ofNat_eq_ofNat]
    congr 2
    apply List.Vector.eq
    rw [eq_comm]
    simp [Function.comp]

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
  step_as (⟦⟧) (fun _ => RadixVec.ofDigitsBE' (bytes.toList.map (fun i => (i.toFin : Digit ⟨256, by decide⟩))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbytes  -- pbytes is the modulus bytes slice
    by_cases h: bytes.length = pbytes.length
    · cases' bytes with bytes bytesLen
      simp only [BitVec.toNat_ofFin] at bytesLen
      cases bytesLen
      loop_inv nat fun i _ _ => (bytes.take i ≤ pbytes.take i) ⋆ [ok ↦ ⟨_, decide $ bytes.take i < (pbytes.take i)⟩]
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
      simp only [BitVec.toNat_ofFin, List.take_length, beq_true, decide_eq_true_eq] at hlt
      simp only [hlen, List.take_length] at hlt
      have hpbytes_eq : pbytes = List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal) := by
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
      have hpbytes_len : pbytes.length = (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal).length := by
        subst pbytes
        simp [RadixVec.toDigitsBE']
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      simp only [List.length_map, List.Vector.toList_length, hpbytes_len] at hlen_lt ⊢
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
    simp only [Fin.eta, RadixVec.toDigitsBE_ofDigitsBE]

set_option maxHeartbeats 300000
theorem to_le_bits_intro :
    STHoare p env ⟦⟧
    («std-1.0.0-beta.12::field::to_le_bits».call h![N] h![f])
    fun r => ∃∃(lt : f.val < (2 ^ N.toNat)), r = (RadixVec.toDigitsBE (d := N.toNat) (r := 2) ⟨f.val, by simp_all [OfNat.ofNat]⟩ |>.map BitVec.ofFin |>.reverse) := by
  rcases N with ⟨⟨N,_⟩⟩
  enter_decl
  steps
  · exact ()
  step_as (⟦⟧) (fun _ => RadixVec.ofDigitsBE' (bits.toList.reverse.map (fun i => (i.toFin : Digit 2))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbits
    by_cases h: bits.length = pbits.length
    · cases' bits with bits bitsLen
      simp only [BitVec.toNat_ofFin] at bitsLen
      cases bitsLen
      loop_inv nat fun i _ _ => (bits.reverse.take i ≤ pbits.reverse.take i) ⋆ [ok ↦ ⟨_, decide $ bits.reverse.take i < (pbits.reverse.take i)⟩]
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
            · simp only [
                List.Vector.get, List.getElem_reverse, List.length_reverse,
                h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · rw [List.take_succ_eq_append_getElem hi_lt_bits, List.take_succ_eq_append_getElem hi_lt_pbits, heq, hi]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp only [
                List.Vector.get, List.getElem_reverse, List.length_reverse,
                h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · steps 9
              rename_i hassert
              have hpbit : pbits[pbits.length - 1 - i] = 1 := by
                simp only [
                  beq_true, decide_eq_true_eq,
                  List.get_eq_getElem
                ] at hassert
                convert hassert using 2
                rw [←hlen_eq]
                exact hidx.symm
              have hbit : bits[bits.length - 1 - i] = 0 := by
                have := U.cases_one bits[bits.length - 1 - i]
                simp only [List.getElem_reverse, h, List.length_reverse, hlen_eq] at hi
                simp_all
              have hbit_lt : bits.reverse[i]'hi_lt_bits < pbits.reverse[i]'hi_lt_pbits := by
                simp only [List.getElem_reverse, h, List.length_reverse, hlen_eq] at hbit ⊢
                simp [hpbit, hbit]
              have : bits.reverse.take (i + 1) < pbits.reverse.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt hi_lt_bits hi_lt_pbits heq hbit_lt
              steps
              · exact List.le_of_lt this
              · simp [this]
      steps
      rename decide _ = true => hlt_final
      have hlen : bits.length = pbits.length := by simp_all
      simp only [BitVec.toNat_ofFin, List.take_length, beq_true, decide_eq_true_eq, List.length_reverse] at hlt_final
      simp only [hlen, List.take_length, List.length_reverse] at hlt_final
      have hlt_full : bits.reverse < pbits.reverse :=
        List.lt_of_take_lt (by simp [hlen]) (by simp) hlt_final
      have hpbits_rev : pbits.reverse = List.map (fun (d : Digit 2) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' 2 p.natVal) := by
        subst pbits
        simp only [
          RadixVec.toDigitsBE', RadixVec.of,
          List.do_pure_eq_map, List.map_map,
          List.map_reverse, List.reverse_reverse
        ]
        congr 1
        funext x
        simp [BitVec.ofNatLT, BitVec.ofFin]
      have hlen_rev : bits.reverse.length = pbits.reverse.length := by simp [List.length_reverse, hlen]
      apply bits_lt_of_lex_lt hlen_rev (hpbits_rev ▸ hlt_full) hpbits_rev
    ·
      loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [BitVec.toNat_ne, *, List.Vector.length, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bits.length < pbits.length := by
        apply lt_of_le_of_ne
        · simp only [BitVec.natCast_eq_ofNat, List.Vector.length, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
          simp_all
        · assumption
      apply ofDigitsBE'_lt_of_shorter_than_modulus (P := p)
      subst pbits
      simp only [
        RadixVec.toDigitsBE', List.do_pure_eq_map, List.length_map,
        List.length_reverse, List.Vector.toList_length
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
  ·
    rename_i h v _
    subst_vars
    simp only [
      ←List.Vector.toList_map, List.length_reverse,
      List.map_reverse, List.Vector.toList_reverse,
      RadixVec.ofDigitsBE'_toList,
    ] at h
    conv_rhs =>
      enter [1, 2, 1, 1]
      rw [ZMod.val_natCast]
      simp only [←RadixVec.ofDigitsBE'_toList, ←List.Vector.toList_map, List.Vector.toList_reverse]
      rw [Nat.mod_eq_of_lt h]
    conv_rhs =>
      enter [1, 2, 1, 1]
      rw [← List.Vector.toList_reverse]
    conv_rhs => rw [
      RadixVec.ofDigitsBE'_subtype_eq, RadixVec.toDigitsBE_ofDigitsBE,
      List.Vector.reverse_map, List.Vector.reverse_reverse, List.Vector.map_ofFin_map_toFin
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
  step_as (⟦⟧) (fun _ => RadixVec.ofDigitsBE' (bytes.toList.reverse.map (fun i => (i.toFin : Digit ⟨256, by decide⟩))) < p.natVal)
  · apply STHoare.iteTrue_intro
    steps
    rename' p => pbytes
    by_cases h: bytes.length = pbytes.length
    · cases' bytes with bytes bytesLen
      simp only [BitVec.toNat_ofFin] at bytesLen
      cases bytesLen
      loop_inv nat fun i _ _ => (bytes.reverse.take i ≤ pbytes.reverse.take i) ⋆ [ok ↦ ⟨_, decide $ bytes.reverse.take i < (pbytes.reverse.take i)⟩]
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
            · simp only [
                List.Vector.get, List.getElem_reverse, List.length_reverse,
                h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · rw [List.take_succ_eq_append_getElem hi_lt_bytes, List.take_succ_eq_append_getElem hi_lt_pbytes, heq, hi]
              steps
              · apply List.le_refl
              · congr
                simp [List.le_refl]
          · convert STHoare.iteTrue_intro _
            · simp only [
                List.Vector.get, List.getElem_reverse, List.length_reverse,
                h, hlen_eq
              ] at hi ⊢
              simp_all [List.get_eq_getElem]
            · steps 14
              rename_i hassert_lt
              have hbyte_lt : bytes.reverse[i]'hi_lt_bytes < pbytes.reverse[i]'hi_lt_pbytes := by
                simp only [List.getElem_reverse, h, List.length_reverse, hlen_eq]
                simp only [beq_true, decide_eq_true_eq, List.Vector.get, List.get_eq_getElem] at hassert_lt
                convert hassert_lt using 2 <;> simp_all
              have : bytes.reverse.take (i + 1) < pbytes.reverse.take (i + 1) :=
                List.take_succ_lt_of_getElem_lt hi_lt_bytes hi_lt_pbytes heq hbyte_lt
              steps
              · exact List.le_of_lt this
              · simp [this]
      steps
      rename decide _ = true => hlt_final
      have hlen : bytes.length = pbytes.length := by simp_all
      simp only [BitVec.toNat_ofFin, List.take_length, beq_true, decide_eq_true_eq, List.length_reverse] at hlt_final
      simp only [hlen, List.take_length, List.length_reverse] at hlt_final
      have hlt_full : bytes.reverse < pbytes.reverse :=
        List.lt_of_take_lt (by simp [hlen]) (by simp) hlt_final
      have hpbytes_rev : pbytes.reverse = List.map (fun (d : Digit ⟨256, by decide⟩) => BitVec.ofNatLT d.val d.prop) (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal) := by
        subst pbytes
        simp only [
          RadixVec.toDigitsBE', RadixVec.of, List.do_pure_eq_map, List.map_map,
          List.map_reverse, List.reverse_reverse
        ]
        congr 1
        funext x
        simp [BitVec.ofNatLT, BitVec.ofFin]
      have hlen_rev : bytes.reverse.length = pbytes.reverse.length := by simp [List.length_reverse, hlen]
      apply bytes_lt_of_lex_lt hlen_rev (hpbytes_rev ▸ hlt_full) hpbytes_rev
    ·
      loop_inv nat fun _ _ _ => [ok ↦ ⟨_, true⟩]
      · congr
        simp only [BitVec.toNat_ne, *, List.Vector.length, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat]
        simp_all
      · simp
      · intro _ _ _
        steps
        apply STHoare.iteFalse_intro
        steps
      steps
      have hlen_lt : bytes.length < pbytes.length := by
        apply lt_of_le_of_ne
        · simp only [BitVec.natCast_eq_ofNat, List.Vector.length, BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
          simp_all
        · assumption
      have hpbytes_len : pbytes.length = (RadixVec.toDigitsBE' ⟨256, by decide⟩ p.natVal).length := by
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
      simp only [
        List.Vector.toList_map, List.Vector.toList_reverse,
        List.map_reverse, List.reverse_reverse, List.map_map, List.map_id,
        BitVec.toFin_ofFin_comp 8,
      ] at hbound
      rw [RadixVec.ofDigitsBE'_toList] at hbound
      exact hbound
    subst hvDigits hbytes hf
    have hval_eq : ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal) = (RadixVec.ofDigitsBE v).val := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound']
    have hlt256N : ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal) < 256^N := by
      rw [hval_eq]
      exact (RadixVec.ofDigitsBE v).isLt
    have hSubtype : (⟨ZMod.val (↑↑(RadixVec.ofDigitsBE v) : ZMod p.natVal), hlt256N⟩ : RadixVec ⟨256, by decide⟩ N) = RadixVec.ofDigitsBE v := by
      ext
      simp only [hval_eq]
    simp only [hSubtype, RadixVec.toDigitsBE_ofDigitsBE, List.Vector.reverse_map]
