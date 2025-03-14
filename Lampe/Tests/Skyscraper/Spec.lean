import Tests.Skyscraper.Ref
import Tests.Skyscraper.Extracted

import Mathlib.Tactic.FieldSimp

open Lampe Extracted

-- set_option trace.Lampe.SL true

def lp : Lampe.Prime := ⟨p, pPrime⟩

def RC : List Int :=
    [-4058822530962036113558957735524994411356374024839875405476791844324326516925,
    5852100059362614845584985098022261541909346143980691326489891671321030921585,
    -4840154698573742532565501789862255731956493498174317200418381990571919688651,
    71577923540621522166602308362662170286605786204339342029375621502658138039,
    1630526119629192105940988602003704216811347521589219909349181656165466494167,
    7807402158218786806372091124904574238561123446618083586948014838053032654983,
    -8558681900379240296346816806663462402801546068866479372657894196934284905006,
    -4916733727805245440019875123169648108733681133486378553671899463457684353318]

def SIGMA : Int :=
    9915499612839321149637521777990102151350674507940716049588462388200839649614

theorem rl_intro : STHoare lp env ⟦⟧
  (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "rl" [] HList.nil) h![input])
    fun output => output = Skyscraper.rl input := by
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.rl.fn
  all_goals try tauto
  simp only [rl]
  steps
  simp_all
  tauto

theorem u8_ge_zero (u : U 8) : 0 ≤ u := by bv_decide

theorem rotateLeft_spec : STHoare lp env ⟦N < 254⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Skyscraper.rotateLeft input N := by
  simp only [Extracted.rotate_left]

  steps
  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Skyscraper.rl i.toNat input⟩]
  change 0 ≤ N
  exact u8_ge_zero N
  · intros i hlo hhi
    steps [rl_intro]
    simp_all
    congr
    have : (i.toNat + 1) % 256 = i.toNat + 1 := by
      have : i.toNat < N.toNat := hhi
      have : N.toNat < 254 := by rename_i a _ _ ; exact a
      omega
    rw [this]
    simp [Nat.repeat]
  · steps
    simp_all [Skyscraper.rotateLeft]

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  enter_decl
  apply STHoare.consequence (h_hoare := rotateLeft_spec)
  simp_all [SLP.entails]
  simp [SLP.star, SLP.top, SLP.entails]

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  simp only [sbox]
  steps [rotate_left_intro]
  · subst_vars; rfl
  all_goals decide

theorem sbox_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "sbox" [] HList.nil) h![input])
    fun output => output = Skyscraper.sbox input := by
  enter_decl
  apply sbox_spec

theorem sgn0_spec : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.u 1) (FuncRef.decl "sgn0" [] HList.nil) h![input])
    fun output => output = (input.val % 2) := by
  enter_decl
  simp only [sgn0]
  steps
  simp_all

def List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
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
    · simp [replicate]
    · simp [List.takeD, List.take, ih]

theorem ZMod.cast_self {p : Fp P} : (p.cast : Fp P) = p := by
  unfold ZMod.cast
  simp only [Prime.natVal]
  apply natCast_zmod_val

lemma Fp.eq_of_val_eq {p} {x y: Fp p}: x.val = y.val → x = y := by
  simp [ZMod.val, Prime.natVal]
  exact Fin.eq_of_val_eq


/---

lemma BitVec.ofNat_1_eq_mod :  BitVec.ofNat 1 (x % 2) = BitVec.ofNat 1 x := by
  unfold BitVec.ofNat
  apply congrArg
  unfold Fin.ofNat'
  simp

lemma BitVec.ofNat_1_eq_0_iff : 0#1 = BitVec.ofNat 1 x ↔ x % 2 = 0 := by
  apply Iff.intro
  · unfold BitVec.ofNat
    intro h
    injection h with h
    simp [Fin.ofNat'] at h
    injection h with h
    rw [←h]
  · intro h
    unfold BitVec.ofNat
    apply BitVec.eq_of_toFin_eq
    simp only
    simp [Fin.ofNat', h]

lemma BitVec.ofNat_1_eq_1_iff : 1#1 = BitVec.ofNat 1 x ↔ x % 2 = 1 := by
  apply Iff.intro
  · unfold BitVec.ofNat
    intro h
    injection h with h
    simp [Fin.ofNat'] at h
    injection h with h
    rw [←h]
  · intro h
    unfold BitVec.ofNat
    apply BitVec.eq_of_toFin_eq
    simp only
    simp [Fin.ofNat', h]

lemma BitVec.one_eq_one_of_ne_zero {v : BitVec 1} : v ≠ 0#1 → v = 1#1 := by
  intro h
  rcases v with ⟨v⟩
  fin_cases v <;> tauto

instance : Fintype (BitVec 1) where
  elems := ⟨[0#1, 1#1], by simp⟩
  complete := by
    intro v
    rcases v with ⟨v⟩
    fin_cases v <;> simp

@[simp]
lemma List.Vector.toList_snoc : (List.Vector.snoc vs v).toList = vs.toList ++ [v] := by
  simp [snoc]

set_option trace.Lampe.STHoare.Helpers true
set_option trace.Lampe.SL true

@[simp]
lemma Int.castBitVec_ofNat {p} {n : Nat} : (Int.cast (OfNat.ofNat n) : Tp.denote p (Tp.u s)) = BitVec.ofNat s n := by
  rfl

theorem to_le_bits_intro {input} : STHoare lp env ⟦⟧ (to_le_bits.call h![] h![input]) fun v => v = Fp.toBitsLE 256 input := by
    enter_decl
    simp only [to_le_bits]
    steps

    enter_block_as v =>
      ([val ↦ ⟨.field, input⟩] ⋆ [bits ↦ v])
      (fun _ => [val ↦ ⟨.field, 0⟩] ⋆ [bits ↦ ⟨(Tp.u 1).array 256, Fp.toBitsLE 256 input⟩])

    loop_inv nat fun i _ _ => [val ↦ ⟨.field, ↑(input.val / 2^i)⟩] ⋆ [bits ↦ ⟨(Tp.u 1).array 256, Fp.toBitsLE i input |>.pad 256 0⟩]

    · decide
    · simp [Int.cast, IntCast.intCast, ZMod.cast_self]
    · have : input.val / 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 0 := by
        cases input
        conv => lhs; arg 1; whnf
        simp [Nat.div_eq_zero_iff, *, lp, p] at *
        linarith
      congr 1
      simp [Int.cast, IntCast.intCast]
      rw [this]
      rfl
    · intro i _ hi
      simp [IntCast.intCast, Int.cast] at hi
      steps [sgn0_spec]
      · let this : i % 4294967296 = i := by rw [Nat.mod_eq_of_lt]; linarith
        simp [Access.modify, Nat.mod_eq_of_lt, this, hi]
        rfl
      enter_block_as v =>
        ([val ↦ ⟨.field, v⟩])
        (fun _ => [val ↦ ⟨.field, ↑(v.val / 2)⟩])
      · simp only [ZMod.div2_on_vals]
        have : i % 4294967296 = i := by
          apply Nat.mod_eq_of_lt; linarith
        fin_cases «#v_11»
        · apply STHoare.iteTrue_intro
          steps
          casesm* ∃_,_
          subst_vars
          simp [ZMod.cast_self, this] at *
          rename 0#1 = _ => h
          rw [BitVec.ofNat_1_eq_0_iff] at h
          rw [h]
          simp [ZMod.cast_self]
        · apply STHoare.iteFalse_intro
          steps
          casesm* ∃_,_
          subst_vars
          simp [ZMod.cast_self, this] at *
          rename _ = BitVec.ofNat _ _ => h
          rw [BitVec.ofNat_1_eq_1_iff] at h
          simp [h, ZMod.cast_self]
      steps
      · simp only [pow_succ]
        congr 2
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
        · simp [Nat.div_div_eq_div_mul]
        · cases input
          apply lt_of_le_of_lt (Nat.div_le_self _ _) (by assumption)
      · congr 1
        casesm* ∃_,_
        subst_vars
        apply List.Vector.eq
        simp [-List.takeD_succ, Fp.toBitsLE, toBaseLE_succ_snoc, List.takeD_eq_take_append, hi, Nat.le_of_lt]
        rw [List.take_of_length_le (by simp_all [Nat.le_of_lt]), List.take_of_length_le (by simp_all [Nat.le_of_lt_succ])]
        have : (256 - i) = 255 - i + 1 := by omega
        simp [this, List.replicate_succ]
        simp [BitVec.ofNat_1_eq_mod, ZMod.val_natCast, ZMod.natCast_val]
        congr
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
        apply lt_of_le_of_lt (Nat.div_le_self _ _)
        simp [ZMod.val, lp, Prime.natVal]
    · decide

    steps
    simp_all

@[simp]
lemma List.chunksExact_length {h : List.length l = k*d} : (List.chunksExact d l h).length = k := by
  induction k generalizing l with
  | zero => simp [chunksExact]
  | succ k ih =>
    simp [chunksExact, ih]

lemma List.getElem_chunksExact {l : List α} {h : l.length = k*d} {hi}: (List.chunksExact d l h)[i]'hi = List.ofFn fun (j : Fin d) =>
  l[d*i + j.val]'(by
    simp [h];
    simp at hi;
    cases j;
    simp;
    apply lt_of_lt_of_le (Nat.add_lt_add_left (by assumption) _)
    rw [←Nat.mul_succ, mul_comm]
    apply Nat.mul_le_mul_right
    linarith
  ) := by
  simp at hi
  induction i generalizing l k with
  | zero =>
    have : k = k - 1 + 1 := by omega
    unfold chunksExact
    split
    · contradiction
    · apply List.ext_get
      · simp
        rename l.length = (_ + 1) * d => hl
        rw [hl]
        simp [Nat.succ_mul]
      · intro n _ _
        simp
  | succ n ih =>
    unfold chunksExact
    · split
      · contradiction
      · simp
        rw [ih]
        simp [Nat.mul_succ]
        ext
        congr 1
        ring
        linarith

lemma toBaseLE_elem_lt {B n i j : Nat} [hnz:NeZero B] {h} : (toBaseLE B n i)[j]'h < B := by
  induction n generalizing i j with
  | zero =>
    simp [toBaseLE]
    contradiction
  | succ n ih =>
    simp [toBaseLE]
    cases j
    · simp
      apply Nat.mod_lt
      apply Nat.zero_lt_of_ne_zero
      exact hnz.ne
    · simp [ih]

theorem to_le_bytes_intro {input} : STHoare lp env ⟦⟧ (to_le_bytes.call h![] h![input]) fun v => v = Fp.toBytesLE 32 input := by
  enter_decl
  simp only
  steps [to_le_bits_intro]
  enter_block_as =>
    ([bytes ↦ ⟨(Tp.u 8).array 32, List.Vector.replicate 32 0⟩])
    (fun _ => [bytes ↦ ⟨(Tp.u 8).array 32, Fp.toBytesLE 32 input⟩])

  · loop_inv nat fun i _ _ => [bytes ↦ ⟨(Tp.u 8).array 32, (Fp.toBytesLE 32 input).take i |>.pad 32 0⟩]
    · decide
    · intro i _ hi
      steps
      rw [Int.castBitVec_ofNat] at *
      simp at *
      casesm* ∃_,_, _∧_
      subst_vars
      simp [Access.modify]
      congr 1
      apply List.Vector.eq
      have : i ≤ 32 := by linarith
      have : i + 1 ≤ 32 := by linarith
      have : i % 4294967296 = i := by
        apply Nat.mod_eq_of_lt; linarith
      simp [-List.takeD_succ, List.takeD_eq_take_append, *, List.take_take]
      rw [List.take_succ, List.append_assoc]
      congr 1
      have : (32 - i) = (31 - i) + 1 := by omega
      simp [this, List.replicate_succ, getElem?, decidableGetElem?, hi]
      simp [Fp.toBytesLE]

      have : 256 = 2 ^ 8 := by rfl
      simp_rw [this]
      conv => rhs; arg 2; arg 1; rw [toBaseLE_pow (B:=2) (D:=8) (K:=32)]
      simp [List.getElem_chunksExact, ofBaseLE, Fp.toBitsLE, List.Vector.get]
      conv in (occs := *) ((8*i + _) % _) => all_goals rw [Nat.mod_eq_of_lt (by linarith)]
      conv in (8 * i % _) => rw [Nat.mod_eq_of_lt (by linarith)]
      ring_nf
      simp [BitVec.add_def, Nat.mod_eq_of_lt, toBaseLE_elem_lt]
      unfold BitVec.ofNat
      congr 1
      unfold Fin.ofNat'
      congr 1
      simp [mul_comm]
    · decide
  steps
  simp_all

lemma Fp.ofBaseLE_append : ofBaseLE B (a ++ b) = ofBaseLE B a + B^a.length * ofBaseLE B b := by
  induction a with
  | nil => simp [ofBaseLE]
  | cons h t ih =>
    simp only [ofBaseLE] at ih
    simp only [ofBaseLE, List.map, List.cons_append, List.foldr_cons, ih, List.length_cons, pow_succ]
    ring

theorem from_le_bytes_intro {input} : STHoare lp env ⟦⟧ (from_le_bytes.call h![] h![input])
    fun output => output = Lampe.Fp.ofBytesLE input.toList := by
  enter_decl
  simp only
  steps

  loop_inv nat fun i _ _ => [v ↦ ⟨.field, 256 ^ i⟩] ⋆ [result ↦ ⟨.field, Lampe.Fp.ofBytesLE $ input.toList.take i⟩]
  · decide
  · intro i _ hhi
    steps
    · simp_all [pow_succ]
    · congr 1
      casesm* ∃_,_
      subst_vars
      conv at hhi => rhs; whnf
      simp [List.take_succ, getElem?, decidableGetElem?, List.Vector.toList_length]
      simp only [hhi, Fp.ofBytesLE, List.map_append, Fp.ofBaseLE_append]
      have : i ≤ 32 := by linarith
      have : i % 4294967296 = i := by
        apply Nat.mod_eq_of_lt; linarith
      simp [*, List.Vector.get, ofBaseLE]
      rw [mul_comm]
      rfl
  · decide
  steps
  simp_all
  rw [List.take_of_length_le]
  · simp; decide

/---

def List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
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
    · simp [replicate]
    · simp [List.takeD, List.take, ih]

theorem as_array_intro (hi : input.length = 32) : STHoare lp env ⟦⟧ (Expr.call [Tp.slice (Tp.u 8)] (Tp.array (Tp.u 8) 32) (FuncRef.decl "as_array" [] HList.nil) h![input])
    fun output => output = ⟨input, hi⟩ := by
  enter_decl
  simp only [as_array]
  steps
  loop_inv fun i _ _ => [array ↦ ⟨Tp.array (Tp.u 8) 32, List.Vector.pad ⟨input.takeD i.toNat 0#8, List.takeD_length i.toNat _ _⟩ 32 0#8⟩]
  · decide
  · intros i hlo hhi
    steps
    casesm* ∃_,_
    subst_vars
    simp [Access.modify]
    congr 1
    rcases i with ⟨i, _⟩
    simp [IntCast.intCast, Int.cast, Fin.lt_def, OfNat.ofNat] at hhi
    apply List.Vector.eq
    simp only [List.Vector.toList_set, List.Vector.toList_pad, BitVec.toNat]
    simp only [List.Vector.toList]
    rw [Nat.mod_eq_of_lt (by linarith)]
    simp only [List.takeD_eq_take_append]
    have : i ≤ 32 := by linarith
    have : i + 1 ≤ 32 := by linarith
    simp [*, List.take_take]
    rw [List.take_succ, List.append_assoc]
    congr 1
    generalize_proofs
    have : 32 - i = (31 - i) + 1 := by omega
    simp [getElem?, decidableGetElem?, *, List.replicate]
  steps
  subst_vars
  apply List.Vector.eq
  simp only [List.Vector.toList_pad]
  simp only [List.Vector.toList]
  conv => enter [1,2,1]; whnf
  have : input.length ≤ input.length := by linarith
  simp only [←hi, Int.cast, IntCast.intCast, BitVec.ofInt, List.takeD_eq_take, this, List.take_length]

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [bar]
  steps [to_le_bytes_intro]

  enter_block_as
    ([new_left ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take 16 |>.map Skyscraper.sbox⟩])

  · loop_inv fun i _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
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
      casesm* ∃_,_
      subst_vars
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
      simp [this, List.replicate_succ, getElem?, decidableGetElem?, i₅, List.Vector.toList]

  steps

  enter_block_as
    ([new_right ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.map Skyscraper.sbox⟩])

  · loop_inv fun i _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
    · decide
    · congr 1
      apply List.Vector.eq
      simp [-List.takeD_succ, Int.cast, IntCast.intCast, List.takeD_eq_take_append, List.take_take]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps [sbox_intro]
      casesm* ∃_,_
      subst_vars
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
      simp [this, List.replicate_succ, getElem?, decidableGetElem?]
      simp only [hlt, dite_true, Option.toList]
      simp [List.cons_append, List.nil_append, List.Vector.toList]

  steps

  rename' «#v_25» => v

  enter_block_as =>
    ([new_bytes ↦ ⟨(Tp.u 8).slice, v.toList⟩])
    (fun _ => [new_bytes ↦ ⟨(Tp.u 8).slice, v.toList ++ ζi0.toList⟩])
  · loop_inv fun i _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice, v.toList ++ ζi0.toList.take i.toNat⟩]
    · decide
    · congr 1
      simp [Int.cast, IntCast.intCast]
    · congr 1
      simp
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps
      simp
      congr 1
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      casesm* ∃_,_
      subst «#v_30» elem
      have : i + 1 < 4294967296 := by linarith
      simp [Nat.mod_eq_of_lt, this, List.take_succ]
      simp [getElem?, decidableGetElem?, hlt]
      rfl

  steps [as_array_intro, from_le_bytes_intro]
  rotate_left
  · subst «#v_35» v
    simp
  · subst_vars
    rfl

-- theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
--     fun output => output = Skyscraper.bar input := by
--   enter_decl
--   apply bar_spec

-- theorem sigma_intro : STHoare lp env (⟦⟧)
--     (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
--       fun output => output = Skyscraper.SIGMA := by
--   enter_decl
--   simp only [Extracted.SIGMA]
--   steps []
--   unfold Skyscraper.SIGMA
--   assumption

-- theorem rc_intro : STHoare lp env (⟦⟧)
--     (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
--       fun output => output = ⟨Skyscraper.RC.toList, by rfl⟩ := by
--   enter_decl
--   simp only [Extracted.RC]
--   steps []
--   subst_vars
--   unfold Skyscraper.RC
--   rfl

-- theorem square_intro : STHoare lp env (⟦⟧)
--     (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
--       fun output => output = Skyscraper.square input := by
--   enter_decl
--   simp only [Extracted.square]
--   steps [sigma_intro]
--   unfold Skyscraper.square
--   subst_vars
--   rfl

-- theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
--     fun output => output = (Skyscraper.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Skyscraper.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by sorry -- TODO: This has a bad timeout now?
--   -- enter_decl
--   -- simp only [Extracted.permute]
--   -- steps [bar_intro, square_intro, rc_intro]
--   -- casesm* ∃_,_
--   -- simp [Builtin.indexTpl] at *
--   -- subst_vars
--   -- unfold Skyscraper.permute

-- theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
--     fun output => output = Skyscraper.compress l r := by
--   simp only [compress]
--   steps [permute_intro]
--   unfold Skyscraper.compress
--   subst_vars
--   simp [Skyscraper.State.permute]
--   casesm*∃_,_
--   subst_vars
--   simp
--   congr 1
