import Merkle.Extracted
import Merkle.Field
import Merkle.Ref
import Lampe

import ProvenZk

import Mathlib.Data.Vector.Snoc

open Lampe Ref Extracted

namespace Spec

def lp : Lampe.Prime := ⟨p, pPrime⟩

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

theorem recover_zero (h : n = 0) : MerkleTree.recover (depth := n) H' idx proof item = item := by
  cases h
  rfl

def List.Vector.takeF {α : Type} {n : Nat} (v : List.Vector α n) (i : Nat) (hi : i ≤ n) : List.Vector α i :=
  List.Vector.congr (by simp [hi]) (v.take i)

theorem List.Vector.takeF_congr (he: i₁ = i₂) : List.Vector.takeF v i₁ h = he ▸ List.Vector.takeF v i₂ (he ▸ h) := by
  cases he
  rfl

theorem List.Vector.takeF_succ_eq_snoc_get {v : List.Vector α n} : List.Vector.takeF v (i + 1) hi = (List.Vector.takeF v i (by linarith)).snoc (v.get ⟨i, by linarith⟩) := by
  rcases v with ⟨v, rfl⟩
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, List.Vector.snoc, List.Vector.get, List.take_succ]

@[simp]
theorem List.Vector.congrArg₂ {f : {n : Nat} → List.Vector α n → List.Vector β n → γ} (h₁ h₂ : n = n₁):
  @f n₁ (h₁ ▸ v₁) (h₂ ▸ v₂) = @f n v₁ v₂ := by
  cases h₁
  cases h₂
  rfl

@[simp]
theorem List.Vector.cast_reverse {h : n₁ = n₂} {v : List.Vector α n₁} : (h ▸ v).reverse = h ▸ v.reverse := by
  cases h
  rfl

@[simp]
theorem List.Vector.takeF_all {v : List.Vector α n} : List.Vector.takeF v n (by simp) = v := by
  cases v
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, *]

@[simp]
theorem List.Vector.takeF_all_of_eq {v : List.Vector α n} (h : n₁ = n) : List.Vector.takeF v n₁ (by simp_all) = h ▸ v := by
  cases h
  cases v
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, *]

theorem recover_intro {H N idx proof item}
    (hHash : ∀ {a b}, STHoare lp env
        ⟦True⟧
        (Expr.call [Tp.field, Tp.field] Tp.field
          (FuncRef.trait (some H) "BinaryHasher" [Kind.type] (HList.cons Tp.field HList.nil) "hash" [] HList.nil) h![a,b])
        (fun v => v = H' (a ::ᵥ b ::ᵥ .nil))):
    STHoare lp env ⟦True⟧ (mtree_recover.call h![H, N] h![idx, proof, item]) (fun v => v = MerkleTree.recover H' idx.reverse proof.reverse item) := by
  enter_decl
  simp only [mtree_recover]
  steps
  loop_inv fun i _ _ =>
    [curr_h ↦ ⟨Tp.field,
      MerkleTree.recover H' (List.Vector.takeF idx i.toNat (by simpa [←BitVec.lt_def];)).reverse
                 (List.Vector.takeF proof i.toNat (by simpa [←BitVec.lt_def])).reverse item⟩]
  · simp [BitVec.le_def, Int.cast, IntCast.intCast]
  · intro i _ hi
    steps
    enter_block_as m =>
      ([curr_h ↦ ⟨Tp.field, m⟩])
      (fun _ => [curr_h ↦ ⟨Tp.field, if dir then H' (sibling_root ::ᵥ m ::ᵥ .nil) else H' (m ::ᵥ sibling_root ::ᵥ .nil) ⟩])
    apply STHoare.ite_intro <;> {
      rintro rfl
      steps [hHash]
      simp_all
    }
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      rcases N with ⟨N, lt⟩
      simp [BitVec.lt_def] at hi
      simp
      linarith []
    congr 1
    simp_rw [List.Vector.takeF_congr this, List.Vector.cast_reverse]
    rw [List.Vector.congrArg₂ (f := fun a b => MerkleTree.recover _ a b _)]
    casesm* ∃_, _
    rename dir = _ => hdir
    rename sibling_root = _ => hsr
    simp at hdir hsr
    simp [MerkleTree.recover, List.Vector.takeF_succ_eq_snoc_get, ←hdir, ←hsr]
    cases dir <;> rfl

  steps
  subst_vars
  congr
  all_goals simp

theorem rl_intro : STHoare lp env ⟦⟧
    (rl.call h![] h![input])
    fun output => output = Ref.rl input := by
  enter_decl
  steps
  subst_vars
  rfl

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
      (rotate_left.call h![] h![input, N])
      fun output => output = Ref.rotateLeft input N := by
  enter_decl
  simp only [rotate_left]
  steps
  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Ref.rl i.toNat input⟩]
  change 0 ≤ N
  · bv_decide
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
    simp_all [Ref.rotateLeft]

theorem sbox_intro : STHoare lp env ⟦⟧ (sbox.call h![] h![input])
    fun output => output = Ref.sbox input := by
  enter_decl
  simp only [Extracted.sbox]
  steps [rotate_left_intro]
  · subst_vars; rfl
  all_goals decide

theorem sgn0_intro : STHoare lp env ⟦⟧ (sgn0.call h![] h![input])
    fun (output: BitVec 1) => output = input.val % 2 := by
  enter_decl
  simp only [sgn0]
  steps
  simp_all

lemma ZMod.div2_on_vals (v : Lampe.Fp lp) :
    v.val / 2 = match v.val % 2 with
    | 0 => (v / 2).val
    | _ => ((v - 1) / 2).val := by

  have two_unit := ZMod.inv_mul_of_unit 2 (ZMod.isUnit_iff_coprime 2 lp.natVal |>.mpr (by decide))
  have vVal_decomp := Nat.div_add_mod v.val 2
  have v_decomp : v = 2 * ↑(v.val / 2) + ↑(v.val % 2) := by
    apply Fp.eq_of_val_eq
    rw [ZMod.val_add, ZMod.val_mul, ZMod.val_natCast, ZMod.val_natCast]
    conv in v.val / 2 % _ => rw [Nat.mod_eq_of_lt (by apply lt_of_le_of_lt (Nat.div_le_self _ _) v.prop)]
    conv in ZMod.val 2 => whnf
    conv in 2 * _ % _ => rw [Nat.mod_eq_of_lt (by apply lt_of_le_of_lt (Nat.mul_div_le _ _) v.prop)]
    conv in v.val % _ % _ => rw [Nat.mod_eq_of_lt (by apply lt_of_le_of_lt (Nat.mod_le _ _) v.prop)]
    rw [vVal_decomp, Nat.mod_eq_of_lt]
    exact v.prop

  split <;> {
    rename_i h
    try simp only [imp_false, Nat.mod_two_not_eq_zero] at h
    rw [←vVal_decomp]
    conv => rhs; rw [v_decomp]
    rw [h]
    ring_nf
    rw [mul_assoc, two_unit]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_right₀, mul_one]
    rewrite [ZMod.val_natCast, Nat.mod_eq_of_lt]
    · omega
    · simp only [ZMod.val, Prime.natVal]
      omega
  }

@[simp]
lemma Fp.cast_u {s P} {v : Fp P} : (v.cast : U s) = BitVec.ofNat s (v.val) := by rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem to_le_bits_intro {input} : STHoare lp env ⟦⟧ (to_le_bits.call h![] h![input]) fun v => v = Fp.toBitsLE 256 input := by
    enter_decl
    simp only [to_le_bits]
    steps

    enter_block_as v =>
      ([val ↦ ⟨.field, input⟩] ⋆ [bits ↦ v])
      (fun _ => [val ↦ ⟨.field, 0⟩] ⋆ [bits ↦ ⟨(Tp.u 1).array 256, Fp.toBitsLE 256 input⟩])

    loop_inv nat fun i _ _ => [val ↦ ⟨.field, ↑(input.val / 2^i)⟩] ⋆ [bits ↦ ⟨(Tp.u 1).array 256, Fp.toBitsLE i input |>.pad 256 0⟩]
    · decide
    · simp [Int.cast, IntCast.intCast, Fp.cast_self]
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
      steps [sgn0_intro]
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
          rename 0#1 = _ => h
          simp [*] at *
          rw [BitVec.ofNat_1_eq_0_iff] at h
          simp [Fp.cast_self, h]
        · apply STHoare.iteFalse_intro
          steps
          casesm* ∃_,_
          subst_vars
          simp [Fp.cast_self, this] at *
          rename _ = BitVec.ofNat _ _ => h
          rw [BitVec.ofNat_1_eq_1_iff] at h
          simp [h, Fp.cast_self]
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

lemma Int.castBitVec_ofNat {p} {n : Nat} : (Int.cast (OfNat.ofNat n) : Tp.denote p (Tp.u s)) = BitVec.ofNat s n := by
  rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
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
      casesm* ∃_,_, _∧_
      rw [Int.castBitVec_ofNat] at *
      simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, zero_le, Nat.reduceMod,
        BitVec.natCast_eq_ofNat, BitVec.reduceToInt, Int.reducePow, exists_prop,
        BitVec.ofNat_eq_ofNat, BitVec.reduceToNat, Builtin.instCastTpU, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.toInt_setWidth, neg_mul, Lens.modify, Lens.get,
        Option.bind_eq_bind, Option.some_bind, Option.bind_some] at *
      subst_vars
      simp only [Access.modify, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        BitVec.reduceToNat, BitVec.toNat_mul, Nat.mul_mod_mod, BitVec.toNat_add, Nat.one_mod,
        Nat.mod_add_mod, Option.get_dite]
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
      simp only [List.Vector.get, Fp.toBitsLE, Fin.cast_eq_self, List.get_eq_getElem,
        List.getElem_map, BitVec.natCast_eq_ofNat, Nat.reduceMul, ofBaseLE,
        List.getElem_chunksExact, List.ofFn_succ, Fin.isValue, Fin.val_zero, add_zero, Fin.val_succ,
        zero_add, Nat.reduceAdd, Fin.val_eq_zero, List.ofFn_zero, List.foldr_cons, List.foldr_nil,
        mul_zero]
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

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
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
      simp only [hhi, Fp.ofBytesLE, List.map_append, ofBaseLE_append]
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
  · simp

theorem as_array_intro (hi : input.length = 32) : STHoare lp env ⟦⟧
    (as_array.call h![] h![input])
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

set_option maxHeartbeats 3000000000000
theorem bar_intro : STHoare lp env ⟦⟧ (bar.call h![] h![input])
    fun output => output = Ref.bar input := by
  enter_decl
  simp only [Extracted.bar]
  steps [to_le_bytes_intro]

  enter_block_as
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

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Extracted.SIGMA.call h![] h![])
      fun output => output = Ref.SIGMA := by
  enter_decl
  simp only [Extracted.SIGMA]
  steps []
  unfold Ref.SIGMA
  assumption

theorem rc_intro : STHoare lp env (⟦⟧)
    (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
      fun output => output = ⟨Ref.RC.toList, by rfl⟩ := by
  enter_decl
  simp only [Extracted.RC]
  steps []
  subst_vars
  unfold Ref.RC
  rfl

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Ref.square input := by
  enter_decl
  simp only [Extracted.square]
  steps [sigma_intro]
  unfold Ref.square
  subst_vars
  rfl

theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
    fun output => output = (Ref.State.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Ref.State.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by
  enter_decl
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn
  simp only [Extracted.permute]
  steps [bar_intro, square_intro, rc_intro]
  casesm* ∃_,_
  simp [Builtin.indexTpl, Nat.mod_eq_of_lt, lp] at *
  subst_vars
  rfl

instance {α H n} : Membership α (MerkleTree α H n) where
  mem t e := ∃p, e = MerkleTree.itemAt t p

lemma SkyscraperHash_correct: STHoare lp env ⟦⟧ (Expr.call [Tp.field, Tp.field] Tp.field
          (FuncRef.trait (some $ «struct#Skyscraper».tp h![]) "BinaryHasher" [Kind.type] (HList.cons Tp.field HList.nil) "hash" [] HList.nil) h![a,b]) (fun v => v = Ref.State.compress ⟨[a, b], rfl⟩) := by
  enter_trait [] env
  steps [permute_intro]
  casesm*∃_,_
  subst_vars
  congr 1

lemma weird_assert_eq_intro : STHoare lp env ⟦⟧ (weird_assert_eq.call h![] h![a, b]) (fun _ => a = b) := by
  enter_decl
  simp only
  steps
  enter_block_as (⟦⟧) (fun _ => ⟦⟧)
  · enter_decl
    simp only
    steps
  steps
  simp_all

theorem main_correct [Fact (CollisionResistant Ref.State.compress)] {tree : MerkleTree (Fp lp) Ref.State.compress 32}:
    STHoare lp env
        ⟦⟧
        (main.call h![] h![tree.root, proof, item, index])
        (fun _ => item ∈ tree) := by
  enter_decl
  simp only
  steps [recover_intro (H:= «struct#Skyscraper».tp h![]) (N:=32) (hHash := SkyscraperHash_correct), weird_assert_eq_intro]
  use index.reverse
  subst_vars
  rename tree.root = _ => hroot
  rw [Eq.comm, MerkleTree.recover_eq_root_iff_proof_and_item_correct] at hroot
  exact hroot.2
