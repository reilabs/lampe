import «std-1.0.0-beta.14».Extracted
import Lampe
import Lampe.Crypto.Aes128

/-!
# `std::aes128::aes128_encrypt<N>` spec

The Noir stdlib wrapper around the `aes128_encrypt` foreign builtin
performs PKCS#7 padding before invoking the builtin:

```
let padding_length = (16 - N % 16) : u8
let mut padded_input = [0u8; N + 16 - N%16]
for i in 0..N do padded_input[i] = input[i]
for i in N..N+16-N%16 do padded_input[i] = padding_length
output = aes128_encrypt_padded_input(padded_input, iv, key)
```

This file proves `aes128_encrypt<N>` evaluates to
`Lampe.Crypto.Aes128.aes128CbcEncryptPkcs7 key iv input`.
-/

namespace Lampe.Stdlib.Aes128

open «std-1.0.0-beta.14»
open Lampe.Crypto

/-- Direct builtin spec: `aes128Encrypt` applied to an input,
returning `Crypto.Aes128.aes128Encrypt`. -/
theorem aes128_encrypt_builtin_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)}
    {iv : Tp.denote p ((Tp.u 8).array (16 : U 32))}
    {key : Tp.denote p ((Tp.u 8).array (16 : U 32))} :
    STHoare p env ⟦⟧
      (.callBuiltin
        [(Tp.u 8).array N, (Tp.u 8).array (16 : U 32), (Tp.u 8).array (16 : U 32)]
        ((Tp.u 8).array N)
        Builtin.aes128Encrypt h![input, iv, key])
      (fun r => r = Crypto.Aes128.aes128Encrypt input iv key) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.aes128Encrypt rfl N p env
    h![input, iv, key]

/-! ### Wrapper spec -/

set_option maxHeartbeats 800000 in
theorem aes128_encrypt_spec {p} {N : U 32}
    {input : Tp.denote p ((Tp.u 8).array N)}
    {iv : Tp.denote p ((Tp.u 8).array (16 : U 32))}
    {key : Tp.denote p ((Tp.u 8).array (16 : U 32))}
    (hN : N.toNat + 16 < 2^32) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::aes128::aes128_encrypt».call h![N] h![input, iv, key])
      (fun r => r.toList =
        Crypto.Aes128.aes128CbcEncryptRaw key iv (Crypto.Aes128.pkcs7Pad input.toList)) := by
  set M : U 32 := (N.add 16).sub (N.umod 16) with hMdef
  have hMtoNat : M.toNat = N.toNat + 16 - N.toNat % 16 := by
    have hmod : (N.toNat % 16) < 16 := Nat.mod_lt _ (by decide)
    have h1 : (N + 16).toNat = N.toNat + 16 := by
      rw [BitVec.toNat_add]
      have : (N.toNat + 16) % 2^32 = N.toNat + 16 :=
        Nat.mod_eq_of_lt (by simpa using hN)
      simpa using this
    have h2 : (N.umod 16).toNat = N.toNat % 16 := by
      simp [BitVec.toNat_umod]
    show ((N + 16) - (N.umod 16)).toNat = _
    rw [BitVec.toNat_sub_of_le]
    · rw [h1, h2]
    · rw [BitVec.le_def, h1, h2]; omega
  enter_decl
  steps
  -- First loop invariant: padded_input is `input.toList.take i ++ replicate (M - i) 0`.
  loop_inv nat fun i hlo hhi =>
    [padded_input ↦ ⟨(Tp.u 8).array M,
      ⟨input.toList.take i ++ List.replicate (M.toNat - i) (0 : BitVec 8),
        by
          have hN_le_M : N.toNat ≤ M.toNat := by rw [hMtoNat]; omega
          have hi_le_N : i ≤ N.toNat := by exact_mod_cast hhi
          have htl : input.toList.length = N.toNat := input.toList_length
          simp [List.length_append, List.length_take, List.length_replicate, htl]
          omega⟩⟩]
  · simp  -- entry condition: 0 ≤ N
  · intro i _hlo hhi  -- body
    steps
    have hN_le_M : N.toNat ≤ M.toNat := by rw [hMtoNat]; omega
    have hi_lt_M : i < M.toNat := lt_of_lt_of_le hhi hN_le_M
    have htl : input.toList.length = N.toNat := input.toList_length
    have htake_len : (input.toList.take i).length = i := by
      rw [List.length_take]; omega
    have hi_lt_len : i < input.toList.length := by omega
    simp_all only [Lens.modify, Lens.get, Access.modify, BitVec.toNat_ofNatLT,
      Builtin.CastTp.cast, BitVec.setWidth_eq]
    congr 1
    apply Subtype.ext
    show ((some (List.Vector.set _ ⟨i, _⟩ (List.Vector.get input ⟨i, _⟩))).get
            (by simp) : List.Vector _ _).toList = _
    simp only [Option.get_some, List.Vector.toList_set, List.Vector.toList_mk]
    have hi_lt_len' : i < input.toList.length := by omega
    rw [List.set_append, if_neg (by simp [htake_len])]
    simp only [htake_len, Nat.sub_self]
    have hrepl_eq : List.replicate (M.toNat - i) (0 : BitVec 8) =
        (0 : BitVec 8) :: List.replicate (M.toNat - i - 1) 0 := by
      conv_lhs => rw [show M.toNat - i = (M.toNat - i - 1) + 1 by omega]
      rw [List.replicate_succ]
    rw [hrepl_eq]
    simp only [List.set_cons_zero]
    have h_take_succ :
        input.toList.take (i + 1) = input.toList.take i ++ [input.toList[i]'hi_lt_len'] := by
      rw [List.take_add_one]
      rw [List.getElem?_eq_getElem hi_lt_len']
      simp
    have hMi_eq : M.toNat - i - 1 = M.toNat - (i + 1) := by omega
    rw [hMi_eq, h_take_succ, List.append_assoc]
    rfl
  -- After first loop: array = take N input ++ replicate (M-N) 0
  steps
  -- Second loop fills slots N..M with padding_length
  -- The upper bound is N + 16 - N%16, which equals M as BitVecs.
  have hMeq2 : N + (16 : U 32) - N % (16 : U 32) = M := by rfl
  -- Recover padding_length = u8 cast of (16 - N%16).
  rename_i hpad _ _ _ _
  -- Get the numeric value of padding_length.
  have hpad_val : padding_length = BitVec.ofNat 8 (M.toNat - N.toNat) := by
    rw [hpad, hMtoNat]
    have h1 : ((16 : U 32) - N % (16 : U 32)).toNat = 16 - N.toNat % 16 := by
      rw [BitVec.toNat_sub_of_le]
      · simp [BitVec.toNat_umod]
      · rw [BitVec.le_def]
        simp [BitVec.toNat_umod]
        exact Nat.le_of_lt (Nat.mod_lt _ (by decide))
    show (Builtin.CastTp.cast _ : BitVec 8) = _
    simp [Builtin.CastTp.cast, BitVec.setWidth]
    congr 1
    have hmod : N.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    omega
  -- Second loop invariant
  have hN_le_M : N.toNat ≤ M.toNat := by rw [hMtoNat]; omega
  have htl : input.toList.length = N.toNat := input.toList_length
  loop_inv nat fun i hlo hhi =>
    [padded_input ↦ ⟨(Tp.u 8).array M,
      ⟨input.toList ++ List.replicate (i - N.toNat) padding_length
        ++ List.replicate (M.toNat - i) (0 : BitVec 8),
        by
          have hMub : ((N + (16 : U 32)) - N % (16 : U 32)).toNat = M.toNat := by
            rw [hMeq2]
          have hi_le_M : i ≤ M.toNat := by rw [← hMub]; exact hhi
          have hi_ge_N : N.toNat ≤ i := hlo
          simp [List.length_append, List.length_replicate, htl]
          omega⟩⟩]
  · -- Entry: prove heap state matches invariant at i = N
    congr 1
    apply Subtype.ext
    have htake : input.toList.take N.toNat = input.toList := by
      apply List.take_of_length_le; rw [htl]
    simp [htake]
  · -- Entry: prove N ≤ hi (the existential witness)
    show N.toNat ≤ (N + (16 : U 32) - N % (16 : U 32)).toNat
    rw [show (N + (16 : U 32) - N % (16 : U 32)) = M from hMeq2]
    exact hN_le_M
  · -- Body: at slot i, change 0 to padding_length
    intro i hlo hhi
    steps
    have hi_le_M_strict : i < M.toNat := by
      have hMub : ((N + (16 : U 32)) - N % (16 : U 32)).toNat = M.toNat := by rw [hMeq2]
      rw [← hMub]; exact hhi
    have hi_ge_N : N.toNat ≤ i := hlo
    simp_all only [Lens.modify, Lens.get, Access.modify, BitVec.toNat_ofNatLT,
      Builtin.CastTp.cast]
    congr 1
    apply Subtype.ext
    show (List.Vector.set _ ⟨i, _⟩ (BitVec.zeroExtend 8 ((16 : U 32) - N % (16 : U 32)))).toList = _
    simp only [List.Vector.toList_set, List.Vector.toList_mk]
    -- Goal shape: (input ++ replicate (i-N) pad ++ replicate (M-i) 0).set i pad = RHS
    -- The outer ++ is between (input ++ rep_pad) and rep_zero; set offset i lands in rep_zero.
    rw [List.set_append, if_neg (by
      simp [List.length_append, List.length_replicate, htl]
      omega)]
    have hlen_left : ∀ x : BitVec 8,
        (input.toList ++ List.replicate (i - N.toNat) x).length = i := by
      intro x
      simp [List.length_append, List.length_replicate, htl]; omega
    rw [hlen_left, Nat.sub_self]
    -- Now: input ++ rep_pad ++ (replicate (M-i) 0).set 0 pad
    have hrepl_eq : List.replicate (M.toNat - i) (0 : BitVec 8) =
        (0 : BitVec 8) :: List.replicate (M.toNat - i - 1) 0 := by
      conv_lhs => rw [show M.toNat - i = (M.toNat - i - 1) + 1 by omega]
      rw [List.replicate_succ]
    rw [hrepl_eq]
    simp only [List.set_cons_zero]
    -- Now: input ++ rep_pad ++ (pad :: replicate (M-i-1) 0)
    -- RHS: input ++ replicate (i+1-N) pad ++ replicate (M-(i+1)) 0
    have hpad_succ : ∀ (x : BitVec 8),
        List.replicate (i + 1 - N.toNat) x =
        List.replicate (i - N.toNat) x ++ [x] := by
      intro x
      have : i + 1 - N.toNat = (i - N.toNat) + 1 := by omega
      rw [this, List.replicate_add]
      simp
    rw [hpad_succ]
    have hMi_eq : M.toNat - i - 1 = M.toNat - (i + 1) := by omega
    rw [hMi_eq]
    simp only [List.append_assoc, List.singleton_append]
    congr 2
  -- After second loop: array = input ++ replicate (M-N) padding_length ++ replicate 0 0
  steps [aes128_encrypt_builtin_spec]
  -- After steps + builtin spec: state has hypotheses about the result.
  -- Goal:  v.toList = aes128CbcEncryptRaw key iv (pkcs7Pad input.toList)
  -- with output = aes128Encrypt ⟨padded list, ..⟩ iv key, v = output.
  -- Coercion-normalized hub_eq: the BitVec.toNat of the loop bound equals M.toNat.
  -- We capture it via `set` to ensure the expression matches.
  -- Note: `↑16 = (16 : U 32) = 16#32` are all definitionally equal.
  -- The padded list in the call
  have htl : input.toList.length = N.toNat := input.toList_length
  -- Bridge lemma needs M.toNat % 16 = 0
  have hM_dvd : M.toNat % 16 = 0 := by
    rw [hMtoNat]
    have hmod : N.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have h : N.toNat + 16 - N.toNat % 16 = 16 * (N.toNat / 16 + 1) := by
      have hdm := Nat.div_add_mod N.toNat 16
      omega
    rw [h]; exact Nat.mul_mod_right 16 _
  -- Equality of the padded list with pkcs7Pad input.toList
  have hMN : M.toNat - N.toNat = 16 - N.toNat % 16 := by
    rw [hMtoNat]
    have hmod : N.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    omega
  subst_vars
  rw [Crypto.Aes128.aes128Encrypt_toList_of_dvd16 _ iv key hM_dvd]
  -- Now: aes128CbcEncryptRaw key iv (padded.toList) = aes128CbcEncryptRaw key iv (pkcs7Pad input.toList)
  congr 1
  -- Goal: padded.toList = pkcs7Pad input.toList
  -- Show that the appended `replicate 0` is empty by recognizing M = N + ↑16 - N % ↑16.
  change input.toList ++ List.replicate (M.toNat - N.toNat) (Builtin.CastTp.cast _ : BitVec 8)
    ++ List.replicate (M.toNat - M.toNat) (0 : BitVec 8) = _
  rw [Nat.sub_self, List.replicate_zero, List.append_nil]
  unfold Crypto.Aes128.pkcs7Pad
  rw [htl, hMN]
  congr 1
  -- Now: replicate (16 - N%16) (cast (↑16 - N % ↑16)) = replicate (16 - N%16) (ofNat 8 (16 - N%16))
  congr 1
  -- LHS: Builtin.CastTp.cast (↑16 - N % ↑16) : BitVec 8
  -- RHS: BitVec.ofNat 8 (16 - N.toNat % 16)
  have h2 : ((16 : U 32) - N % (16 : U 32)).toNat = 16 - N.toNat % 16 := by
    rw [BitVec.toNat_sub_of_le]
    · simp [BitVec.toNat_umod]
    · rw [BitVec.le_def]
      simp [BitVec.toNat_umod]
      have : N.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      omega
  show (Builtin.CastTp.cast ((16 : U 32) - N % (16 : U 32)) : BitVec 8) = _
  simp [Builtin.CastTp.cast, BitVec.setWidth]
  apply BitVec.eq_of_toNat_eq
  have hmod : N.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
  simp [BitVec.toNat_ofNat]
  omega

end Lampe.Stdlib.Aes128
