import «std-1.0.0-beta.25».Extracted
import Lampe
import Stdlib.EmbeddedCurveOps
import Stdlib.Field.Bn254
import Stdlib.Hash.Mod

namespace Lampe.Stdlib.Hash.Pedersen

open «std-1.0.0-beta.25»
open Lampe.Builtin (bytesToList)
open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen
open Lampe.Stdlib.EmbeddedCurveOps

/-- Alias for the BN254 high limb (`PHI` field constant) as a `Nat`.
Not `private`: it appears in the public `from_field_unsafe_spec` statement. -/
abbrev phi : Nat := Lampe.Crypto.Bn254.phi

/-- Alias for the BN254 low limb (`PLO` field constant) as a `Nat`.
Not `private`: it appears in the public `from_field_unsafe_spec` statement. -/
abbrev plo : Nat := Lampe.Crypto.Bn254.plo

/-- Alias for `2^128` as a `Nat`.
Not `private`: it appears in the public `from_field_unsafe_spec` statement. -/
abbrev pow128 : Nat := Lampe.pow128

/-!
# Stdlib specs for `std::hash` Pedersen wrappers

This module proves STHoare triples for all 5 Noir stdlib functions
that sit on top of the `derive_pedersen_generators` foreign builtin:

- `derive_generators_spec` — pass-through wrapper around the builtin
- `from_field_unsafe_spec` — ∃-limbs decomposition `scalar = xlo + 2^128 * xhi`
- `pedersen_commitment_with_separator_spec_canonical` — substantive MSM spec
- `pedersen_hash_with_separator_spec_canonical` — substantive
  MSM-then-`pointX` spec
- `pedersen_commitment_spec_canonical`, `pedersen_hash_spec_canonical` —
  wrappers at `separator = 0`

The public `_spec_canonical` theorems express the result as the pure
closed forms `pedersenCommitment` /
`pedersenHash` (BLAKE3 hash-to-curve + Tonelli-Shanks generators, with
each input collapsed to its canonical limb decomposition). They are
derived from private existential `_spec` intermediates that expose the
per-slot `from_field_unsafe` output as an existential `Ss` witness
satisfying `FromFieldUnsafeWitness` (limb relation, canonical-range
disjunction, and limb-range canonicality).
-/

/-! ### `derive_pedersen_generators` builtin spec -/

private theorem derivePedersenGenerators_builtin_spec {p}
    {N M : U 32}
    {domainBytes : Tp.denote p ((Tp.u 8).array M)}
    {startIdx : U 32} :
    STHoare p env ⟦⟧
      (.callBuiltin [(Tp.u 8).array M, Tp.u 32] (pointTp.array N)
        Builtin.derivePedersenGenerators h![domainBytes, startIdx])
      (fun r =>
        r = derivePedersenGenerators p
          (bytesToList (M := M) domainBytes)
          startIdx.toNat
          N.toNat) := by
  exact STHoare.genericTotalPureBuiltin_intro Builtin.derivePedersenGenerators rfl
    (N, M) p env h![domainBytes, startIdx]

/-! ### `derive_generators` wrapper spec -/

theorem derive_generators_spec {p} {N M : U 32}
    {domainBytes : Tp.denote p ((Tp.u 8).array M)}
    {startIdx : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::derive_generators».call h![N, M]
        h![domainBytes, startIdx])
      (fun r =>
        r = derivePedersenGenerators p
          (bytesToList (M := M) domainBytes)
          startIdx.toNat
          N.toNat) := by
  enter_decl
  steps [derivePedersenGenerators_builtin_spec (p := p) (N := N) (M := M)
    (domainBytes := domainBytes) (startIdx := startIdx)]
  assumption

/-! ### Bridging lemmas -/

private lemma strAsBytes_default_domain_eq {p} :
    bytesToList (p := p) (M := (24 : U 32))
      (Lampe.NoirStr.of "DEFAULT_DOMAIN_SEPARATOR") = defaultDomainBytes := by
  rfl

private lemma strAsBytes_hash_length_eq {p} :
    bytesToList (p := p) (M := (20 : U 32))
      (Lampe.NoirStr.of "pedersen_hash_length") = pedersenHashLengthBytes := by
  rfl

/-! ### `from_field_unsafe` wrapper spec -/

/-- Spec for `std::hash::from_field_unsafe`. The body decomposes
`scalar` into two field limbs `xlo, xhi` via the `decompose_hint`
oracle and then enforces

```
scalar = xlo + 2^128 * xhi                  -- limb decomposition
(xhi, xlo) <ₗₑₓ (PHI, PLO)                  -- canonical-range
```

where `PLO + 2^128 * PHI = p` is the BN254 scalar-field prime
limb decomposition. The output `EmbeddedCurveScalar` is
`Scalar.mk xlo xhi`.

Unlike `decompose`, `from_field_unsafe` does **not** call
`assert_max_bit_size<128>` on the limbs, so the per-limb bounds
`xlo.val, xhi.val < 2^128` are *not* part of the postcondition;
the constraint enforced is the canonical-range disjunction
below. -/
theorem from_field_unsafe_spec {p} [Lampe.Crypto.Bn254.Prime p]
    {scalar : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::from_field_unsafe».call h![] h![scalar])
      (fun r =>
        ∃∃ xlo xhi,
          r = Scalar.mk xlo xhi ∧
          scalar = xlo + (pow128 : Fp p) * xhi ∧
          ((xhi = (phi : Fp p) ∧ xlo.val < plo) ∨ xhi.val < phi)) := by
  enter_decl
  apply STHoare.letIn_intro
    (Q := fun (_ : Tp.denote p (Tp.tuple none [Tp.field, Tp.field])) => ⟦⟧)
  · steps [Lampe.Stdlib.Field.Bn254.decompose_hint_intro (p := p)]
  intro xlo_xhi
  steps [Lampe.Stdlib.Field.Bn254.two_pow_128_spec (p := p),
    Lampe.Stdlib.Field.Bn254.phi_spec (p := p),
    Lampe.Stdlib.Field.Bn254.plo_spec (p := p),
    Lampe.Stdlib.Field.Bn254.assert_lt_intro (p := p)]
  rename_i hxlo hxhi _ hassert
  -- Bind the ite result and case-split on the condition.
  apply STHoare.letIn_intro
    (Q := fun (v : Tp.denote p (Tp.tuple none [Tp.field, Tp.field])) =>
      ⟦v = (if decide (xhi = (phi : Fp p)) then (xlo, (plo : Fp p), ())
            else (xhi, (phi : Fp p), ()))⟧)
  · -- Prove the ite produces the expected tuple.
    apply STHoare.ite_intro
    · intro h_eq
      steps [Lampe.Stdlib.Field.Bn254.plo_spec (p := p)]
      subst_vars
      simp_all
    · intro h_ne
      steps [Lampe.Stdlib.Field.Bn254.phi_spec (p := p)]
      subst_vars
      simp_all
  -- Bridge lemma: `(plo : Fp p).val = plo` under `[Bn254.Prime p]`. Used by the xhi=phi branch via aesop.
  have hplo_val : ((plo : Nat) : Fp p).val = plo := by
    have hplo_lt : (plo : Nat) < p.natVal := by
      have : (plo : Nat) < Lampe.pow128 := by decide
      linarith [this, Lampe.Crypto.Bn254.pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hplo_lt)
  have hphi_val : ((phi : Nat) : Fp p).val = phi := by
    have hphi_lt : (phi : Nat) < p.natVal := by
      have : (phi : Nat) < Lampe.pow128 := by decide
      linarith [this, Lampe.Crypto.Bn254.pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hphi_lt)
  intro v
  -- Discharge the ⟦ v = ... ⟧ pure precondition and split on the bool.
  by_cases h_xhi : xhi = (phi : Fp p)
  · -- Branch: xhi = phi, so v = (xlo, plo, ()). After assert_lt(xlo, plo) we get xlo.val < plo.
    have h_xhi_eq : decide (xhi = (phi : Fp p)) = true := by simp [h_xhi]
    simp only [h_xhi_eq, if_true] at *
    steps [Lampe.Stdlib.Field.Bn254.assert_lt_intro (p := p)]
    simp [SLP.exists_pure] at *
    sl
    aesop
  · -- Branch: xhi ≠ phi, so v = (xhi, phi, ()). After assert_lt(xhi, phi) we get xhi.val < phi.
    have h_xhi_eq : decide (xhi = (phi : Fp p)) = false := by simp [h_xhi]
    rw [h_xhi_eq] at *
    simp only [Bool.false_eq_true, if_false] at *
    steps [Lampe.Stdlib.Field.Bn254.assert_lt_intro (p := p)]
    rename_i _ hv_eq ha_eq hb_eq hab vret hret
    have ha_xhi : a = xhi := by rw [ha_eq, hv_eq]; rfl
    have hb_phi : b = ((phi : Nat) : Fp p) := by rw [hb_eq, hv_eq]; rfl
    have h_xhi_val_lt : xhi.val < phi := by
      have := hab
      rw [ha_xhi, hb_phi] at this
      simpa [hphi_val] using this
    have hassert_eq : scalar = xlo + ((Lampe.pow128 : Nat) : Fp p) * xhi := by
      simpa [decide_eq_true_eq] using hassert
    have hret_mk : vret = Scalar.mk xlo xhi := by
      simpa [Scalar.mk, HList.toTuple] using hret
    simp only [SLP.exists_pure]
    sl
    refine ⟨xhi, hret_mk, ?_, Or.inr h_xhi_val_lt⟩
    show scalar = xlo + ((Lampe.pow128 : Nat) : Fp p) * xhi
    exact hassert_eq

/-! ### `pedersen_commitment_with_separator` substantive spec -/

/-- Relation enforced by the body of `from_field_unsafe` on its output
scalar `s` for input `x`: the limb relation `x = lo + 2^128 * hi` and
the canonical-range disjunction enforced by the `assert_lt`. Used as
the per-slot loop invariant of the scalar-buffer loops below. -/
private def fromFieldUnsafeRel {p} [Lampe.Crypto.Bn254.Prime p]
    (x : Fp p) (s : Scalar.denote p) : Prop :=
  x = s.1 + ((pow128 : Nat) : Fp p) * s.2.1
    ∧ ((s.2.1 = ((phi : Nat) : Fp p) ∧ s.1.val < plo)
        ∨ s.2.1.val < phi)

/-- Everything the Pedersen wrappers learn about one `from_field_unsafe`
output scalar `s` for input `x`: `fromFieldUnsafeRel` plus the MSM
gadget's limb-range canonicality. This is the per-slot witness carried
by the existential `_spec` intermediates and consumed (via
`Scalar.canonicalDecomp_unique`) by the `_spec_canonical` proofs. -/
private def FromFieldUnsafeWitness {p} [Lampe.Crypto.Bn254.Prime p]
    (x : Fp p) (s : Scalar.denote p) : Prop :=
  fromFieldUnsafeRel x s ∧ Scalar.Canonical s

/-- Existential intermediate for
`std::hash::pedersen_commitment_with_separator`, consumed only by the
public `_spec_canonical` theorem below. The witness `Ss` records the
per-slot `from_field_unsafe` outputs, each satisfying
`FromFieldUnsafeWitness`. -/
private theorem pedersen_commitment_with_separator_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_commitment_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = encodeCurvePoint
                (∑ i, Scalar.valueNat (Ss.get i)
                    • pedersenGenerator (p := p)
                        defaultDomainBytes
                        (separator.toNat + i.val))
          ∧ ∀ i, FromFieldUnsafeWitness (input.get i) (Ss.get i)) := by
  let Ps : List.Vector (affineCurve p).Point N.toNat :=
    List.Vector.ofFn (fun i => pedersenGenerator (p := p)
      defaultDomainBytes (separator.toNat + i.val))
  have h_gen : ∀ i,
      encodeCurvePoint (Ps.get i) =
        pedersenGeneratorPoint p defaultDomainBytes
          (separator.toNat + i.val) := by
    intro i
    simp [Ps, List.Vector.get_ofFn, pedersenGeneratorPoint_eq]
  enter_decl
  steps
  loop_inv nat fun (i : Nat) _ _ =>
    ∃∃ v : Tp.denote p (Scalar.type.array N),
      [points ↦ ⟨Scalar.type.array N, v⟩] ⋆
        ⟦∀ (j : Nat) (hj : j < i) (hjN : j < N.toNat),
          fromFieldUnsafeRel (input.get ⟨j, hjN⟩) (v.get ⟨j, hjN⟩)⟧
  · sl
    intro j hj _
    simp at hj
  · simp
  · intro i hlo hhi
    steps [from_field_unsafe_spec (p := p)]
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.CastTp.cast,
      BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT,
      Lens.modify, Access.modify, Lens.get, Option.bind_eq_bind, Option.bind_some,
      dite_true, Option.get_some]
    rename_i v_prev hPrefix hCastLt xlo xhi _hModSome _ hRes
    obtain ⟨_h_mk, h_scalar, h_range⟩ := hRes
    intro j hj hjN
    by_cases h_eq : j = i
    · subst h_eq
      unfold fromFieldUnsafeRel
      have hSetGet :
          (List.Vector.set v_prev ⟨j, hCastLt⟩ (Scalar.mk xlo xhi)).get ⟨j, hjN⟩ =
            Scalar.mk xlo xhi := by
        rw [List.Vector.get_set_same]
      rw [hSetGet]
      simp only [Scalar.mk]
      refine ⟨h_scalar, h_range⟩
    · have hjlt : j < i := by omega
      have hne : (⟨i, hCastLt⟩ : Fin N.toNat) ≠ ⟨j, hjN⟩ := by
        intro hh
        have : i = j := by exact (Fin.mk.injEq _ _ _ _).mp hh
        exact h_eq this.symm
      have hSetGet :
          (List.Vector.set v_prev ⟨i, hCastLt⟩ (Scalar.mk xlo xhi)).get ⟨j, hjN⟩ =
            v_prev.get ⟨j, hjN⟩ :=
        List.Vector.get_set_of_ne (v := v_prev) hne (Scalar.mk xlo xhi)
      unfold fromFieldUnsafeRel
      rw [hSetGet]
      exact hPrefix j hjlt hjN
  steps [derive_generators_spec (p := p) (N := N) (M := (24 : U 32))
    (startIdx := separator)]
  rename_i _hLo vFinal hInv _strLen hGen
  -- Bridge: bytesToList (strAsBytes "DEFAULT_DOMAIN_SEPARATOR") = defaultDomainBytes.
  have hDomain :
      bytesToList (p := p) (M := (24 : U 32))
        (Lampe.NoirStr.of "DEFAULT_DOMAIN_SEPARATOR").bytes = defaultDomainBytes :=
    strAsBytes_default_domain_eq (p := p)
  rw [hDomain] at hGen
  have h_enc :
      generators.toList = Ps.toList.map encodeCurvePoint := by
    rw [hGen]
    exact derivePedersenGenerators_h_enc (p := p) (n := N.toNat)
      (domain := defaultDomainBytes) (start := separator.toNat) (Ps := Ps) h_gen
  steps [multi_scalar_mul_combined_spec (p := p) (N := N)
    (points := generators) (scalars := vFinal) (Ps := Ps) h_enc]
  case v => exact vFinal
  rename_i hMsm
  obtain ⟨hCanon, hSum⟩ := hMsm
  refine ⟨?_, ?_⟩
  ·
    have hPs_get : ∀ i : Fin N.toNat,
        Ps.get i = pedersenGenerator (p := p)
          defaultDomainBytes (separator.toNat + i.val) := by
      intro i
      simp [Ps, List.Vector.get_ofFn]
    simp only [hPs_get] at hSum
    exact hSum
  ·
    intro i
    exact ⟨hInv i.val i.isLt i.isLt, hCanon i⟩

/-- Deterministic closed-form of `pedersen_commitment_with_separator_spec`:
the result is the pure `pedersenCommitment` (the
MSM with each input collapsed to its canonical limb decomposition). -/
theorem pedersen_commitment_with_separator_spec_canonical {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_commitment_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        r = pedersenCommitment p defaultDomainBytes input separator.toNat) := by
  apply STHoare.consequence (h_pre_conseq := SLP.entails_self) ?_
    (pedersen_commitment_with_separator_spec (p := p) (N := N)
      (input := input) (separator := separator))
  intro r
  rw [← SLP.star_exists]
  apply SLP.exists_intro_l
  intro Ss
  apply SLP.pure_left
  rintro ⟨h_eq, h_wit⟩
  have h_unique : ∀ i, Ss.get i = Scalar.canonicalDecomp (input.get i) := fun i =>
    Scalar.canonicalDecomp_unique (h_wit i).2 (h_wit i).1.2 (h_wit i).1.1
  have hSumEq :
      (∑ i : Fin N.toNat,
        Scalar.valueNat (Ss.get i)
        • pedersenGenerator (p := p)
            defaultDomainBytes (separator.toNat + i.val)) =
      ∑ i : Fin N.toNat,
        Scalar.valueNat
            (Scalar.canonicalDecomp (input.get i))
        • pedersenGenerator (p := p)
            defaultDomainBytes (separator.toNat + i.val) :=
    Finset.sum_congr rfl (fun i _ => by rw [h_unique i])
  apply SLP.pure_right
  · rw [pedersenCommitment_eq, h_eq, hSumEq]
  · exact SLP.entails_top

/-! ### `pedersen_hash_with_separator` spec -/

set_option maxHeartbeats 300000 in
/-- Existential intermediate for `std::hash::pedersen_hash_with_separator`,
consumed only by the public `_spec_canonical` theorem below. The body adds
a length-slot scalar `(N, 0)` at position `N`, derives the corresponding
generator from `"pedersen_hash_length"` (with `starting_index = 0`),
and returns the x-coordinate of the singleton MSM result. The witness
`Ss` records the per-slot `from_field_unsafe` outputs, each satisfying
`FromFieldUnsafeWitness`. -/
private theorem pedersen_hash_with_separator_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_hash_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = pointX
                (encodeCurvePoint
                  ((∑ i : Fin N.toNat,
                      Scalar.valueNat (Ss.get i)
                      • pedersenGenerator (p := p)
                          defaultDomainBytes (separator.toNat + i.val))
                   + (N.toNat : ℕ) • pedersenGenerator (p := p)
                          pedersenHashLengthBytes 0))
          ∧ ∀ i, FromFieldUnsafeWitness (input.get i) (Ss.get i)) := by
  let Ps : List.Vector (affineCurve p).Point (N.toNat + 1) :=
    List.Vector.ofFn (fun i : Fin (N.toNat + 1) =>
      if h : i.val < N.toNat then
        pedersenGenerator (p := p) defaultDomainBytes
          (separator.toNat + i.val)
      else
        pedersenGenerator (p := p) pedersenHashLengthBytes 0)
  have h_gen : ∀ (i : Fin N.toNat),
      encodeCurvePoint
        (Ps.get ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
        pedersenGeneratorPoint p defaultDomainBytes
          (separator.toNat + i.val) := by
    intro i
    simp [Ps, List.Vector.get_ofFn, i.isLt,
      pedersenGeneratorPoint_eq]
  have h_len_gen :
      encodeCurvePoint
        (Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩) =
        pedersenGeneratorPoint p pedersenHashLengthBytes 0 := by
    simp [Ps, List.Vector.get_ofFn,
      pedersenGeneratorPoint_eq]
  have hPs_get_lt : ∀ (i : Fin N.toNat),
      Ps.get ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ =
        pedersenGenerator (p := p)
          defaultDomainBytes (separator.toNat + i.val) := by
    intro i
    simp [Ps, List.Vector.get_ofFn, i.isLt]
  have hPs_get_last :
      Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩ =
        pedersenGenerator (p := p)
          pedersenHashLengthBytes 0 := by
    simp [Ps, List.Vector.get_ofFn]
  enter_decl
  steps [point_at_infinity_spec (p := p),
    derive_generators_spec (p := p) (N := N) (M := (24 : U 32))
      (startIdx := separator)]
  rename_i _hu domain_generators hDom
  loop_inv nat fun (i : Nat) _ _ =>
    ∃∃ (s : Tp.denote p (Scalar.type.array (N + 1)))
       (g : Tp.denote p (Point.type.array (N + 1))),
      [scalars ↦ ⟨Scalar.type.array (N + 1), s⟩] ⋆
      [generators ↦ ⟨Point.type.array (N + 1), g⟩] ⋆
        ⟦∀ (j : Nat) (hj : j < i) (hjN : j < N.toNat)
            (hjN1 : j < (N + 1).toNat),
          fromFieldUnsafeRel (input.get ⟨j, hjN⟩) (s.get ⟨j, hjN1⟩)
          ∧ g.get ⟨j, hjN1⟩ = domain_generators.get ⟨j, hjN⟩⟧
  · sl
    sl
    intro j hj _ _
    simp at hj
  · simp
  · intro i hlo hhi
    steps [from_field_unsafe_spec (p := p)]
    sl
    rename_i s_prev g_prev hPrefix hCast1 xlo xhi hRes hModS hCast2 hModG _
    obtain ⟨h_mk, h_scalar, h_range⟩ := hRes
    intro j hj hjN hjN1
    simp_all only [Lens.modify, Access.modify, Lens.get,
      Option.bind_eq_bind, Option.bind_some,
      Builtin.CastTp.cast, BitVec.toNat_intCast, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
    have hiN1 : i < (BitVec.toNat N + 1) % 4294967296 := by
      by_contra hcontra
      simp [Nat.not_lt.mpr (Nat.le_of_not_lt hcontra)] at hModS
    have hGoalBdd : i < (BitVec.add N 1).toNat := hiN1
    simp only [dif_pos hGoalBdd, Option.bind_some, Option.get_some] at *
    by_cases h_eq : j = i
    · subst h_eq
      refine ⟨?_, ?_⟩
      · rw [List.Vector.get_set_same]
        simp only [Scalar.mk]
        exact ⟨h_scalar, h_range⟩
      · rw [List.Vector.get_set_same]
    · have hjlt : j < i := by omega
      have hne : (⟨i, hGoalBdd⟩ : Fin (BitVec.add N 1).toNat) ≠ ⟨j, hjN1⟩ := by
        intro hh; exact h_eq ((Fin.mk.injEq _ _ _ _).mp hh).symm
      rw [List.Vector.get_set_of_ne (v := s_prev) hne,
        List.Vector.get_set_of_ne (v := g_prev) hne]
      exact hPrefix j hjlt hjN hjN1
  steps [derive_generators_spec (p := p) (N := (1 : U 32)) (M := (20 : U 32))
    (startIdx := (0 : U 32))]
  rename_i _hLo sFinal gFinal hInv hModSN _strLen hLenGen hLgBdd hModGN
  simp only [Lens.modify, Access.modify, Lens.get,
    Option.bind_eq_bind, Option.bind_some] at hModSN hModGN ⊢
  -- Extract `N.toNat < (BitVec.add N 1).toNat` from hModSN.
  have hNlt_dite : N.toNat < (BitVec.toNat N + 1) % 4294967296 := by
    by_contra hcontra
    have hge : (BitVec.toNat N + 1) % 4294967296 ≤ N.toNat := Nat.le_of_not_lt hcontra
    simp [Nat.not_lt.mpr hge] at hModSN
  have hNlt : N.toNat < (BitVec.add N 1).toNat := hNlt_dite
  simp only [dif_pos hNlt, Option.bind_some, Option.get_some] at hModSN hModGN ⊢
  -- The constraint `N.toNat < (N+1).toNat` together with the wrap-around behaviour
  -- of `BitVec.add` forces `N.toNat + 1 < 2^32`.
  have hN1_eq : (N + 1).toNat = N.toNat + 1 := by
    -- (N + 1).toNat = (N.toNat + 1) % 2^32. The loop-bound hypothesis
    -- `hNlt_dite : N.toNat < (N.toNat + 1) % 2^32` rules out wraparound.
    have hadd : (N + 1).toNat = (N.toNat + 1) % 4294967296 := by
      show BitVec.toNat (N + 1) = _
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hNbnd : N.toNat < 4294967296 := N.isLt
    have hbnd : N.toNat + 1 < 4294967296 := by
      rcases Nat.lt_or_ge (N.toNat + 1) 4294967296 with h | h
      · exact h
      · exfalso
        have : N.toNat + 1 = 4294967296 := by omega
        rw [this, Nat.mod_self] at hNlt_dite
        omega
    rw [hadd, Nat.mod_eq_of_lt hbnd]
  let Ss : List.Vector (Scalar.denote p) N.toNat :=
    ⟨List.ofFn fun j : Fin N.toNat => sFinal.get ⟨j.val, by rw [hN1_eq]; omega⟩,
      by simp⟩
  have hSs_get : ∀ (i : Fin N.toNat),
      Ss.get i = sFinal.get ⟨i.val, by rw [hN1_eq]; omega⟩ := by
    intro i
    rw [List.Vector.get_eq_get_toList]
    show (List.ofFn _).get _ = _
    simp
  set lenScalar : Tp.denote p Scalar.type :=
    HList.toTuple p h![(Builtin.CastTp.cast N : Fp p), (Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)]
      (some «std-1.0.0-beta.25::embedded_curve_ops::EmbeddedCurveScalar».name) with hLenScalar_def
  set lenGen : Tp.denote p Point.type :=
    length_generator.get ⟨BitVec.toNat ↑(0 : U 32), hLgBdd⟩ with hLenGen_def
  set sFull : Tp.denote p (Scalar.type.array (N + 1)) :=
    sFinal.set ⟨N.toNat, hNlt⟩ lenScalar with hsFull_def
  set gFull : Tp.denote p (Point.type.array (N + 1)) :=
    gFinal.set ⟨N.toNat, hNlt⟩ lenGen with hgFull_def
  have hsFull_get : ∀ (i : Fin N.toNat) (hi : i.val < (N + 1).toNat),
      sFull.get ⟨i.val, hi⟩ = sFinal.get ⟨i.val, by rw [hN1_eq]; omega⟩ := by
    intro i hi
    show (sFinal.set ⟨N.toNat, hNlt⟩ lenScalar).get _ = _
    rw [List.Vector.get_set_of_ne]
    intro hh
    have h_eq : N.toNat = i.val := (Fin.mk.injEq _ _ _ _).mp hh
    have := i.isLt; omega
  have hLenScalar_value : Scalar.valueNat lenScalar = N.toNat := by
    show (Scalar.lo lenScalar).val
      + pow128 *
        (Scalar.hi lenScalar).val = N.toNat
    show ((Builtin.CastTp.cast N : Fp p)).val
      + pow128 *
        ((Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)).val = N.toNat
    have hcast_zero : ((Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)).val = 0 := by
      show ((0 : Fp p)).val = 0
      simp
    rw [hcast_zero, Nat.mul_zero, Nat.add_zero]
    show ((Builtin.CastTp.cast N : Fp p)).val = N.toNat
    show ((N.toNat : Fp p)).val = N.toNat
    rw [ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have hNbnd : N.toNat < 2^32 := N.isLt
    have hp128 : (2^32 : Nat) < Lampe.pow128 := by decide
    have hpprime := Lampe.Crypto.Bn254.pow128_lt_prime (p := p)
    omega
  set Ps_full : List.Vector (affineCurve p).Point (N + 1).toNat :=
    ⟨Ps.toList, by rw [List.Vector.toList_length]; exact hN1_eq.symm⟩ with hPs_full_def
  have hPs_full_get : ∀ (k : Nat) (hk : k < (N + 1).toNat) (hk' : k < N.toNat + 1),
      Ps_full.get ⟨k, hk⟩ = Ps.get ⟨k, hk'⟩ := by
    intro k hk hk'
    simp [Ps_full, List.Vector.get, List.Vector.toList]
  have h_enc : gFull.toList = Ps_full.toList.map encodeCurvePoint := by
    rw [← List.Vector.toList_map]
    apply congrArg List.Vector.toList
    apply List.Vector.ext
    rintro ⟨k, hk⟩
    have hkSucc : k < N.toNat + 1 := by omega
    by_cases h_isN : k = N.toNat
    ·
      have hsetget : gFull.get ⟨k, hk⟩ = lenGen := by
        show (gFinal.set ⟨N.toNat, hNlt⟩ lenGen).get ⟨k, hk⟩ = lenGen
        have : (⟨k, hk⟩ : Fin (N + 1).toNat) = ⟨N.toNat, hNlt⟩ := by
          apply Fin.ext; exact h_isN
        rw [this, List.Vector.get_set_same]
      rw [hsetget]
      have hlg : lenGen =
          pedersenGeneratorPoint p pedersenHashLengthBytes 0 := by
        show length_generator.get _ = _
        rw [hLenGen]
        simp only [strAsBytes_hash_length_eq (p := p)]
        show (derivePedersenGenerators p pedersenHashLengthBytes 0 1).get
          ⟨0, by decide⟩ = _
        rw [derivePedersenGenerators_get]
        simp
      rw [hlg]
      symm
      calc (Ps_full.map encodeCurvePoint).get ⟨k, hk⟩
          = encodeCurvePoint (Ps_full.get ⟨k, hk⟩) := by
            simp [List.Vector.get_map]
        _ = encodeCurvePoint (Ps.get ⟨k, hkSucc⟩) := by
            rw [hPs_full_get k hk hkSucc]
        _ = encodeCurvePoint
              (Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩) := by
            congr 1; apply congrArg; apply Fin.ext; exact h_isN
        _ = _ := h_len_gen
    · have hkN : k < N.toNat := by omega
      have hsetget : gFull.get ⟨k, hk⟩ = gFinal.get ⟨k, hk⟩ := by
        show (gFinal.set ⟨N.toNat, hNlt⟩ lenGen).get ⟨k, hk⟩ = gFinal.get ⟨k, hk⟩
        rw [List.Vector.get_set_of_ne]
        intro hh
        exact h_isN ((Fin.mk.injEq _ _ _ _).mp hh).symm
      rw [hsetget, (hInv k hkN hkN hk).2, hDom]
      symm
      calc (Ps_full.map encodeCurvePoint).get ⟨k, hk⟩
          = encodeCurvePoint (Ps_full.get ⟨k, hk⟩) := by
            simp [List.Vector.get_map]
        _ = encodeCurvePoint (Ps.get ⟨k, hkSucc⟩) := by
            rw [hPs_full_get k hk hkSucc]
        _ = pedersenGeneratorPoint p defaultDomainBytes
              (BitVec.toNat separator + (⟨k, hkN⟩ : Fin N.toNat).val) := h_gen ⟨k, hkN⟩
        _ = (derivePedersenGenerators p defaultDomainBytes
              (BitVec.toNat separator) N.toNat).get ⟨k, hkN⟩ := by
            rw [derivePedersenGenerators_get]
  have hGetEnc : ∀ i : Fin (N + 1).toNat, gFull.get i =
      encodeCurvePoint (Ps_full.get i) := by
    intro i
    have hi_gFull : i.val < gFull.toList.length := by simp [List.Vector.toList_length]
    have hi_Ps : i.val < Ps_full.toList.length := by simp [List.Vector.toList_length]
    have hgFull_get_eq : gFull.get i = gFull.toList[i.val]'hi_gFull := by
      rw [List.Vector.get_eq_get_toList]; rfl
    have hPs_get_eq : Ps_full.get i = Ps_full.toList[i.val]'hi_Ps := by
      rw [List.Vector.get_eq_get_toList]; rfl
    rw [hgFull_get_eq, hPs_get_eq]
    have h' := congrArg (fun l : List _ => l[i.val]?) h_enc
    simp only at h'
    rw [List.getElem?_eq_getElem hi_gFull,
      List.getElem?_eq_getElem (by simp)] at h'
    simp only [Option.some.injEq] at h'
    rw [h']
    simp [List.getElem_map]
  have hOnCurve : ∀ i : Fin (N + 1).toNat,
      (curvePoint? (gFull.get i)).isSome = true := by
    intro i
    rw [hGetEnc i]
    simp
  have hSumEq :
      (∑ i : Fin (N + 1).toNat,
        Scalar.valueNat (sFull.get i)
        • (curvePoint? (gFull.get i)).get (hOnCurve i)) =
      ∑ i : Fin (N + 1).toNat,
        Scalar.valueNat (sFull.get i) • Ps_full.get i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hCp : curvePoint? (gFull.get i) = some (Ps_full.get i) := by
      rw [hGetEnc i]; simp
    rw [Option.get_of_eq_some _ hCp]
  steps [Lampe.Stdlib.EmbeddedCurveOps.multi_scalar_mul_builtin_combined_spec
    (p := p) (N := N + 1) (points := gFull) (scalars := sFull) hOnCurve]
  case v => exact Ss
  rcases (‹(∀ _, _) ∧ _› :
      (∀ i, Scalar.Canonical (sFull.get i)) ∧ _)
    with ⟨hCanonFull, hSumRes⟩
  refine ⟨?_, ?_⟩
  ·
    subst hSumRes
    subst_vars
    show pointX
        (encodeCurvePoint _) = _
    congr 1
    congr 1
    show (∑ i : Fin (N + 1).toNat,
        Scalar.valueNat (sFull.get i)
        • (curvePoint? (gFull.get i)).get (hOnCurve i)) = _
    rw [hSumEq]
    have hSumSplit :
        (∑ i : Fin (N + 1).toNat,
          Scalar.valueNat (sFull.get i) • Ps_full.get i) =
        ∑ j : Fin (N.toNat + 1),
          Scalar.valueNat
              (sFull.get ⟨j.val, by rw [hN1_eq]; exact j.isLt⟩) •
            Ps_full.get ⟨j.val, by rw [hN1_eq]; exact j.isLt⟩ := by
      apply Finset.sum_equiv (finCongr hN1_eq)
        (fun _ => Iff.intro (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _))
        (fun _ _ => by congr 2)
    rw [hSumSplit]
    rw [Fin.sum_univ_castSucc]
    congr 1
    ·
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hi_N1 : i.val < (N + 1).toNat := by rw [hN1_eq]; omega
      have hcs_idx : (⟨(i.castSucc).val, by rw [hN1_eq]; exact (i.castSucc).isLt⟩ :
          Fin (N + 1).toNat) = ⟨i.val, hi_N1⟩ := Fin.ext rfl
      rw [hcs_idx, hsFull_get i hi_N1,
          hPs_full_get i.val hi_N1 (Nat.lt_succ_of_lt i.isLt),
          hPs_get_lt i, hSs_get i]
    ·
      have hN_lt_N1 : N.toNat < (N + 1).toNat := hNlt
      have hsFull_last : sFull.get ⟨N.toNat, hN_lt_N1⟩ = lenScalar := by
        show (sFinal.set ⟨N.toNat, hNlt⟩ lenScalar).get _ = _
        rw [List.Vector.get_set_same]
      have hPsFull_last : Ps_full.get ⟨N.toNat, hN_lt_N1⟩ =
          Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩ :=
        hPs_full_get N.toNat _ (Nat.lt_succ_self _)
      have hidx : (⟨(Fin.last N.toNat).val,
            by rw [hN1_eq]; exact (Fin.last N.toNat).isLt⟩ :
          Fin (N + 1).toNat) = ⟨N.toNat, hN_lt_N1⟩ := Fin.ext rfl
      rw [hidx, hsFull_last, hPsFull_last, hPs_get_last, hLenScalar_value]
  ·
    intro i
    have hi_N1 : i.val < (N + 1).toNat := by rw [hN1_eq]; omega
    refine ⟨?_, ?_⟩
    ·
      rw [hSs_get i]
      exact (hInv i.val i.isLt i.isLt (by omega)).1
    ·
      rw [hSs_get i, ← hsFull_get i hi_N1]
      exact hCanonFull ⟨i.val, hi_N1⟩

/-- Deterministic closed-form of `pedersen_hash_with_separator_spec`:
the result is the pure `pedersenHash` (the
x-coordinate of the canonical-decomposition MSM, plus the length-slot
term `N • pedersenGenerator pedersenHashLengthBytes 0`). -/
theorem pedersen_hash_with_separator_spec_canonical {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_hash_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        r = pedersenHash p defaultDomainBytes input separator.toNat) := by
  apply STHoare.consequence (h_pre_conseq := SLP.entails_self) ?_
    (pedersen_hash_with_separator_spec (p := p) (N := N)
      (input := input) (separator := separator))
  intro r
  rw [← SLP.star_exists]
  apply SLP.exists_intro_l
  intro Ss
  apply SLP.pure_left
  rintro ⟨h_eq, h_wit⟩
  have h_unique : ∀ i, Ss.get i = Scalar.canonicalDecomp (input.get i) := fun i =>
    Scalar.canonicalDecomp_unique (h_wit i).2 (h_wit i).1.2 (h_wit i).1.1
  have hSumEq :
      (∑ i : Fin N.toNat,
        Scalar.valueNat (Ss.get i)
        • pedersenGenerator (p := p)
            defaultDomainBytes (separator.toNat + i.val)) =
      ∑ i : Fin N.toNat,
        Scalar.valueNat
            (Scalar.canonicalDecomp (input.get i))
        • pedersenGenerator (p := p)
            defaultDomainBytes (separator.toNat + i.val) :=
    Finset.sum_congr rfl (fun i _ => by rw [h_unique i])
  apply SLP.pure_right
  · rw [pedersenHash_eq, h_eq, hSumEq]
  · exact SLP.entails_top

/-! ### `pedersen_commitment` wrapper spec -/

theorem pedersen_commitment_spec_canonical {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_commitment».call h![N] h![input])
      (fun r =>
        r = pedersenCommitment p defaultDomainBytes input 0) := by
  enter_decl
  steps [pedersen_commitment_with_separator_spec_canonical (p := p) (N := N)
    (input := input) (separator := (0 : U 32))]
  rename_i hPost
  simpa using hPost

/-! ### `pedersen_hash` wrapper spec -/

theorem pedersen_hash_spec_canonical {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.25::hash::pedersen_hash».call h![N] h![input])
      (fun r =>
        r = pedersenHash p defaultDomainBytes input 0) := by
  enter_decl
  steps [pedersen_hash_with_separator_spec_canonical (p := p) (N := N)
    (input := input) (separator := (0 : U 32))]
  rename_i hPost
  simpa using hPost

end Lampe.Stdlib.Hash.Pedersen
