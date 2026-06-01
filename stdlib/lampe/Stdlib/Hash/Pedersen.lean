import «std-1.0.0-beta.14».Extracted
import Lampe
import Stdlib.EmbeddedCurveOps
import Stdlib.Field.Bn254
import Stdlib.Hash.Mod

namespace Lampe.Stdlib.Hash.Pedersen

open «std-1.0.0-beta.14»
open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen
open Lampe.Stdlib.EmbeddedCurveOps

/-- Local alias for the BN254 high limb (`PHI` field constant) as a `Nat`. -/
private abbrev phi : Nat := Lampe.Crypto.Bn254.phi

/-- Local alias for the BN254 low limb (`PLO` field constant) as a `Nat`. -/
private abbrev plo : Nat := Lampe.Crypto.Bn254.plo

/-- Local alias for `2^128` as a `Nat`. -/
private abbrev pow128 : Nat := Lampe.Crypto.Bn254.pow128

/-!
# Stdlib specs for `std::hash` Pedersen wrappers

This module proves STHoare triples for all 5 Noir stdlib functions
that sit on top of the `derive_pedersen_generators` foreign builtin:

- `derive_generators_spec` — pass-through wrapper around the builtin
- `from_field_unsafe_spec` — ∃-limbs decomposition `scalar = xlo + 2^128 * xhi`
- `pedersen_commitment_with_separator_spec` — substantive MSM spec
- `pedersen_hash_with_separator_spec` — substantive MSM-then-`pointX` spec
- `pedersen_commitment_spec`, `pedersen_hash_spec` — wrappers at `separator = 0`

The two substantive specs (and their wrappers) express their result
directly in terms of `pedersenGenerator`,
the concrete BN254-scalar generator definition (BLAKE3 hash-to-curve +
Tonelli-Shanks). They expose the per-slot `from_field_unsafe`
decomposition as an existential `Ss` witness, carrying the limb
relation and canonical-range disjunction that `from_field_unsafe_spec`
produces.
-/

/-! ### Domain-separator strings -/

/-- ASCII byte vector for the literal `"DEFAULT_DOMAIN_SEPARATOR"`
(24 bytes). Used by `pedersen_commitment_with_separator` and
`pedersen_hash_with_separator`. -/
def defaultDomainBytes : List Nat :=
  [68, 69, 70, 65, 85, 76, 84, 95,    -- "DEFAULT_"
   68, 79, 77, 65, 73, 78, 95,         -- "DOMAIN_"
   83, 69, 80, 65, 82, 65, 84, 79, 82] -- "SEPARATOR"

/-- ASCII byte vector for the literal `"pedersen_hash_length"`
(20 bytes). Used by `pedersen_hash_with_separator` for the
length-slot generator. -/
def pedersenHashLengthBytes : List Nat :=
  [112, 101, 100, 101, 114, 115, 101, 110, 95,  -- "pedersen_"
   104, 97, 115, 104, 95,                       -- "hash_"
   108, 101, 110, 103, 116, 104]                 -- "length"

/-! ### `derive_pedersen_generators` builtin spec -/

/-- Direct spec for the `derivePedersenGenerators` foreign builtin
descriptor. -/
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

/-- Spec for `std::hash::derive_generators`. The body is
`assertConstant(domain_bytes); assertConstant(starting_index);
derivePedersenGenerators(domain_bytes, starting_index)`.

The two `assertConstant` calls are runtime hints, modeled as
no-ops; the wrapper is therefore extensionally equal to the
underlying foreign builtin. -/
theorem derive_generators_spec {p} {N M : U 32}
    {domainBytes : Tp.denote p ((Tp.u 8).array M)}
    {startIdx : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::derive_generators».call h![N, M]
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

/-- The bytes of the literal `"DEFAULT_DOMAIN_SEPARATOR"` (as produced
by `Lampe.NoirStr.of`) coincide, under `bytesToList`, with the
`defaultDomainBytes` constant declared above. Plumbing lemma used by
the substantive `pedersen_commitment_with_separator` / `pedersen_hash_with_separator`
specs to bridge between the syntactic `strAsBytes` output and the
opaque `pedersenGeneratorPoint` domain key. -/
private lemma strAsBytes_default_domain_eq {p} :
    bytesToList (p := p) (M := (24 : U 32))
      (Lampe.NoirStr.of "DEFAULT_DOMAIN_SEPARATOR") = defaultDomainBytes := by
  rfl

/-- The bytes of the literal `"pedersen_hash_length"` (as produced by
`Lampe.NoirStr.of`) coincide, under `bytesToList`, with the
`pedersenHashLengthBytes` constant declared above. Plumbing lemma
used by the substantive `pedersen_hash_with_separator` spec for the
length-slot generator. -/
private lemma strAsBytes_hash_length_eq {p} :
    bytesToList (p := p) (M := (20 : U 32))
      (Lampe.NoirStr.of "pedersen_hash_length") = pedersenHashLengthBytes := by
  rfl

/-- Pointwise-to-`toList` bridge for `derivePedersenGenerators`. Given
a Mathlib-point vector `Ps` whose `i`-th element encodes (via
`encodeCurvePoint`) to the opaque generator
`pedersenGeneratorPoint p domain (start + i)`, the `toList` of the
derived generator vector equals `Ps.toList.map encodeCurvePoint`.
This is exactly the `h_enc` hypothesis shape required by
`multi_scalar_mul_spec`. -/
private lemma derivePedersenGenerators_h_enc {p : Prime} {N : U 32}
    {domain : List Nat} {start : Nat}
    {Ps : List.Vector (affineCurve p).Point N.toNat}
    (h_gen : ∀ i,
      encodeCurvePoint (Ps.get i) =
        pedersenGeneratorPoint p domain (start + i.val)) :
    (derivePedersenGenerators p domain start N.toNat).toList =
      Ps.toList.map encodeCurvePoint := by
  rw [← List.Vector.toList_map]
  apply congrArg List.Vector.toList
  apply List.Vector.ext
  intro i
  rw [derivePedersenGenerators_get,
    List.Vector.get_map, ← h_gen i]

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
below. Callers that need the per-limb bound (e.g. for
`Scalar.Canonical`) should use the constrained
`EmbeddedCurveScalar::from_field` wrapper and its
`scalar_from_field_spec`. -/
theorem from_field_unsafe_spec {p} [Lampe.Crypto.Bn254.Prime p]
    {scalar : Fp p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::from_field_unsafe».call h![] h![scalar])
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
      have : (plo : Nat) < Lampe.Crypto.Bn254.pow128 := by decide
      linarith [this, Lampe.Crypto.Bn254.pow128_lt_prime (p := p)]
    simpa using (ZMod.val_natCast_of_lt hplo_lt)
  have hphi_val : ((phi : Nat) : Fp p).val = phi := by
    have hphi_lt : (phi : Nat) < p.natVal := by
      have : (phi : Nat) < Lampe.Crypto.Bn254.pow128 := by decide
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
    have hassert_eq : scalar = xlo + ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * xhi := by
      simpa [decide_eq_true_eq] using hassert
    have hret_mk : vret = Scalar.mk xlo xhi := by
      simpa [Scalar.mk, HList.toTuple] using hret
    simp only [SLP.exists_pure]
    sl
    refine ⟨xhi, hret_mk, ?_, Or.inr h_xhi_val_lt⟩
    show scalar = xlo + ((Lampe.Crypto.Bn254.pow128 : Nat) : Fp p) * xhi
    exact hassert_eq

/-! ### `pedersen_commitment_with_separator` substantive spec -/

/-- Per-slot well-formedness predicate for the scalar buffer the
`pedersen_commitment_with_separator` loop builds. Each slot `j` is
the `from_field_unsafe` output for `input.get j`: it carries the
limb relation `input[j] = lo + 2^128 * hi` and the canonical-range
disjunction enforced by the `assert_lt`. -/
private def fromFieldUnsafeRel {p} [Lampe.Crypto.Bn254.Prime p]
    (input : Tp.denote p (Tp.field.array N))
    (v : Tp.denote p (Scalar.type.array N))
    (j : Nat) (hj : j < N.toNat) : Prop :=
  (input.get ⟨j, hj⟩) = (v.get ⟨j, hj⟩).1
      + ((pow128 : Nat) : Fp p) * (v.get ⟨j, hj⟩).2.1
    ∧ (((v.get ⟨j, hj⟩).2.1 = ((phi : Nat) : Fp p)
          ∧ (v.get ⟨j, hj⟩).1.val < plo)
        ∨ (v.get ⟨j, hj⟩).2.1.val < phi)

theorem pedersen_commitment_with_separator_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_commitment_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = encodeCurvePoint
                (∑ i, scalarValueNat (Ss.get i)
                    • pedersenGenerator (p := p)
                        defaultDomainBytes
                        (separator.toNat + i.val))
          ∧ (∀ i, (input.get i) = (Ss.get i).1 + ((pow128 : Nat) : Fp p) * (Ss.get i).2.1)
          ∧ (∀ i, ((Ss.get i).2.1 = ((phi : Nat) : Fp p) ∧ (Ss.get i).1.val < plo)
                  ∨ (Ss.get i).2.1.val < phi)) := by
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
          fromFieldUnsafeRel (N := N) input v j hjN⟧
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
    exact derivePedersenGenerators_h_enc (p := p) (N := N) (domain := defaultDomainBytes)
      (start := separator.toNat) (Ps := Ps) h_gen
  -- Use multi_scalar_mul_spec to finish.
  steps [multi_scalar_mul_spec (p := p) (N := N)
    (points := generators) (scalars := vFinal) (Ps := Ps) h_enc]
  rename_i hSum
  case v => exact vFinal
  refine ⟨?_, ?_, ?_⟩
  ·
    simp only [Scalar.valueNat_eq_scalarValueNat] at hSum
    have hPs_get : ∀ i : Fin N.toNat,
        Ps.get i = pedersenGenerator (p := p)
          defaultDomainBytes (separator.toNat + i.val) := by
      intro i
      simp [Ps, List.Vector.get_ofFn]
    simp only [hPs_get] at hSum
    exact hSum
  ·
    intro i
    exact (hInv i.val i.isLt i.isLt).1
  ·
    intro i
    exact (hInv i.val i.isLt i.isLt).2

/-! ### `pedersen_hash_with_separator` substantive spec -/

-- 1.5x default: the length-slot bookkeeping at the end of the proof
-- (rewriting through `Fin.sum_univ_castSucc` while transporting indices
-- across the `hN1_eq : (N+1).toNat = N.toNat + 1` bridge) needs the
-- extra headroom; the body itself is otherwise tight.
set_option maxHeartbeats 300000 in
/-- Spec for `std::hash::pedersen_hash_with_separator`. The body adds
a length-slot scalar `(N, 0)` at position `N`, derives the corresponding
generator from `"pedersen_hash_length"` (with `starting_index = 0`),
and returns the x-coordinate of the singleton MSM result. -/
theorem pedersen_hash_with_separator_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)}
    {separator : U 32} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_hash_with_separator».call h![N]
        h![input, separator])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = pointX
                (encodeCurvePoint
                  ((∑ i : Fin N.toNat,
                      scalarValueNat (Ss.get i)
                      • pedersenGenerator (p := p)
                          defaultDomainBytes (separator.toNat + i.val))
                   + (N.toNat : ℕ) • pedersenGenerator (p := p)
                          pedersenHashLengthBytes 0))
          ∧ (∀ i, (input.get i) = (Ss.get i).1 + ((pow128 : Nat) : Fp p) * (Ss.get i).2.1)
          ∧ (∀ i, ((Ss.get i).2.1 = ((phi : Nat) : Fp p) ∧ (Ss.get i).1.val < plo)
                  ∨ (Ss.get i).2.1.val < phi)) := by
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
          ((input.get ⟨j, hjN⟩) = (s.get ⟨j, hjN1⟩).1
              + ((pow128 : Nat) : Fp p) * (s.get ⟨j, hjN1⟩).2.1
            ∧ (((s.get ⟨j, hjN1⟩).2.1 = ((phi : Nat) : Fp p)
                  ∧ (s.get ⟨j, hjN1⟩).1.val < plo)
                ∨ (s.get ⟨j, hjN1⟩).2.1.val < phi))
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
  set lenScalar : Tp.denote p Scalar.type :=
    HList.toTuple p h![(Builtin.CastTp.cast N : Fp p), (Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)]
      (some «std-1.0.0-beta.14::embedded_curve_ops::EmbeddedCurveScalar».name) with hLenScalar_def
  set lenGen : Tp.denote p Point.type :=
    length_generator.get ⟨BitVec.toNat ↑(0 : U 32), hLgBdd⟩ with hLenGen_def
  set sFull : Tp.denote p (Scalar.type.array (N + 1)) :=
    sFinal.set ⟨N.toNat, hNlt⟩ lenScalar with hsFull_def
  set gFull : Tp.denote p (Point.type.array (N + 1)) :=
    gFinal.set ⟨N.toNat, hNlt⟩ lenGen with hgFull_def
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
      -- The goal: pedersenGeneratorPoint p pedersenHashLengthBytes 0 = (Ps_full.map encodeCurvePoint).get ⟨k, hk⟩
      symm
      calc (Ps_full.map encodeCurvePoint).get ⟨k, hk⟩
          = encodeCurvePoint (Ps_full.get ⟨k, hk⟩) := by
            simp [List.Vector.get_map]
        _ = encodeCurvePoint (Ps.get ⟨k, hkSucc⟩) := by
            rw [hPs_full_get k hk hkSucc]
        _ = encodeCurvePoint
              (Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩) := by
            congr 1
            apply congrArg
            apply Fin.ext; exact h_isN
        _ = _ := h_len_gen
    · have hkN : k < N.toNat := by omega
      have hkN1 : k < (N + 1).toNat := hk
      have hsetget : gFull.get ⟨k, hk⟩ = gFinal.get ⟨k, hkN1⟩ := by
        show (gFinal.set ⟨N.toNat, hNlt⟩ lenGen).get ⟨k, hk⟩ = gFinal.get ⟨k, hkN1⟩
        rw [List.Vector.get_set_of_ne]
        intro hh
        have : N.toNat = k := (Fin.mk.injEq _ _ _ _).mp hh
        exact h_isN this.symm
      rw [hsetget]
      have hgFinalEq : gFinal.get ⟨k, hkN1⟩ = domain_generators.get ⟨k, hkN⟩ :=
        (hInv k hkN hkN hkN1).2
      rw [hgFinalEq, hDom]
      symm
      calc (Ps_full.map encodeCurvePoint).get ⟨k, hk⟩
          = encodeCurvePoint (Ps_full.get ⟨k, hk⟩) := by
            simp [List.Vector.get_map]
        _ = encodeCurvePoint (Ps.get ⟨k, hkSucc⟩) := by
            rw [hPs_full_get k hk hkSucc]
        _ = encodeCurvePoint
              (Ps.get ⟨(⟨k, hkN⟩ : Fin N.toNat).val, Nat.lt_succ_of_lt (⟨k, hkN⟩ : Fin N.toNat).isLt⟩) := rfl
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
        scalarValueNat (sFull.get i)
        • (curvePoint? (gFull.get i)).get (hOnCurve i)) =
      ∑ i : Fin (N + 1).toNat,
        scalarValueNat (sFull.get i) • Ps_full.get i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hCp : curvePoint? (gFull.get i) = some (Ps_full.get i) := by
      rw [hGetEnc i]; simp
    rw [Option.get_of_eq_some _ hCp]
  -- Use steps with the builtin spec.
  steps [Lampe.Stdlib.EmbeddedCurveOps.multi_scalar_mul_builtin_spec (p := p) (N := N + 1)
    (points := gFull) (scalars := sFull) hOnCurve]
  -- Provide the existential witness Ss as the first N entries of sFinal.
  case v =>
    refine ⟨List.ofFn (fun i : Fin N.toNat => sFinal.get ⟨i.val, ?_⟩), ?_⟩
    · omega
    · simp
  -- Now discharge the goal: v = pointX (encodeCurvePoint (∑ ... + N • Ps.last)).
  rename_i hSumRes
  -- Simplify hSumRes: `indexTpl ... Member.head` reduces to the first projection of the singleton's first element.
  refine ⟨?_, ?_, ?_⟩
  · -- Result equality. We have:
    --   hSumRes : v = indexTpl (Vector.get ⟨[encodeCurvePoint <msmAcc>], _⟩ ⟨0, _⟩) Member.head
    --   hSumEq : <msmAcc-as-sum> = ∑ i, scalarValueNat (sFull.get i) • Ps_full.get i
    -- We want: v = pointX (encodeCurvePoint (∑ i : Fin N, ... • Ps_i + N.toNat • Ps_last))
    rw [hSumRes]
    show pointX
        (encodeCurvePoint _) = _
    congr 1
    congr 1
    show (∑ i : Fin (N + 1).toNat,
        scalarValueNat (sFull.get i)
        • (curvePoint? (gFull.get i)).get (hOnCurve i)) = _
    rw [hSumEq]
    have hSumSplit :
        (∑ i : Fin (N + 1).toNat,
          scalarValueNat (sFull.get i) • Ps_full.get i) =
        ∑ j : Fin (N.toNat + 1),
          scalarValueNat
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
      -- The Fin index `⟨i.castSucc.val, _⟩` reduces to `⟨i.val, _⟩`.
      have hcs_idx : (⟨(i.castSucc).val, by rw [hN1_eq]; exact (i.castSucc).isLt⟩ : Fin (N + 1).toNat) =
          ⟨i.val, hi_N1⟩ := by
        apply Fin.ext; rfl
      rw [hcs_idx]
      -- Now: sFull.get ⟨i.val, hi_N1⟩ = sFinal.get ⟨i.val, hi_N1⟩.
      have hsFull_eq : sFull.get ⟨i.val, hi_N1⟩ = sFinal.get ⟨i.val, hi_N1⟩ := by
        show (sFinal.set ⟨N.toNat, hNlt⟩ lenScalar).get _ = _
        rw [List.Vector.get_set_of_ne]
        intro hh
        have h_eq : N.toNat = i.val := (Fin.mk.injEq _ _ _ _).mp hh
        have := i.isLt; omega
      rw [hsFull_eq]
      rw [hPs_full_get i.val hi_N1 (Nat.lt_succ_of_lt i.isLt)]
      rw [hPs_get_lt i]
      have hSs_eq :
          List.Vector.get
            (⟨List.ofFn fun j : Fin N.toNat => sFinal.get ⟨j.val, by omega⟩,
                by simp⟩ : List.Vector (Scalar.denote p) N.toNat) i =
            sFinal.get ⟨i.val, hi_N1⟩ := by
        rw [List.Vector.get_eq_get_toList]
        show (List.ofFn _).get _ = _
        simp
      rw [hSs_eq]
    ·
      have hN_lt_N1 : N.toNat < (N + 1).toNat := hNlt
      have hsFull_last : sFull.get ⟨N.toNat, hN_lt_N1⟩ = lenScalar := by
        show (sFinal.set ⟨N.toNat, hNlt⟩ lenScalar).get _ = _
        rw [List.Vector.get_set_same]
      have hPsFull_last :
          Ps_full.get ⟨N.toNat, hN_lt_N1⟩ =
            Ps.get ⟨N.toNat, Nat.lt_succ_self _⟩ := by
        rw [hPs_full_get N.toNat _ (Nat.lt_succ_self _)]
      -- The form `(Fin.last N.toNat).val` reduces to N.toNat.
      have hidx :
          (⟨(Fin.last N.toNat).val, by rw [hN1_eq]; exact (Fin.last N.toNat).isLt⟩ :
            Fin (N + 1).toNat) = ⟨N.toNat, hN_lt_N1⟩ := by
        apply Fin.ext; rfl
      rw [hidx, hsFull_last, hPsFull_last]
      rw [hPs_get_last]
      -- scalarValueNat lenScalar = N.toNat.
      have hsv : scalarValueNat lenScalar = N.toNat := by
        show (scalarLo lenScalar).val
          + pow128 *
            (scalarHi lenScalar).val = N.toNat
        show ((Builtin.CastTp.cast N : Fp p)).val
          + pow128 *
            ((Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)).val = N.toNat
        have hcast_zero : ((Builtin.CastTp.cast ↑(0 : Fp p) : Fp p)).val = 0 := by
          show ((0 : Fp p)).val = 0
          simp
        rw [hcast_zero]
        show ((Builtin.CastTp.cast N : Fp p)).val + _ * 0 = N.toNat
        simp only [Nat.mul_zero, Nat.add_zero]
        show ((N.toNat : Fp p)).val = N.toNat
        rw [ZMod.val_natCast]
        apply Nat.mod_eq_of_lt
        have hNlt2 : N.toNat < 2^32 := N.isLt
        have hpow128 : (2^32 : Nat) < Lampe.Crypto.Bn254.pow128 := by decide
        have hpprime := Lampe.Crypto.Bn254.pow128_lt_prime (p := p)
        omega
      rw [hsv]
  ·
    intro i
    have hSs_eq :
        List.Vector.get
          (⟨List.ofFn fun j : Fin N.toNat => sFinal.get ⟨j.val, by omega⟩,
              by simp⟩ : List.Vector (Scalar.denote p) N.toNat) i =
          sFinal.get ⟨i.val, by omega⟩ := by
      rw [List.Vector.get_eq_get_toList]
      show (List.ofFn _).get _ = _
      simp
    rw [hSs_eq]
    exact (hInv i.val i.isLt i.isLt (by omega)).1.1
  ·
    intro i
    have hSs_eq :
        List.Vector.get
          (⟨List.ofFn fun j : Fin N.toNat => sFinal.get ⟨j.val, by omega⟩,
              by simp⟩ : List.Vector (Scalar.denote p) N.toNat) i =
          sFinal.get ⟨i.val, by omega⟩ := by
      rw [List.Vector.get_eq_get_toList]
      show (List.ofFn _).get _ = _
      simp
    rw [hSs_eq]
    exact (hInv i.val i.isLt i.isLt (by omega)).1.2

/-! ### `pedersen_commitment` wrapper spec -/

/-- Spec for `std::hash::pedersen_commitment`. The body is the single
call `pedersen_commitment_with_separator(input, 0)`, so this spec is
the `separator = 0` specialisation of
`pedersen_commitment_with_separator_spec`. -/
theorem pedersen_commitment_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_commitment».call h![N] h![input])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = encodeCurvePoint
                (∑ i, scalarValueNat (Ss.get i)
                    • pedersenGenerator (p := p)
                        defaultDomainBytes i.val)
          ∧ (∀ i, (input.get i) = (Ss.get i).1 + ((pow128 : Nat) : Fp p) * (Ss.get i).2.1)
          ∧ (∀ i, ((Ss.get i).2.1 = ((phi : Nat) : Fp p) ∧ (Ss.get i).1.val < plo)
                  ∨ (Ss.get i).2.1.val < phi)) := by
  enter_decl
  steps [pedersen_commitment_with_separator_spec (p := p) (N := N)
    (input := input) (separator := (0 : U 32))]
  case v => assumption
  -- `(0 : U 32).toNat + i.val` reduces to `i.val` via `Nat.zero_add` (after
  -- BitVec normalisation). Use `simpa` to align the inner spec's hypothesis
  -- with the wrapper's goal.
  rename_i hPost
  simpa using hPost

/-! ### `pedersen_hash` wrapper spec -/

/-- Spec for `std::hash::pedersen_hash`. The body is the single call
`pedersen_hash_with_separator(input, 0)`, so this spec is the
`separator = 0` specialisation of
`pedersen_hash_with_separator_spec`. -/
theorem pedersen_hash_spec {p N}
    [Lampe.Crypto.Bn254.Prime p]
    {input : Tp.denote p (Tp.field.array N)} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::pedersen_hash».call h![N] h![input])
      (fun r =>
        ∃∃ Ss : List.Vector (Scalar.denote p) N.toNat,
          r = pointX
                (encodeCurvePoint
                  ((∑ i : Fin N.toNat,
                      scalarValueNat (Ss.get i)
                      • pedersenGenerator (p := p)
                          defaultDomainBytes i.val)
                   + (N.toNat : ℕ) • pedersenGenerator (p := p)
                          pedersenHashLengthBytes 0))
          ∧ (∀ i, (input.get i) = (Ss.get i).1 + ((pow128 : Nat) : Fp p) * (Ss.get i).2.1)
          ∧ (∀ i, ((Ss.get i).2.1 = ((phi : Nat) : Fp p) ∧ (Ss.get i).1.val < plo)
                  ∨ (Ss.get i).2.1.val < phi)) := by
  enter_decl
  steps [pedersen_hash_with_separator_spec (p := p) (N := N)
    (input := input) (separator := (0 : U 32))]
  case v => assumption
  rename_i hPost
  simpa using hPost

end Lampe.Stdlib.Hash.Pedersen
