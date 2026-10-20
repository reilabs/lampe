import Lampe.Builtin.Cast

open Lampe

namespace CastRegression

/--
Issue #316: `CastTp` stored the cast function as data, so a derivation of the cast builtin
could supply a hand-made instance and return any value. Now that `CastTp` is a proposition,
any two derivations of one cast agree on the result.
-/
theorem cast_deterministic {P : Prime} {st : ValHeap P} {tp tp' : Tp}
    [Builtin.CastTp tp tp'] {v : Tp.denote P tp}
    {Q₁ Q₂ : Option (ValHeap P × Tp.denote P tp') → Prop}
    (h₁ : Builtin.castOmni P st [tp] tp' h![v] Q₁)
    (h₂ : Builtin.castOmni P st [tp] tp' h![v] Q₂) :
    ∃ r, Q₁ r ∧ Q₂ r := by
  obtain ⟨_, hq₁⟩ := Builtin.castOmni_inv h₁
  obtain ⟨_, hq₂⟩ := Builtin.castOmni_inv h₂
  exact ⟨_, hq₁, hq₂⟩

/--
The concrete shape from issue #316: a derivation cannot assign an arbitrary value `c` to
`v as Field`; the result is pinned to `v.toNat`.
-/
theorem cast_u64_field_pinned {P : Prime} {st : ValHeap P} {v : U 64} {c : Fp P}
    (h : Builtin.castOmni P st [.u 64] .field h![v] (fun r => r = some (st, c))) :
    c = (v.toNat : Fp P) := by
  obtain ⟨_, hq⟩ := Builtin.castOmni_inv h
  simp only [Builtin.CastTp.cast, Option.some.injEq, Prod.mk.injEq, true_and] at hq
  exact hq.symm

end CastRegression
