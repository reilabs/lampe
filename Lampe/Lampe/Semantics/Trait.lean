import Lampe.Semantics.Env

namespace Lampe

/--
Having an instance of this type indicates that in the environment `Γ` we are able to resolve a trait
implementation that matches the provided `TraitImplRef`.
-/
inductive TraitResolvable (Γ : Env) : TraitImplRef → Prop where
| ok {ref impl} :
  (ref.trait.name, impl) ∈ Γ.traits →
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds) →
  (implGenerics : HList Kind.denote impl.implGenericKinds) →
  (ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics) →
  ref.self = impl.self implGenerics →
  (∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) →
  TraitResolvable Γ ref

/--
Any theorem involving `TraitResolvable` that is proven for some environment Γ₁ is is also valid for
an environment Γ₂ where Γ₁ ⊆ Γ₂.
-/
theorem TraitResolvable.env_mono
    {Γ₁ Γ₂ : Env}
    (inner_sub_outer : Γ₁ ⊆ Γ₂)
  : TraitResolvable Γ₁ t → TraitResolvable Γ₂ t := by
  intro h
  induction h

  constructor
  . apply inner_sub_outer.2
    assumption

  all_goals assumption

/--
Having an instance of this type indicates a successful trait resolution for the provided
`TraitImplRef` in the environment `Γ`, yielding the methods available in said trait implementation.
-/
inductive TraitResolution (Γ : Env) : TraitImplRef → List (Ident × Function) → Prop where
| ok {ref impl}
  (h_mem : (ref.trait.name, impl) ∈ Γ.traits)
  (ktc : ref.trait.traitGenericKinds = impl.traitGenericKinds)
  (implGenerics : HList Kind.denote impl.implGenericKinds)
  (_ : ktc ▸ ref.trait.traitGenerics = impl.traitGenerics implGenerics)
  (_ : ref.self = impl.self implGenerics)
  (_ : ∀constraint ∈ impl.constraints implGenerics, TraitResolvable Γ constraint) :
  TraitResolution Γ ref (impl.impl implGenerics)

/--
Any theorem involving `TraitResolution` that is proven for some environment Γ₁ is is also valid for
an environment Γ₂ where Γ₁ ⊆ Γ₂.
-/
theorem TraitResolution.env_mono
    {Γ₁ Γ₂ : Env}
    (inner_sub_outer : Γ₁ ⊆ Γ₂)
  : TraitResolution Γ₁ t xs → TraitResolution Γ₂ t xs := by
  intro h
  induction h

  constructor
  . apply inner_sub_outer.2
    assumption

  any_goals assumption
  . intros
    apply TraitResolvable.env_mono inner_sub_outer
    tauto

end Lampe
