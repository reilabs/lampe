-- End-to-end proof test for impl Trait return types (issues #265, #267)

import «ExtractionTests-0.0.0».Extracted
import Lampe

open Lampe

set_option linter.unusedTactic false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev ImplTraitEnv := «ExtractionTests-0.0.0».ImplTraitReturn.env

-- get_impl_bar() returns Bar{}, which is ()
theorem get_impl_bar_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::get_impl_bar».call h![] h![])
      fun v => v = () := by
  enter_decl; steps; simp_all

-- get_impl_baz() returns Baz{x: 99}, a one-field struct: (99, ())
theorem get_impl_baz_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::get_impl_baz».call h![] h![])
      fun v => v = ((99 : Fp lp), ()) := by
  enter_decl; steps; simp_all

-- use_bar() calls call_foo(get_impl_bar()).
-- Exercises: generic call_foo<Bar>, trait resolution (Bar as Foo)::foo, returns 42
theorem use_bar_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::use_bar».call h![] h![])
      fun v => v = (42 : Fp lp) := by
  enter_decl
  steps [get_impl_bar_spec]
  enter_decl
  steps
  resolve_trait
  steps
  norm_cast

-- use_baz() calls call_foo(get_impl_baz()).
-- Exercises: generic call_foo<Baz>, trait resolution (Baz as Foo)::foo, returns 99
theorem use_baz_spec {lp} :
    STHoare lp ImplTraitEnv ⟦⟧
      («ExtractionTests-0.0.0::impl_trait_return::use_baz».call h![] h![])
      fun v => v = (99 : Fp lp) := by
  enter_decl
  steps [get_impl_baz_spec]
  enter_decl
  steps
  resolve_trait
  steps
  norm_cast

-- Trait associated constants are extracted as additional kind-annotated
-- params on the trait alongside associated types. Use sites emit a
-- name-bound reference (`uConst!(N: u32)`) into that scope, so reasoning
-- about a use site requires resolving the trait impl to bind `N`. These
-- specs exercise the `Foo` and `Bar` impls of `HasConst` (which fix
-- `N := 5` and `N := 10`) and the polymorphic `poly_array<T>()` use of
-- `<T as HasConst>::N` at type level - a scenario where static resolution
-- would have been impossible because `T` is itself a generic.
abbrev TraitAssocConstEnv :=
  «ExtractionTests-0.0.0».TraitAssociatedConst.env

theorem double_foo_spec {lp} :
    STHoare lp TraitAssocConstEnv ⟦⟧
      («ExtractionTests-0.0.0::trait_associated_const::double_foo».call h![] h![])
      fun v => v = (10 : U 32) := by
  enter_decl
  steps
  resolve_trait
  steps
  simp [Tp.denote] at *
  subst_vars
  rfl

theorem double_bar_spec {lp} :
    STHoare lp TraitAssocConstEnv ⟦⟧
      («ExtractionTests-0.0.0::trait_associated_const::double_bar».call h![] h![])
      fun v => v = (20 : U 32) := by
  enter_decl
  steps
  resolve_trait
  steps
  simp [Tp.denote] at *
  subst_vars
  rfl

theorem use_foo_array_spec {lp} :
    STHoare lp TraitAssocConstEnv ⟦⟧
      («ExtractionTests-0.0.0::trait_associated_const::use_foo_array».call h![] h![])
      fun v => v = List.Vector.replicate 5 (0#32 : U 32) := by
  enter_decl
  steps
  enter_decl
  steps
  subst_vars
  rfl

theorem use_bar_array_spec {lp} :
    STHoare lp TraitAssocConstEnv ⟦⟧
      («ExtractionTests-0.0.0::trait_associated_const::use_bar_array».call h![] h![])
      fun v => v = List.Vector.replicate 10 (0#32 : U 32) := by
  enter_decl
  steps
  enter_decl
  steps
  subst_vars
  rfl
