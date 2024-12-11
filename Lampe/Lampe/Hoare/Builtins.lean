import Lampe.Hoare.SepTotal

import Lampe.Builtin.Arith
import Lampe.Builtin.Array
import Lampe.Builtin.BigInt
import Lampe.Builtin.Bit
import Lampe.Builtin.Cmp
import Lampe.Builtin.Field
import Lampe.Builtin.Memory
import Lampe.Builtin.Slice
import Lampe.Builtin.Str
import Lampe.Builtin.Struct

namespace Lampe.STHoare

/--
Introduction rule for pure builtins.
-/
theorem pureBuiltin_intro {A : Type} {a : A} {sgn desc args} :
  STHoare p Γ
    ⟦⟧
    (.call h![] (sgn a).fst (sgn a).snd (.builtin (Builtin.newGenericPureBuiltin sgn desc)) args)
    (fun v => ∃h, (v = (desc a args).snd h)) := by
  unfold STHoare
  intro H
  unfold THoare
  intros st p
  constructor
  cases em (desc a args).fst
  . apply Builtin.genericPureOmni.ok
    . simp_all only [mapToValHeapCondition, SLP.true_star, exists_const]
      apply SLP.ent_star_top
      simp_all only [SLP.true_star, exists_const]
    . tauto
  . apply Builtin.genericPureOmni.err
    . tauto
    . simp_all [mapToValHeapCondition]

lemma pureBuiltin_intro_consequence
    {A : Type} {a : A} {sgn desc args} {Q : Tp.denote p outTp → Prop}
    (h1 : argTps = (sgn a).fst)
    (h2 : outTp = (sgn a).snd)
    (hp : (h: (desc a (h1 ▸ args)).fst) → Q (h2 ▸ (desc a (h1 ▸ args)).snd h)) :
    STHoare p Γ ⟦⟧
      (.call h![] argTps outTp (.builtin (Builtin.newGenericPureBuiltin sgn desc)) args)
      fun v => Q v := by
  subst_vars
  dsimp only at *
  apply ramified_frame_top
  apply pureBuiltin_intro
  simp only [SLP.true_star]
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  simp only [SLP.true_star]
  apply SLP.pure_left'
  rintro ⟨_, _⟩
  simp_all [SLP.entails_top]

-- Arithmetics

 theorem uAdd_intro : STHoarePureBuiltin p Γ Builtin.uAdd (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uSub_intro : STHoarePureBuiltin p Γ Builtin.uSub (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uMul_intro : STHoarePureBuiltin p Γ Builtin.uAdd (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uDiv_intro : STHoarePureBuiltin p Γ Builtin.uDiv (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uRem_intro : STHoarePureBuiltin p Γ Builtin.uRem (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iAdd_intro : STHoarePureBuiltin p Γ Builtin.iAdd (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iSub_intro : STHoarePureBuiltin p Γ Builtin.iSub (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iMul_intro : STHoarePureBuiltin p Γ Builtin.iMul (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iDiv_intro : STHoarePureBuiltin p Γ Builtin.iDiv (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iRem_intro : STHoarePureBuiltin p Γ Builtin.iRem (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem iNeg_intro : STHoarePureBuiltin p Γ Builtin.iNeg (by tauto) h![a] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem fAdd_intro : STHoarePureBuiltin p Γ Builtin.fAdd (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

 theorem fSub_intro : STHoarePureBuiltin p Γ Builtin.fSub (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

 theorem fMul_intro : STHoarePureBuiltin p Γ Builtin.fMul (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

 theorem fDiv_intro : STHoarePureBuiltin p Γ Builtin.fDiv (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

 theorem fNeg_intro : STHoarePureBuiltin p Γ Builtin.fNeg (by tauto) h![a] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

-- Arrays

theorem arrayLen_intro : STHoarePureBuiltin p Γ Builtin.arrayLen (by tauto) h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem arrayAsSlice_intro : STHoarePureBuiltin p Γ Builtin.arrayAsSlice (by tauto) h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

-- BigInt

theorem bigIntEq_intro : STHoarePureBuiltin p Γ Builtin.bigIntEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem bigIntAdd_intro : STHoarePureBuiltin p Γ Builtin.bigIntAdd (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntSub_intro : STHoarePureBuiltin p Γ Builtin.bigIntSub (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntMul_intro : STHoarePureBuiltin p Γ Builtin.bigIntMul (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntDiv_intro : STHoarePureBuiltin p Γ Builtin.bigIntDiv (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntFromLeBytes_intro : STHoarePureBuiltin p Γ Builtin.bigIntFromLeBytes (by tauto) h![bs, mbs] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bigIntToLeBytes_intro : STHoarePureBuiltin p Γ Builtin.bigIntToLeBytes (by tauto) h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  . dsimp only
    intro h
    use h
  exact ()

-- Bitwise

theorem bNot_intro : STHoarePureBuiltin p Γ Builtin.bNot (by tauto) h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bAnd_intro : STHoarePureBuiltin p Γ Builtin.bAnd (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bOr_intro : STHoarePureBuiltin p Γ Builtin.bOr (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem bXor_intro : STHoarePureBuiltin p Γ Builtin.bXor (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uNot_intro : STHoarePureBuiltin p Γ Builtin.uNot (by tauto) h![a] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uOr_intro : STHoarePureBuiltin p Γ Builtin.uOr (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uAnd_intro : STHoarePureBuiltin p Γ Builtin.uAnd (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uXor_intro : STHoarePureBuiltin p Γ Builtin.uXor (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uShl_intro : STHoarePureBuiltin p Γ Builtin.uShl (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uShr_intro : STHoarePureBuiltin p Γ Builtin.uShl (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iNot_intro : STHoarePureBuiltin p Γ Builtin.iNot (by tauto) h![a] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iAnd_intro : STHoarePureBuiltin p Γ Builtin.iAnd (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iOr_intro : STHoarePureBuiltin p Γ Builtin.iOr (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iXor_intro : STHoarePureBuiltin p Γ Builtin.iXor (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iShl_intro : STHoarePureBuiltin p Γ Builtin.iShl (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iShr_intro : STHoarePureBuiltin p Γ Builtin.iShr (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

-- Comparison

theorem unitEq_intro : STHoarePureBuiltin p Γ Builtin.unitEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto

theorem boolEq_intro : STHoarePureBuiltin p Γ Builtin.boolEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem fEq_intro : STHoarePureBuiltin p Γ Builtin.fEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem uEq_intro : STHoarePureBuiltin p Γ Builtin.uEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem iEq_intro : STHoarePureBuiltin p Γ Builtin.uEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem strEq_intro : STHoarePureBuiltin p Γ Builtin.strEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> tauto
   tauto

theorem uLt_intro : STHoarePureBuiltin p Γ Builtin.uLt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iLt_intro : STHoarePureBuiltin p Γ Builtin.iLt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uGt_intro : STHoarePureBuiltin p Γ Builtin.uGt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iGt_intro : STHoarePureBuiltin p Γ Builtin.iGt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

-- Field misc

theorem fApplyRangeConstraint_intro :
  STHoarePureBuiltin p Γ Builtin.fApplyRangeConstraint (by tauto) h![f, c] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModNumBits_intro : STHoarePureBuiltin p Γ Builtin.fModNumBits (by tauto) h![f] (a := ())  := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModLeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModBeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModLeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem fModBeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem uFromField_intro : STHoarePureBuiltin p Γ Builtin.uFromField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem iFromField_intro : STHoarePureBuiltin p Γ Builtin.iFromField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

-- Slice

theorem sliceLen_intro : STHoarePureBuiltin p Γ Builtin.sliceLen (by tauto) h![s] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceIndex_intro : STHoarePureBuiltin p Γ Builtin.sliceIndex (by tauto) h![sl, i] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePushBack_intro : STHoarePureBuiltin p Γ Builtin.slicePushBack (by tauto) h![sl, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePushFront_intro : STHoarePureBuiltin p Γ Builtin.slicePushFront (by tauto) h![sl, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceInsert_intro : STHoarePureBuiltin p Γ Builtin.sliceInsert (by tauto) h![sl, i, e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePopFront_intro : STHoarePureBuiltin p Γ Builtin.slicePopFront (by tauto) h![sl] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem slicePopBack_intro : STHoarePureBuiltin p Γ Builtin.slicePopBack (by tauto) h![sl] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem sliceRemove_intro : STHoarePureBuiltin p Γ Builtin.sliceRemove (by tauto) h![sl, i]  := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

-- String

theorem strAsBytes_intro : STHoarePureBuiltin p Γ Builtin.strAsBytes (by tauto) h![s] := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

-- Memory

theorem ref_intro:
    STHoare p Γ
      ⟦⟧
      (.call h![] [tp] (Tp.ref tp) (.builtin .ref) h![v])
      (fun r => [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.ref_intro (fun _ => SLP.entails_self)
  simp only [SLP.true_star]
  intro st hH r hr
  exists (⟨Finmap.singleton r ⟨tp, v⟩, st.lambdas⟩ ∪ st), ∅
  apply And.intro (by rw [LawfulHeap.disjoint_symm_iff]; apply LawfulHeap.empty_disjoint)
  constructor
  . simp only [State.insertVal, Finmap.insert_eq_singleton_union, LawfulHeap.union_empty]
    simp only [State.union_parts_left, Finmap.union_self]
  . apply And.intro ?_ (by simp)
    exists (⟨Finmap.singleton r ⟨tp, v⟩, ∅⟩), st
    constructor
    . simp only [LawfulHeap.disjoint]
      apply And.intro (by simp [Finmap.singleton_disjoint_of_not_mem hr]) (by tauto)
    . simp_all only
      apply And.intro _ (by trivial)
      simp only [State.union_parts_left, Finmap.empty_union, Finmap.union_self]

theorem readRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref] tp (.builtin .readRef) h![r])
    (fun v' => ⟦v' = v⟧ ⋆ [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.readRef_intro (fun _ => SLP.entails_self)
  rotate_left
  intro st
  rintro ⟨_, _, _, _, hs, _⟩
  subst_vars
  apply And.intro
  . simp only [State.union_vals]
    rename_i st₁ st₂ _ _
    have hsome : Finmap.lookup r st₁.vals = some ⟨tp, v⟩ := by
      unfold State.valSingleton at hs
      rw [hs]
      apply Finmap.lookup_singleton_eq
    rw [Finmap.lookup_union_left]
    tauto
    apply Finmap.lookup_isSome.mp
    rw [hsome]
    apply Option.isSome_some
  simp only [SLP.true_star, SLP.star_assoc]
  rename_i st₁ st₂ _ _
  exists (⟨Finmap.singleton r ⟨tp, v⟩, st₁.lambdas⟩), ?_
  unfold State.valSingleton at hs
  rw [←hs]
  repeat apply And.intro (by tauto)
  apply SLP.ent_star_top
  assumption

theorem writeRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref, tp] .unit (.builtin .writeRef) h![r, v'])
    (fun _ => [r ↦ ⟨tp, v'⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.writeRef_intro (fun _ => SLP.entails_self)
  intro st
  rintro ⟨_, _, _, _, hs, _⟩
  simp only [State.valSingleton] at hs
  subst_vars
  apply And.intro
  . rename_i st₁ st₂ _ _
    have _ : r ∈ st₁.vals := by rw [hs]; tauto
    simp_all [State.membership_in_val]
  simp only [Finmap.insert_eq_singleton_union, ←Finmap.union_assoc, Finmap.union_singleton, SLP.star_assoc]
  rename_i st₁ st₂ _ _
  exists (⟨Finmap.singleton r ⟨tp, v'⟩, st₁.lambdas⟩), ?_
  refine ⟨?_, ?_, ?_, (by apply SLP.ent_star_top; assumption)⟩
  . simp only [LawfulHeap.disjoint] at *
    have _ : r ∉ st₂.vals := by
      rename_i h _
      rw [hs] at h
      apply Finmap.singleton_disjoint_iff_not_mem.mp <;> tauto
    refine ⟨?_, by tauto⟩
    apply Finmap.singleton_disjoint_of_not_mem
    assumption
  . simp only [State.mk.injEq, State.union_vals, State.union_closures, State.union_parts_left]
    rw [←Finmap.union_assoc, hs]
    simp [Finmap.union_singleton]
  . simp_all

-- Struct/tuple

theorem mkTuple_intro : STHoarePureBuiltin p Γ Builtin.mkTuple (by tauto) fieldExprs (a := (name, fieldTps)) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

theorem projectTuple_intro : STHoarePureBuiltin p Γ (Builtin.projectTuple mem) (by tauto) h![tpl] (a := name) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

-- Misc

theorem assert_intro : STHoarePureBuiltin p Γ Builtin.assert (by tauto) h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> tauto
  tauto

end Lampe.STHoare
