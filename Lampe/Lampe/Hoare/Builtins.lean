import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

-- Arithmetics

theorem add_intro [Builtin.ArithAdd tp]
   : STHoare p Γ ⟦⟧
   (.call h![] [tp, tp] tp (.builtin .add) h![a, b])
   (fun v => v = Builtin.ArithAdd.compute a b ∧ (Builtin.ArithAdd.validate a b)) := by
  unfold STHoare
  intros H st h
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  constructor
  by_cases hv : Builtin.ArithAdd.validate a b
  · apply Builtin.addOmni.ok
    · assumption
    · simp only [SLP.star_assoc]
      exists ∅, st
      simp_all [SLP.lift, Finmap.Disjoint.symm]
  · apply Builtin.addOmni.err <;> tauto

theorem mul_intro {ha : Builtin.ArithTp tp} : STHoare p Γ ⟦⟧
    (.call h![] [tp, tp] tp (.builtin .mul) h![a, b])
    (fun v => v = Builtin.mulOp ha a b ∧ (Builtin.noOverflow a b (·*·))) := by
  unfold STHoare
  intros H st h
  constructor
  simp only [Builtin.mul]
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  cases tp
  <;> (constructor; simp only [SLP.true_star])
  <;> (
    simp only [Builtin.noOverflow] at *
    intros
  )
  <;> try tauto
  all_goals try unfold bitsCanRepresent
  . rename_i hno
    simp only [hno, and_self, SLP.true_star]
    tauto
  . rename_i hno
    simp only [hno, and_self, SLP.true_star]
    tauto
  . simp only [and_self, SLP.true_star]
    tauto
  . simp only [and_self, SLP.true_star]
    tauto

theorem sub_intro {ha : Builtin.ArithTp tp}: STHoare p Γ ⟦⟧
    (.call h![] [tp, tp] tp (.builtin .sub) h![a, b])
    (fun v => v = Builtin.subOp h a b ∧ (Builtin.noUnderflow a b (·-·))) := by
  unfold STHoare
  intros H st h
  constructor
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  cases tp
  <;> (constructor; simp only [SLP.true_star])
  <;> (
    simp only [Builtin.noUnderflow] at *
    intros
  )
  <;> try tauto
  all_goals try unfold bitsCanRepresent
  . rename_i hno
    simp only [hno, and_self, SLP.true_star]
    tauto
  . rename_i hno
    simp only [hno, and_self, SLP.true_star]
    tauto
  . simp only [and_self, SLP.true_star]
    tauto
  . simp only [and_self, SLP.true_star]
    tauto

theorem div_intro {ha : Builtin.ArithTp tp}: STHoare p Γ ⟦⟧
    (.call h![] [tp, tp] tp (.builtin .div) h![a, b])
    (fun v => v = Builtin.divOp ha a b ∧ Builtin.canDivide a b) := by
  unfold STHoare
  intros H st h
  constructor
  simp only [Builtin.div]
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  cases tp
  <;> (constructor; simp only [SLP.true_star])
  <;> (
    simp only [Builtin.canDivide] at *
    intros
  )
  <;> try tauto
  all_goals (
    have hno : b ≠ 0 ↔ True := by tauto
    simp only [hno, and_self, SLP.true_star]
    tauto
  )

theorem rem_intro : STHoare p Γ ⟦⟧
    (.call h![] [tp, tp] tp (.builtin .rem) h![a, b])
    (fun v => Builtin.canDivide a b ∧
      match tp with
      | .u _ => v = a % b
      | .i _ => v = Builtin.intRem a b
      | _ => False) := by
  unfold STHoare
  intros H st h
  constructor
  simp only [Builtin.rem]
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  cases tp
  <;> (constructor; simp only [SLP.true_star])
  <;> (
    simp only [Builtin.canDivide] at *
    intros
  )
  <;> try tauto
  all_goals (
    have hno : b ≠ 0 ↔ True := by tauto
    simp only [hno, and_self, SLP.true_star]
    tauto
  )

theorem neg_intro : STHoare p Γ ⟦⟧
  (.call h![] [tp, tp] tp (.builtin .neg) h![a, b])
  (fun v => match tp with
    | .i _ => v = -a
    | .field => v = -a
    | .bi => v = -a
    | _ => False) := by
  unfold STHoare
  intros H st h
  constructor
  simp only [Builtin.rem]
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  cases tp
  <;> (constructor; simp)

-- Arrays

theorem arrayLen_intro : STHoarePureBuiltin p Γ Builtin.arrayLen (by tauto) h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

theorem arrayAsSlice_intro : STHoarePureBuiltin p Γ Builtin.arrayAsSlice (by tauto) h![arr] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  tauto

-- BigInt misc

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

theorem eq_intro [Builtin.EqTp tp]: STHoare p Γ ⟦⟧
    (.call h![] [tp, tp] .bool (.builtin .eq) h![a, b])
    (fun v => v = (Builtin.EqTp.eq a b)) := by
  unfold STHoare
  unfold THoare
  intros H st h
  rw [SLP.true_star] at h
  apply SLP.ent_star_top at h
  constructor
  constructor
  simp only [SLP.star_assoc]
  exists ∅, st
  simp_all [SLP.lift, Finmap.Disjoint.symm]

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

-- Zeroed

theorem zeroed_intro : STHoarePureBuiltin p Γ Builtin.zeroed (by tauto) h![] (a := tp) := by
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
  exists (Finmap.singleton r ⟨tp, v⟩ ∪ st), ∅
  apply And.intro (by simp)
  apply And.intro (by simp [Finmap.insert_eq_singleton_union])
  apply And.intro ?_ (by simp)
  exists (Finmap.singleton r ⟨tp, v⟩), st
  simp_all [SLP.singleton]

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
  apply And.intro (by simp; rfl)
  simp only [SLP.true_star, SLP.star_assoc]
  exists (Finmap.singleton r ⟨tp, v⟩), ?_
  apply And.intro (by assumption)
  apply And.intro rfl
  apply And.intro (by simp [SLP.singleton])
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
  simp only [SLP.singleton] at hs
  subst_vars
  apply And.intro (by simp)
  simp only
  simp only [Finmap.insert_eq_singleton_union, ←Finmap.union_assoc, Finmap.union_singleton, SLP.star_assoc]
  use Finmap.singleton r ⟨tp, v'⟩, ?_
  apply And.intro (by assumption)
  apply And.intro rfl
  apply And.intro (by simp [SLP.singleton])
  apply SLP.ent_star_top
  assumption

-- Misc

theorem assert_intro : STHoarePureBuiltin p Γ Builtin.assert (by tauto) h![a] (a := ()) := by
  unfold STHoarePureBuiltin
  intro H
  apply THoare.assert_intro
  simp [SLP.entails_self, SLP.star_mono_l]

end Lampe.STHoare