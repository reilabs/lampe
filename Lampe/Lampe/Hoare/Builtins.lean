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
import Lampe.Builtin.Cast
import Lampe.Builtin.Lens

namespace Lampe.STHoare

/--
Introduction rule for pure builtins.
-/
theorem pureBuiltin_intro {A : Type} {a : A} {sgn desc args} :
  STHoare p Γ
    ⟦⟧
    (.callBuiltin (sgn a).fst (sgn a).snd (Builtin.newGenericPureBuiltin sgn desc) args)
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
      (.callBuiltin argTps outTp (Builtin.newGenericPureBuiltin sgn desc) args)
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


def genericTotalPureBuiltin_intro {A : Type} {sgn : A → List Tp × Tp} {desc}
   (b : Builtin) (h : b = Builtin.newGenericTotalPureBuiltin sgn desc):
    ∀(a p Γ args), STHoare p Γ ⟦⟧
      (.callBuiltin (sgn a).fst (sgn a).snd b args)
      (fun v => v = desc a args) := by
  intros
  simp [h]
  apply pureBuiltin_intro_consequence
  any_goals rfl
  tauto


-- Arithmetics

 theorem uAdd_intro : STHoarePureBuiltin p Γ Builtin.uAdd (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uSub_intro : STHoarePureBuiltin p Γ Builtin.uSub (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try rfl
   tauto

 theorem uMul_intro : STHoarePureBuiltin p Γ Builtin.uMul (by tauto) h![a, b] := by
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
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

 theorem fSub_intro : STHoarePureBuiltin p Γ Builtin.fSub (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

 theorem fMul_intro : STHoarePureBuiltin p Γ Builtin.fMul (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

 theorem fDiv_intro : STHoarePureBuiltin p Γ Builtin.fDiv (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

 theorem fNeg_intro : STHoarePureBuiltin p Γ Builtin.fNeg (by tauto) h![a] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

-- Arrays

def PureTotalBuiltinTriple {sgn : α → List Tp × Tp} {desc : {p : Prime} → (a: α) → HList (Tp.denote p) (sgn a).1 → (sgn a).2.denote p}
    (b : Builtin)
    (_ : b = Builtin.newGenericPureBuiltin sgn fun a args => ⟨True, fun _ => desc a args⟩) : Prop :=
  ∀{a p Γ args}, STHoare p Γ ⟦⟧
    (.callBuiltin (sgn a).1 (sgn a).2 b args)
    (fun v => v = desc a args)

theorem PureTotalBuiltinTriple_intro
    {sgn : α → List Tp × Tp} {desc : {p : Prime} → (a: α) → HList (Tp.denote p) (sgn a).1 → (sgn a).2.denote p}
    (b : Builtin)
    (h : b = Builtin.newGenericPureBuiltin sgn fun a args => ⟨True, fun _ => desc a args⟩) : PureTotalBuiltinTriple b h := by
  simp only [PureTotalBuiltinTriple, h]
  intros
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem arrayIndex_intro : STHoarePureBuiltin p Γ Builtin.arrayIndex (by tauto) h![arr, i] (a := (tp, n)) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem arrayLen_intro : STHoarePureBuiltin p Γ Builtin.arrayLen (by tauto) h![arr] (a := (tp, n)) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem asSlice_intro : STHoarePureBuiltin p Γ Builtin.asSlice (by tauto) h![arr] (a := (tp, n)) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

-- BigInt

theorem bigIntEq_intro : STHoarePureBuiltin p Γ Builtin.bigIntEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem bigIntAdd_intro : STHoarePureBuiltin p Γ Builtin.bigIntAdd (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem bigIntSub_intro : STHoarePureBuiltin p Γ Builtin.bigIntSub (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem bigIntMul_intro : STHoarePureBuiltin p Γ Builtin.bigIntMul (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem bigIntDiv_intro : STHoarePureBuiltin p Γ Builtin.bigIntDiv (by tauto) h![a, b] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem bigIntFromLeBytes_intro : STHoarePureBuiltin p Γ Builtin.bigIntFromLeBytes (by tauto) h![bs, mbs] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem bigIntToLeBytes_intro : STHoarePureBuiltin p Γ Builtin.bigIntToLeBytes (by tauto) h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  . dsimp only
    intro h
    use h
  exact ()

-- Bitwise

def bNot_intro := genericTotalPureBuiltin_intro Builtin.bNot rfl ()
def bAnd_intro := genericTotalPureBuiltin_intro Builtin.bAnd rfl ()
def bOr_intro := genericTotalPureBuiltin_intro Builtin.bOr rfl ()
def bXor_intro := genericTotalPureBuiltin_intro Builtin.bXor rfl ()
def uNot_intro := genericTotalPureBuiltin_intro Builtin.uNot rfl
def uOr_intro := genericTotalPureBuiltin_intro Builtin.uOr rfl
def uAnd_intro := genericTotalPureBuiltin_intro Builtin.uAnd rfl
def uXor_intro := genericTotalPureBuiltin_intro Builtin.uXor rfl
def uShl_intro := genericTotalPureBuiltin_intro Builtin.uShl rfl
def uShr_intro := genericTotalPureBuiltin_intro Builtin.uShr rfl
def iNot_intro := genericTotalPureBuiltin_intro Builtin.iNot rfl
def iAnd_intro := genericTotalPureBuiltin_intro Builtin.iAnd rfl
def iOr_intro := genericTotalPureBuiltin_intro Builtin.iOr rfl
def iXor_intro := genericTotalPureBuiltin_intro Builtin.iXor rfl
def iShl_intro := genericTotalPureBuiltin_intro Builtin.iShl rfl
def iShr_intro := genericTotalPureBuiltin_intro Builtin.iShr rfl

-- Comparison

theorem unitEq_intro : STHoarePureBuiltin p Γ Builtin.unitEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> tauto

theorem bEq_intro : STHoarePureBuiltin p Γ Builtin.bEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem fEq_intro : STHoarePureBuiltin p Γ Builtin.fEq (by tauto) h![a, b] (a := ()) := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem uEq_intro : STHoarePureBuiltin p Γ Builtin.uEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem iEq_intro : STHoarePureBuiltin p Γ Builtin.uEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem strEq_intro : STHoarePureBuiltin p Γ Builtin.strEq (by tauto) h![a, b] := by
   apply pureBuiltin_intro_consequence <;> try tauto
   tauto

theorem uLt_intro : STHoarePureBuiltin p Γ Builtin.uLt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem iLt_intro : STHoarePureBuiltin p Γ Builtin.iLt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem uGt_intro : STHoarePureBuiltin p Γ Builtin.uGt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem iGt_intro : STHoarePureBuiltin p Γ Builtin.iGt (by tauto) h![a, b] := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

-- Field misc

theorem fApplyRangeConstraint_intro :
  STHoarePureBuiltin p Γ Builtin.fApplyRangeConstraint (by tauto) h![f, c] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem fModNumBits_intro : STHoarePureBuiltin p Γ Builtin.fModNumBits (by tauto) h![f] (a := ())  := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem fModLeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem fModBeBits_intro : STHoarePureBuiltin p Γ Builtin.fModLeBits (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem fModLeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem fModBeBytes_intro : STHoarePureBuiltin p Γ Builtin.fModLeBytes (by tauto) h![f] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem uFromField_intro : STHoarePureBuiltin p Γ Builtin.uFromField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem iFromField_intro : STHoarePureBuiltin p Γ Builtin.iFromField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem uAsField_intro {p Γ s f} : STHoarePureBuiltin p Γ Builtin.uAsField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem iAsField_intro {p Γ s f} : STHoarePureBuiltin p Γ Builtin.iAsField (by tauto) h![f] (a := s) := by
  apply pureBuiltin_intro_consequence <;> try tauto
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
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

-- Memory

theorem ref_intro :
    STHoare p Γ
      ⟦⟧
      (.callBuiltin [tp] (.ref tp) .ref h![v])
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

theorem readRef_intro :
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.callBuiltin [.ref tp] tp .readRef h![r])
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

theorem writeRef_intro :
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.callBuiltin [.ref tp, tp] .unit .writeRef h![r, v'])
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

-- TODO maybe these can be removed as `steps` automates it and the compound construction is still usable manually.
theorem mkTuple_intro : STHoarePureBuiltin p Γ Builtin.mkTuple (by tauto) fieldExprs (a := (name, fieldTps)) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem makeData_intro : STHoarePureBuiltin p Γ Builtin.makeData (by tauto) fieldExprs (a := (name, fieldTps)) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem projectTuple_intro : STHoarePureBuiltin p Γ (Builtin.projectTuple mem) (by tauto) h![tpl] (a := name) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem getMember_intro : STHoarePureBuiltin p Γ (Builtin.getMember mem) (by tauto) fieldExprs (a := name) := by
  apply pureBuiltin_intro_consequence <;> try tauto

-- Lens

 theorem modifyLens_intro {lens : Lens (Tp.denote p) tp₁ tp₂} {s : Tp.denote p tp₁} {v : Tp.denote p tp₂} :
    STHoare p Γ
    [r ↦ ⟨tp₁, s⟩]
    (.callBuiltin [tp₁.ref, tp₂] .unit (.modifyLens lens) h![r, v])
    (fun _ => ∃∃h, [r ↦ ⟨tp₁, lens.modify s v |>.get h⟩]) := by
  unfold STHoare THoare
  intros H st h
  constructor
  cases hl : (lens.modify s v)
  . apply Builtin.modifyLensOmni.err <;> try tauto
    unfold SLP.star State.valSingleton at *
    aesop
  . apply Builtin.modifyLensOmni.ok <;> try tauto
    . unfold SLP.star State.valSingleton at *
      aesop
    . unfold mapToValHeapCondition
      simp_all only [Option.map_some, SLP.true_star, SLP.star_assoc]
      obtain ⟨st₁, st₂, ⟨h₁, _⟩, h₂, h₃, h₄⟩ := h
      simp only [State.valSingleton] at h₃
      rename (Tp.denote p tp₁) => s'
      exists ⟨Finmap.singleton r ⟨tp₁, s'⟩, st₁.lambdas⟩, st₂
      apply And.intro
      . simp only [LawfulHeap.disjoint]
        apply And.intro ?_ (by tauto)
        aesop
      apply And.intro
      . simp only [State.union_parts, State.mk.injEq, and_true]
        apply And.intro ?_ (by simp_all)
        rw [Finmap.insert_eq_singleton_union]
        simp_all only [State.union_parts]
        rw [←Finmap.union_assoc, ←Finmap.insert_eq_singleton_union]
        simp_all
      apply And.intro
      . simp_all [SLP.exists']
      apply SLP.ent_star_top
      tauto

theorem getLens_intro {lens : Lens (Tp.denote p) tp₁ tp₂} :
    STHoare p Γ
    ⟦⟧
    (.callBuiltin [tp₁] tp₂ (.getLens lens) h![s])
    (fun v => ⟦lens.get s = some v⟧) := by
  unfold STHoare THoare
  intros H st h
  constructor
  cases hl : (lens.get s)
  . apply Builtin.getLensOmni.err <;> tauto
  . apply Builtin.getLensOmni.ok <;> try tauto
    . unfold mapToValHeapCondition
      simp_all only [Option.map_some, SLP.true_star, SLP.star_assoc]
      apply SLP.ent_star_top at h
      simp_all

-- Misc

theorem assert_intro : STHoarePureBuiltin p Γ Builtin.assert (by tauto) h![a] (a := ()) := by
  apply pureBuiltin_intro_consequence <;> try tauto
  tauto

theorem cast_intro [Builtin.CastTp tp tp'] : STHoare p Γ ⟦⟧ (.callBuiltin [tp] tp' .cast h![v])
   (fun v' => v' = @Builtin.CastTp.cast tp tp' _ p v) := by
   unfold STHoare THoare
   intros
   constructor
   constructor
   simp only [mapToValHeapCondition]
   apply SLP.ent_star_top
   simp_all

end Lampe.STHoare
