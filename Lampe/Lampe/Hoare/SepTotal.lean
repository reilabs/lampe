import Lampe.Ast
import Lampe.Tp
import Lampe.Semantics
import Lampe.Hoare.Total

namespace Lampe

/--
A Hoare triple `{P} e {λv ↦ Q v}` has the following meaning:
if the state of the program satisfies the pre-condition `P`,
then the expression `e` terminates and evaluates to `v` such that the post-condition `Q v` holds.

Note that even if `e` terminates, it may evaluate to an error, e.g., division-by-zero.
Accordingly, we interpret `{P} e {λv ↦ Q v}` as follows:
if `P` holds, then `e` terminates and it either (1) fails or (2) *successfully* evaluates to `v` such that `Q v` holds.
This is logically equivalent to saying that if `P` holds, then `e` terminates and (`Q v` holds if `e` succeeds and evaluates to `v`).

Hence, the triples are *partial* with respect to failure and *total* with respect to termination.

An intuitive way of looking at this is thinking in terms of "knowledge discovery".
For example, if the operation `a + b` succeeds, then we know that it evaluates to `v = a + b` **and** `a + b < 2^32`, i.e., no overflow has happened.
Then, we would define the post-condition such that `Q = λv ↦ (v = a + b) ∧ (a + b < 2^32)`.
 -/
def STHoare p Γ P e (Q : Tp.denote p tp → SLP (State p))
  := ∀H, THoare p Γ (P ⋆ H) e (fun v => ((Q v) ⋆ H) ⋆ ⊤)

abbrev STHoarePureBuiltin p (Γ : Env)
  (b : Lampe.Builtin)
  {a : A}
  (_ : b = @Builtin.newGenericPureBuiltin A sgn desc)
  (args : HList (Tp.denote p) (sgn a).fst) : Prop :=
    STHoare p Γ ⟦⟧
      (.callBuiltin (sgn a).fst (sgn a).snd b args)
      (fun v => ∃h, v = (desc a (args)).snd h)

namespace STHoare

theorem frame (h_hoare: STHoare p Γ P e Q): STHoare p Γ (P ⋆ H) e (fun v => Q v ⋆ H) := by
  unfold STHoare
  intro H'
  apply THoare.consequence ?_ (h_hoare (H ⋆ H')) ?_ <;> {
    simp_all only [SLP.star_assoc] -- [TODO] use SL-normalizer
    tauto
  }

theorem consequence {p tp} {e : Expr (Tp.denote p) tp} {H₁ H₂} {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_post_conseq : ∀ v, Q₁ v ⋆ ⊤ ⊢ Q₂ v ⋆ ⊤)
    (h_hoare: STHoare p Γ H₁ e Q₁):
    STHoare p Γ H₂ e Q₂:= by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ (h_hoare H) ?_
  · apply SLP.star_mono_r; assumption
  · intro
    repeat rw [SLP.star_comm (H:=H), SLP.star_assoc]
    apply SLP.star_mono_l
    apply_assumption

theorem ramified_frame_top {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare: STHoare p Γ H₁ e Q₁)
    (h_ent: H₂ ⊢ H₁ ⋆ (∀∀v, Q₁ v -⋆ (Q₂ v ⋆ ⊤))):
    STHoare p Γ H₂ e Q₂ := by
  unfold STHoare
  intro H
  apply consequence h_ent ?_
  apply frame h_hoare
  intro v
  apply SLP.entails_trans
  · apply SLP.star_mono_r
    apply SLP.star_mono_l
    apply SLP.forall_left
    apply SLP.entails_self
    use v
  apply SLP.entails_trans
  · apply SLP.star_mono_r
    apply SLP.wand_cancel
  simp [SLP.entails_self]

theorem consequence_frame_left {H H₁ H₂ : SLP (State p)}
    (h_hoare: STHoare p Γ H₁ e Q)
    (h_ent : H ⊢ (H₁ ⋆ H₂)):
    STHoare p Γ H e (fun v => Q v ⋆ H₂) := by
  apply ramified_frame_top h_hoare
  apply SLP.entails_trans
  · use h_ent
  apply SLP.star_mono_l
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  rw [SLP.star_comm]
  apply SLP.ent_star_top

theorem var_intro {v : Tp.denote p tp}:
    STHoare p Γ ⟦⟧ (.var v) (fun v' => ⟦v' = v⟧) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.var_intro (fun _ => SLP.entails_self)
  simp

theorem letIn_intro {tp} {P} {Q : Tp.denote p tp → SLP (State p)} {e₁ e₂}
    (h_first: STHoare p Γ P e₁ Q)
    (h_rest: ∀v, STHoare p Γ (Q v) (e₂ v) R):
    STHoare p Γ P (Expr.letIn e₁ e₂) R := by
  unfold STHoare at *
  intro H
  apply THoare.letIn_intro
  · tauto
  intro v
  apply THoare.consequence
  rotate_left
  apply h_rest v (H ⋆ ⊤)
  · simp [SLP.entails_self]
  · simp [SLP.entails_self]

@[simp]
lemma Finmap.empty_disjoint: Finmap.Disjoint st ∅ := by
  rw [Finmap.Disjoint.symm_iff]
  simp [Finmap.disjoint_empty]

lemma Finmap.union_singleton [DecidableEq α] {β : α → Type u} {r : α} {v v' : β r} :
  Finmap.singleton r v ∪ Finmap.singleton r v' = Finmap.singleton r v := by
  apply Finmap.ext_lookup
  intro x
  cases Decidable.em (r = x)
  · simp_all
  · rw [Finmap.lookup_union_right]
    apply Eq.trans (b := none)
    · simp_all [Finmap.lookup_eq_none, eq_comm]
    · simp_all [Finmap.lookup_eq_none, eq_comm]
    simp_all [eq_comm]

theorem fresh_intro :
  STHoare p Γ
      ⟦⟧
      (.callBuiltin [] tp .fresh h![])
      (fun _ => ⟦⟧) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.fresh_intro (fun _ => SLP.entails_self)
  simp [SLP.entails_self, SLP.forall_right]

lemma eq (a b : Tp.denote p tp)
  (_ : BEq (Tp.denote p tp))
  (h1 : LawfulBEq (Tp.denote p tp))
  : (a == b) = true → a = b := h1.eq_of_beq


-- [TODO] BitVec should be a `Preorder` but it isn't?
lemma BitVec.le_refl {a : BitVec w} : a ≤ a := by
  cases a
  simp [BitVec.le_def]

-- [TODO] BitVec should be a `Preorder` but it isn't?
lemma BitVec.le_trans {a b c : BitVec w}: a ≤ b → b ≤ c → a ≤ c := by
  intros
  cases_type* BitVec
  simp only [BitVec.le_ofFin] at *
  apply _root_.le_trans <;> assumption

-- [TODO] BitVec should be a `Preorder` but it isn't?
lemma BitVec.le_of_lt {a b : BitVec w}: a < b → a ≤ b := by
  intros
  cases_type* BitVec
  simp only [BitVec.le_ofFin, BitVec.lt_ofFin] at *
  apply _root_.le_of_lt
  assumption

-- [TODO] BitVec should be a `Preorder` but it isn't?
lemma BitVec.le_or_lt (a b : BitVec w): a ≤ b ∨ b < a := by
  cases_type* BitVec
  simp only [BitVec.le_ofFin, BitVec.lt_ofFin] at *
  apply _root_.le_or_lt

lemma BitVec.not_lt {a b : BitVec w}: ¬ a < b ↔ b ≤ a := by
  cases_type* BitVec
  simp [BitVec.le_ofFin, BitVec.lt_ofFin] at *

theorem loopDone_intro : STHoare p Γ ⟦⟧ (.loop lo lo body) (fun _ => ⟦⟧) := by
  intro _ _ _
  apply Omni.loopDone
  apply BitVec.le_refl

theorem loopNext_intro {lo hi : U s} :
    lo < hi →
    STHoare p Γ P (body lo) (fun _ => Q) →
    STHoare p Γ Q (.loop (lo + 1) hi body) R →
    STHoare p Γ P (.loop lo hi body) R := by
  intro _ _ _ _ _ _
  apply Omni.loopNext
  · assumption
  apply letIn_intro
  all_goals tauto

lemma inv_congr  (Inv : (i : U s) → (lo ≤ i) → (i ≤ hi) → SLP (State p)) {i j hlo hhi} (hEq : i = j):
    Inv i hlo hhi = Inv j (hEq ▸ hlo) (hEq ▸ hhi) := by
  cases hEq
  rfl

lemma U.le_add_one_of_exists_lt {i : U s}  (h: i < j) : i ≤ i + 1 := by
  rcases i with ⟨⟨_, _⟩⟩
  rcases j with ⟨⟨_, _⟩⟩
  simp only [BitVec.lt_def, BitVec.toNat] at h
  simp only [BitVec.le_def, BitVec.add_def, BitVec.toNat, OfNat.ofNat, BitVec.ofNat, Fin.ofNat']
  rw [Nat.mod_eq_of_lt] <;>
    (rw [Nat.mod_eq_of_lt] <;> linarith)

lemma U.le_plus_one_of_lt {i j : U s} (h: i < j): i + 1 ≤ j := by
  rcases i with ⟨⟨_, _⟩⟩
  rcases j with ⟨⟨_, _⟩⟩
  simp only [BitVec.le_def, BitVec.lt_def, BitVec.add_def, BitVec.toNat, OfNat.ofNat, BitVec.ofNat, Fin.ofNat'] at *
  rw [Nat.mod_eq_of_lt] <;> (
    have : 1 % 2^s ≤ 1 := by apply Nat.mod_le;
    linarith
  )

theorem loop_inv_intro (Inv : (i : U s) → (lo ≤ i) → (i ≤ hi) → SLP (State p)) {body : U s → Expr (Tp.denote p) tp}:
    (∀i, (hlo: lo ≤ i) → (hhi: i < hi) → STHoare p Γ (Inv i hlo (BitVec.le_of_lt hhi)) (body i) (fun _ => Inv (i + 1) (BitVec.le_trans hlo (U.le_add_one_of_exists_lt hhi)) (U.le_plus_one_of_lt hhi))) →
    STHoare p Γ (∃∃h, Inv lo BitVec.le_refl h) (.loop lo hi body) (fun _ => ∃∃h, Inv hi h BitVec.le_refl) := by
  cases BitVec.le_or_lt lo hi with
  | inr =>
    intro _ H st h
    simp only [SLP.star, SLP.exists'] at h
    casesm* ∃ _, _, _∧_
    rw [←BitVec.not_lt] at *
    contradiction
  | inl =>
    rcases lo with ⟨lo, _⟩
    rcases hi with ⟨hi, _⟩
    have : hi = lo + (hi - lo) := by simp_all
    generalize h : hi - lo = d at *
    cases this
    intro h
    apply consequence (H₁ := Inv ⟨lo, by assumption⟩ (by simp) (by simp)) (Q₁ := fun _ => Inv ⟨lo + d, by assumption⟩ (by simp) (by simp))
    · intro st h
      cases h
      assumption
    · intro
      apply SLP.star_mono_r
      intro st h
      use (by simp)
    induction d generalizing lo with
    | zero =>
      apply ramified_frame_top loopDone_intro
      -- TODO this should be solved by the SL tactic
      simp only [SLP.true_star]
      apply SLP.forall_right
      intro _
      apply SLP.wand_intro
      simp
    | succ d ih =>
      apply loopNext_intro
      · simp
      · apply_assumption
        simp
      · have : BitVec.ofFin (Fin.mk lo (by assumption)) + 1 = BitVec.ofFin (Fin.mk (lo + 1) (by linarith)) := by
          simp [Fin.add_def]
          rw [Nat.mod_eq_of_lt]
          · linarith
        rw [inv_congr Inv this]
        simp_rw [this]
        have : BitVec.ofFin (Fin.mk (lo + (d + 1)) (by assumption)) = BitVec.ofFin (Fin.mk ((lo + 1) + d) (by linarith)) := by
          simp_arith
        rw [inv_congr Inv this]
        simp_rw [this]
        apply ih (lo := lo + 1) (Inv := fun i hlo hhi =>
          Inv i (by cases i; simp [Fin.le_def] at hlo; simp [Fin.le_def]; linarith)
                (by cases i; simp [Fin.le_def] at hhi; simp [Fin.le_def]; linarith))
        · simp
        · simp
        · intros
          apply h
          simp [*]

theorem iteTrue_intro :
    STHoare p Γ P mainBody Q →
    STHoare p Γ P (.ite true mainBody elseBody) Q := by
  tauto

theorem iteFalse_intro :
    STHoare p Γ P elseBody Q →
    STHoare p Γ P (.ite false mainBody elseBody) Q := by
  tauto

theorem ite_intro {cnd : Bool}
  (h₁ : cnd = true → STHoare p Γ P mainBody Q)
  (h₂ : cnd = false → STHoare p Γ P elseBody Q) :
  STHoare p Γ P (.ite cnd mainBody elseBody) Q := by
  unfold STHoare
  intros
  cases cnd
  . apply iteFalse_intro
    tauto
  . apply iteTrue_intro
    tauto

theorem skip_intro :
  STHoare p Γ ⟦⟧ (.skip) (fun v => v = ()) := by
  unfold STHoare
  intros
  simp only [SLP.true_star]
  unfold THoare
  intros
  constructor
  simp only
  . apply SLP.ent_star_top
    tauto

theorem lam_intro :
  STHoare p Γ ⟦⟧ (.lam argTps outTp lambdaBody)
    fun v => ∃∃ r, ⟦v = FuncRef.lambda r⟧ ⋆ [λr ↦ ⟨argTps, outTp, lambdaBody⟩] := by
  unfold STHoare THoare
  intros H st h
  constructor
  intros
  simp_all only [SLP.true_star, SLP.star_assoc]
  rename Ref => r
  generalize (⟨_, _, _⟩ : Lambda _) = lambda
  exists ⟨∅, Finmap.singleton r lambda⟩, st
  refine ⟨?_, ?_, ?_, ?_⟩
  . simp only [LawfulHeap.disjoint]
    refine ⟨?_, by simp_all⟩
    apply Finmap.disjoint_empty
  . simp only [State.union_parts, State.mk.injEq]
    refine ⟨by simp_all, ?_⟩
    have hd : Finmap.Disjoint st.lambdas (Finmap.singleton r lambda) := by
      rw [Finmap.Disjoint.symm_iff]
      apply Finmap.singleton_disjoint_of_not_mem (by assumption)
    simp only [Finmap.insert_eq_singleton_union, Finmap.union_comm_of_disjoint hd]
  . unfold State.lmbSingleton SLP.exists'
    exists r
    simp_all only [SLP.true_star]
  . apply SLP.ent_star_top
    tauto

theorem callLambda_intro {lambdaBody} {P : SLP $ State p}
  {Q : Tp.denote p outTp → SLP (State p)}
  {fnRef : Tp.denote p (.fn argTps outTp)}
  {hlam : STHoare p Γ P (lambdaBody args) Q} :
  STHoare p Γ (P ⋆ ∃∃ r, ⟦fnRef = FuncRef.lambda r⟧ ⋆ [λr ↦ ⟨argTps, outTp, lambdaBody⟩])
    (Expr.call argTps outTp fnRef args)
    (fun v => (Q v) ⋆ ∃∃ r, ⟦fnRef = FuncRef.lambda r⟧ ⋆ [λr ↦ ⟨argTps, outTp, lambdaBody⟩]) := by
  unfold STHoare THoare
  intros H st h
  have h₁ : ∃ r, fnRef = .lambda r := by
    simp only [SLP.star, SLP.exists', SLP.lift] at h
    tauto
  obtain ⟨r, _⟩ := h₁
  apply Omni.callLambda (ref := r) (lambdaBody := lambdaBody)
  · tauto
  . obtain ⟨st₁, st₂, _, _, ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, _⟩, _⟩, _⟩ := h
    subst_vars
    simp_all only [FuncRef.lambda.injEq]
    subst_vars
    simp_all only [LawfulHeap.empty_union, LawfulHeap.empty_disjoint]
    simp only [State.union_parts]
    rw [Finmap.lookup_union_left, Finmap.lookup_union_right]
    <;> simp only [State.lmbSingleton, LawfulHeap.disjoint, State.union_parts] at *
    . simp_all
    . apply Finmap.singleton_disjoint_iff_not_mem.mp
      simp_all only
      tauto
    . simp_all
  · apply STHoare.consequence_frame_left <;> tauto

theorem callDecl_intro {fnRef : Tp.denote p (.fn argTps outTp)}
    {href : H ⊢ ⟦fnRef = (.decl fnName kinds generics)⟧ ⋆ (⊤ : SLP $ State p)}
    {h_fn : (fnName, fn) ∈ Γ.functions}
    {hkc : fn.generics = kinds}
    {htci : (fn.body _ (hkc ▸ generics) |>.argTps) = argTps}
    {htco : (fn.body _ (hkc ▸ generics) |>.outTp) = outTp}
    {h_hoare: STHoare p Γ H (htco ▸ (fn.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q} :
    STHoare p Γ H (Expr.call argTps outTp fnRef args) Q := by
  unfold STHoare THoare
  intros
  have _ : fnRef = (.decl fnName kinds generics) := by
    rename_i h'
    apply SLP.extract_prop at h' <;> tauto
  apply Omni.callDecl <;> tauto


theorem callTrait_intro {impls : List $ Ident × Function} {fnRef : Tp.denote p (.fn argTps outTp)}
    (href : H ⊢  ⟦fnRef = (.trait selfTp traitName traitKinds traitGenerics fnName kinds generics)⟧ ⋆ (⊤ : SLP $ State p))
    (h_trait : TraitResolution Γ ⟨⟨traitName, traitKinds, traitGenerics⟩, selfTp⟩ impls)
    (h_fn : (fnName, fn) ∈ impls)
    (hkc : fn.generics = kinds)
    (htci : (fn.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (fn.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (fn.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q) :
    STHoare p Γ H
      (Expr.call argTps outTp fnRef args)
      Q := by
  unfold STHoare THoare
  intros
  have _ : fnRef = (.trait selfTp traitName traitKinds traitGenerics fnName kinds generics) := by
    rename_i h'
    apply SLP.extract_prop at h' <;> tauto
  apply Omni.callTrait <;> tauto

theorem fn_intro : STHoare p Γ ⟦⟧ (.fn argTps outTp r) fun v => v = r := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

end Lampe.STHoare
