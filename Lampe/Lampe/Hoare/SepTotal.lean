import Lampe.Ast
import Lampe.Hoare.Total
import Lampe.Semantics
import Lampe.Tactic.SL
import Lampe.Tp

namespace Lampe

/--
A Hoare triple where the states must be valid under separation logic.

A Hoare triple `{Γ} {P} e {λv ↦ Q v}` means that if the state of the program satisfies the
pre-condition `P`, then the expression `e` terminates and evaluates to `v` in the environment `Γ`
such that the postcondition `Q v` holds.

Note that the evaluation of `e` to an error is still termination. Consequently, we interpret
`{P} e {λv ↦ Q v}` to mean that if `P` holds, then `e` terminates and either:

1. Fails
2. Successfully evaluates to `v` such that `Q v` holds.

This is logically equivalent to stating that if `P` holds, then `e` terminates, and that `Q v` holds
if `e` **succeeds** and evaluates to `v`. This means that our triples are _partial_ with respect to
failure, and _total_ with respect to termination of the program.

A reasonable intuition for how this works is the lens of "knowledge discovery". For example, if the
operation `a + b` on `u32` succeeds, then we know that it evaluates to `v = a + b` **and** that
`a + b < 2^32` (that no overflow has happened). Under such circumstances, we would define the
postcondition such that `Q = λv ↦ (v = a + b) ∧ (a + b < 2^32)`.

Note that we have the `⋆ ⊤` term in our postcondition here. This term is able to subsume evidence
that goes unused, thereby turning the separation logic from linear to affine. This is necessary to
model programs that do not have explicit deallocation semantics, like lean.
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

abbrev STHoarePureBuiltin' p (Γ : Env)
  {a : A}
  {sgn: A → List Tp × Tp}
  {desc : {p : Prime} → (a : A) → (args : HList (Tp.denote p) (sgn a).fst) → (Tp.denote p (sgn a).snd)}
  (args : HList (Tp.denote p) (sgn a).fst) : Prop :=
    STHoare p Γ ⟦⟧
      (.callBuiltin (sgn a).fst (sgn a).snd (@Builtin.newGenericPureBuiltin A sgn (@fun p a args => ⟨True, fun _ => @desc p a args⟩)) args)
      (fun v => v = desc a args)

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


theorem litU_intro: STHoare p Γ ⟦⟧ (.litNum (.u s) n) fun v => v = n := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem litField_intro: STHoare p Γ ⟦⟧ (.litNum .field n) fun v => v = n := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem litStr_intro: STHoare p Γ ⟦⟧ (.litStr u s) fun v => v = s := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem fmtStr_intro : STHoare p Γ ⟦⟧ (.fmtStr u tps s) fun v => v = s := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem litFalse_intro: STHoare p Γ ⟦⟧ (.litNum .bool 0) fun v => v = false := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem litTrue_intro: STHoare p Γ ⟦⟧ (.litNum .bool 1) fun v => v = true := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem litUnit_intro: STHoare p Γ ⟦⟧ (.litNum .unit n) fun v => v = unit := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

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
  apply le_or_gt

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

lemma inv_congr {h₁ h₂ : α → Prop} (Inv : (i : α) → h₁ i → h₂ i → SLP (State p)) {i j hlo hhi} (hEq : i = j):
    Inv i hlo hhi = Inv j (hEq ▸ hlo) (hEq ▸ hhi) := by
  cases hEq
  rfl

lemma U.le_add_one_of_exists_lt {i : U s}  (h: i < j) : i ≤ i + 1 := by
  rcases i with ⟨⟨_, _⟩⟩
  rcases j with ⟨⟨_, _⟩⟩
  simp only [BitVec.lt_def, BitVec.toNat] at h
  simp only [BitVec.le_def, BitVec.add_def, BitVec.toNat, OfNat.ofNat, BitVec.ofNat, Fin.ofNat]
  rw [Nat.mod_eq_of_lt] <;>
    (rw [Nat.mod_eq_of_lt] <;> linarith)

lemma U.le_plus_one_of_lt {i j : U s} (h: i < j): i + 1 ≤ j := by
  rcases i with ⟨⟨_, _⟩⟩
  rcases j with ⟨⟨_, _⟩⟩
  simp only [BitVec.le_def, BitVec.lt_def, BitVec.add_def, BitVec.toNat, OfNat.ofNat, BitVec.ofNat, Fin.ofNat] at *
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
          simp +arith +decide
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

theorem SLP.entails_of_eq [LawfulHeap α] {P Q : SLP α} (h : P = Q) : P ⊢ Q := by
  cases h
  apply SLP.entails_self

theorem loop_inv_intro' {lo hi : U s} (Inv : (i : Nat) → (lo.toNat ≤ i) → (i ≤ hi.toNat) → SLP (State p)) {body : U s → Expr (Tp.denote p) tp}:
    (∀(i:Nat), (hlo: lo.toNat ≤ i) → (hhi: i < hi.toNat) → STHoare p Γ (Inv i hlo (by linarith)) (body i) (fun _ => Inv (i + 1) (by linarith) (by linarith))) →
    STHoare p Γ (∃∃h, Inv lo.toNat BitVec.le_refl h) (.loop lo hi body) (fun _ => ∃∃h, Inv hi.toNat h BitVec.le_refl) := by
  intro hinv
  apply STHoare.ramified_frame_top
  apply loop_inv_intro fun i _ _ => Inv i.toNat (by rw [←BitVec.le_def]; assumption) (by rw [←BitVec.le_def]; assumption)
  · intro i hlo hhi
    have : i = ↑i.toNat := by simp
    apply consequence

    case h_hoare =>
      rw [this]
      apply hinv
      · rw [←BitVec.le_def]; assumption
      · rw [←BitVec.lt_def]; assumption
    · apply SLP.entails_self
    · intro
      have : BitVec.toNat (i + 1) = i.toNat + 1 := by
        simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod]
        rw [Nat.mod_eq_of_lt]
        simp only [BitVec.lt_def] at hhi
        apply Nat.lt_of_lt_of_le (m := hi.toNat + 1) (by linarith)
        apply Nat.succ_le_of_lt
        cases hi
        simp
      apply SLP.star_mono
      · apply SLP.entails_of_eq
        apply inv_congr (Inv:=Inv)
        rw [this]
      · apply SLP.entails_self
  · conv => lhs; rw [←SLP.star_true (H := SLP.exists' _)]
    apply SLP.star_mono
    · apply SLP.exists_intro_l
      intro hp
      apply SLP.exists_intro_r
      apply SLP.entails_self
      apply BitVec.le_def.mpr hp
    · apply SLP.forall_right
      intro _
      apply SLP.wand_intro
      simp
      apply SLP.ent_star_top

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

theorem constU_intro: STHoare p Γ ⟦⟧ (.constU c) fun v => v = c := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

theorem constFp_intro: STHoare p Γ ⟦⟧ (.constFp c) fun v => v = c := by
  unfold STHoare THoare
  intro H st hp
  constructor
  simp only
  apply SLP.ent_star_top
  assumption

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
    fun v => ∃∃ (h:v.isLambda), [λ (v.asLambda h) ↦ ⟨argTps, outTp, lambdaBody⟩] := by
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
    refine ⟨?_, ?_⟩
    . apply Finmap.disjoint_empty
    . apply Finmap.singleton_disjoint_of_not_mem (by tauto)
  . simp only [State.union_parts, State.mk.injEq]
    refine ⟨by simp_all, ?_⟩
    have hd : Finmap.Disjoint st.lambdas (Finmap.singleton r lambda) := by
      rw [Finmap.Disjoint.symm_iff]
      apply Finmap.singleton_disjoint_of_not_mem (by assumption)
    simp only [Finmap.insert_eq_singleton_union, Finmap.union_comm_of_disjoint hd]
  . unfold State.lmbSingleton SLP.exists'
    simp [FuncRef.isLambda]
    rfl
  . apply SLP.ent_star_top
    tauto

theorem callLambda_intro' {lambdaBody} {P : SLP $ State p}
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


lemma FuncRef.lambda_asLambda {f : FuncRef a o} {h} : FuncRef.lambda (FuncRef.asLambda f h) = f := by
  unfold FuncRef.isLambda at h
  split at h
  · rfl
  · contradiction

theorem callLambda_intro {lambdaBody} {P : SLP $ State p}
  {Q : Tp.denote p outTp → SLP (State p)}
  {fnRef : Tp.denote p (.fn argTps outTp)}
  {hlam : STHoare p Γ P (lambdaBody args) Q} :
  STHoare p Γ ((∃∃ h, [λfnRef.asLambda h ↦ ⟨argTps, outTp, lambdaBody⟩]) ⋆ P)
    (Expr.call argTps outTp fnRef args)
    (fun v => (∃∃ h, [λfnRef.asLambda h ↦ ⟨argTps, outTp, lambdaBody⟩]) ⋆ Q v) := by
  apply STHoare.consequence (h_hoare := callLambda_intro' (P := P) (Q := Q) (hlam := hlam))
  · rw [SLP.star_comm]
    apply SLP.star_mono_l
    apply SLP.exists_intro_l
    intro h
    apply SLP.exists_intro_r (a := fnRef.asLambda h)
    simp [FuncRef.lambda_asLambda]
    apply SLP.entails_self
  · intro
    apply SLP.star_mono_r
    rw [SLP.star_comm]
    apply SLP.star_mono_r
    apply SLP.exists_intro_l
    intro r
    apply SLP.pure_left
    rintro rfl
    apply SLP.exists_intro_r
    apply SLP.entails_self
    rfl

theorem callDecl_intro {fnRef : Tp.denote p (.fn argTps outTp)}
    {href : H ⊢ ⟦fnRef = (.decl fnName kinds generics)⟧ ⋆ (⊤ : SLP $ State p)}
    {h_fn : ⟨fnName, func⟩ ∈ Γ.functions}
    {hkc : func.generics = kinds}
    {htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps}
    {htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp}
    {h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q} :
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
    (h_fn : (fnName, func) ∈ impls)
    (hkc : func.generics = kinds)
    (htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) Q) :
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

/--
A given theorem on a Hoare Triple is valid for any environment Γ₂ that contains the environment Γ₁
for which the theorem was originally proven.

In detail:

- `p` is the value of the field prime under which the proof should hold.
- `Γ₁` is the "inner" environment, namely the one for which a proof of the Hoare triple already
  exists, while `Γ₂` is the "outer" environment, the one for which we want our existing proof to
  hold.
- `pre` is the precondition for our Hoare triples, namely the state in which our program is before
  executing `expr`.
- `expr` is the program expression to be "executed" in both cases.
- `post` is the postcondition for our Hoare triples, namely the state in which our program will end
  up if `expr` evaluates.

See the documentation for `STHoare` for more detail.
-/
theorem is_mono
    {p : Prime}
    {Γ₁ Γ₂ : Env}
    {pre : SLP (State p)}
    {expr : Expr (Tp.denote p) tp}
    {post : Tp.denote p tp → SLP (State p)}
    (inner_sub_outer : Γ₁ ⊆ Γ₂)
  : STHoare p Γ₁ pre expr post → STHoare p Γ₂ pre expr post := by
  unfold STHoare THoare
  intros
  apply Omni.is_mono inner_sub_outer
  repeat apply_assumption

end Lampe.STHoare
