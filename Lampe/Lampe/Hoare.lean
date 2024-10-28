import Lampe.Ast
-- import Lampe.Assignable
import Lampe.Tp
import Lampe.Data.Field
import Lampe.Tactic.IntroCases
import Lampe.Semantics
import Lampe.Syntax
import Lampe.State
import Lampe.SeparationLogic
import Mathlib

namespace Lampe

theorem omni_conseq:
    Omni p Γ st e Q →
    (∀ v, Q v → Q' v) →
    Omni p Γ st e Q' := by
  intro h
  induction h <;> try (
    intro
    constructor
    all_goals tauto
  )
  case callBuiltin =>
    cases_type Builtin
    tauto
  sorry

def THoare
    {tp : Tp}
    (p : Prime)
    (Γ : Env)
    (P : SLP p)
    (e : Expr (Tp.denote p) tp)
    (Q : (tp.denote p) → SLP p): Prop :=
  ∀st, P st → Omni p Γ st e (fun r => match r with
    | none => True
    | some (st', v) => Q v st')

theorem THoare.consequence {p Γ tp}  {e : Expr (Tp.denote p) tp} {H₁ H₂ Q₁ Q₂}:
    (H₂ ⊢ H₁) →
    THoare p Γ H₁ e Q₁ →
    (∀ v, Q₁ v ⊢ Q₂ v) →
    THoare p Γ H₂ e Q₂ := by
  unfold THoare
  intros
  apply omni_conseq
  · tauto
  rintro (_ | _) <;> tauto

theorem THoare.var_intro {p Γ P tp} {n : Tp.denote p tp} {Q: Tp.denote p tp → SLP p}:
    (P ⊢ Q n) →
    THoare p Γ P (Expr.var n) Q := by
  unfold THoare SLP.entails
  tauto

theorem THoare.assert_intro {p Γ P} {v : Bool} {Q : Unit → SLP p}:
    (v ⋆ P ⊢ Q ()) → THoare p Γ P (.call h![] [.bool] .unit (.builtin .assert) h![v]) Q := by
  unfold THoare
  intros
  constructor
  unfold Builtin.assert
  cases v
  · constructor
    simp
  · constructor; apply_assumption; simp_all

def STHoare p Γ P e (Q : Tp.denote p tp → SLP p) := ∀H, THoare p Γ (P ⋆ H) e (fun v => ((Q v) ⋆ H) ⋆ ⊤)

theorem frame : STHoare p Γ P e Q → STHoare p Γ (P ⋆ H) e (fun v => Q v ⋆ H) := by
  unfold STHoare
  intro h H'
  have := h (H ⋆ H')
  simp_all [SLP.star_assoc]

theorem consequence_top {p tp} {e : Expr (Tp.denote p) tp} {H₁ H₂} {Q₁ Q₂ : Tp.denote p tp → SLP p}:
    (H₁ ⊢ H₂) → (∀ v, Q₂ v ⋆ ⊤ ⊢ Q₁ v ⋆ ⊤) → STHoare p Γ H₂ e Q₂ → STHoare p Γ H₁ e Q₁ := by
  unfold STHoare
  intro hHs hQs hE H
  apply THoare.consequence ?_ (hE H) ?_
  · apply SLP.star_mono_r
    tauto
  · intro
    rw [SLP.star_assoc, SLP.star_assoc]
    conv in (occs := *) (H ⋆ ⊤) => rw [SLP.star_comm]
    rw [←SLP.star_assoc, ←SLP.star_assoc]
    apply SLP.star_mono_r
    apply_assumption

@[aesop unsafe 1%]
theorem ramified_frame_top {Q₁ Q₂ : Tp.denote p tp → SLP p}:
    STHoare p Γ H₁ e Q₁ →
    (H₂ ⊢ (H₁ ⋆ (∀∀v, Q₁ v -⋆ Q₂ v ⋆ ⊤))) →
    STHoare p Γ H₂ e Q₂ := by
  intro hST hHE
  apply consequence_top
  rotate_left
  rotate_left
  apply frame
  rotate_left
  assumption
  apply_assumption
  intro v
  apply SLP.entails_trans
  rw [SLP.star_assoc, SLP.star_comm, SLP.star_assoc]
  exact SLP.forall_star
  apply SLP.forall_left
  rw [SLP.star_comm, SLP.star_assoc, SLP.star_comm]
  apply SLP.entails_trans
  apply SLP.star_mono_r
  apply SLP.wand_cancel
  rw [SLP.star_assoc]
  simp
  tauto

theorem consequence_left {H₁ H₂ : SLP p}:
    STHoare p Γ H₁ e Q →
    (H₂ ⊢ H₁) →
    STHoare p Γ H₂ e Q := by
  intro hE h
  apply ramified_frame_top
  apply hE
  conv => lhs; rw [←SLP.star_true (H:=H₂)]
  apply SLP.star_mono
  · assumption
  · apply SLP.forall_right
    intro
    apply SLP.wand_intro
    simp

@[aesop safe 10]
theorem consequence_frame_left {H H₁ H₂ : SLP p} :
    STHoare p Γ H₁ e Q →
    (H ⊢ (H₁ ⋆ H₂)) →
    STHoare p Γ H e (fun v => Q v ⋆ H₂) := by
  intro hE h
  apply ramified_frame_top
  apply hE
  apply SLP.entails_trans
  exact h
  apply SLP.star_mono_l
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  rw [SLP.star_comm]
  apply SLP.ent_star_top

-- @[aesop safe 10]
-- theorem consequence_frame_right {H : SLP p} {Q₁ Q₂ : Tp.denote p tp → SLP p}:
--     STHoare p Γ H e Q₁ →
--     (∀ v, Q₁ v ⊢ Q₂ v ⋆ H₂ ⋆ ⊤) →
--     STHoare p Γ H e (fun v => Q v ⋆ H₂) := by
--   intro hE h
--   apply ramified_frame_top
--   apply hE
--   apply SLP.entails_trans
--   exact h
--   apply SLP.star_mono_l
--   apply SLP.forall_right
--   intro
--   apply SLP.wand_intro
--   rw [SLP.star_comm]
--   apply SLP.ent_star_top

@[aesop safe]
theorem var_intro :
    STHoare p Γ ⟦⟧ (Expr.var n) (fun v => v = n) := by
  intro
  apply THoare.var_intro
  simp

@[aesop safe]
theorem assert_intro {v:Bool}:
    STHoare p Γ
    ⟦⟧
    (.call (argTypes := [.bool]) h![] .unit (.builtin .assert) h![v])
    (fun _ => v) := by
  intro H
  apply THoare.assert_intro
  simp [←SLP.star_assoc]

theorem omni_frame {p Γ tp st₁ st₂} {e : Expr (Tp.denote p) tp} {Q}:
    Omni p Γ st₁ e Q →
    st₁.Disjoint st₂ →
    Omni p Γ (st₁ ∪ st₂) e (fun st => match st with
      | some (st', v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st'
      | none => Q none
    ) := by
  intro h
  induction h with
  | litField hq
  | litFalse hq
  | litTrue hq
  | var hq =>
    intro
    constructor
    repeat apply Exists.intro
    tauto
  | letIn _ _ hN ihE ihB =>
    intro
    constructor
    apply ihE
    assumption
    · intro _ _ h
      cases h
      casesm* ∃ _, _, _∧_
      subst_vars
      apply ihB
      assumption
      assumption
    · simp_all
  | callBuiltin hq =>
    cases_type Builtin
    tauto
  | callDecl _ _ _ _ _ ih =>
    intro
    constructor
    all_goals (try assumption)
    tauto
  | loopDone => sorry
  | loopNext => sorry

@[aesop safe]
theorem letIn_intro:
    STHoare p Γ P e₁ Q →
    (∀v, STHoare p Γ (Q v) (e₂ v) R) →
    STHoare p Γ P (Expr.letIn e₁ e₂) R := by
  unfold STHoare THoare
  intro he hb H
  intros
  constructor
  apply_assumption
  apply_assumption
  intro _ _ h
  simp only at h
  cases h
  casesm* ∃ _, _, _∧_
  subst_vars
  apply omni_conseq
  apply omni_frame
  apply_assumption
  apply_assumption
  apply_assumption
  intro v
  cases v with
  | none => simp
  | some v =>
    cases v
    simp only
    rintro ⟨_, _, _, _, h, _⟩
    rcases h with ⟨_, _, _, _, _, _⟩
    subst_vars
    apply Exists.intro
    apply Exists.intro
    apply And.intro
    rotate_left
    apply And.intro
    rotate_left
    apply And.intro
    assumption
    simp [SLP.top]
    rotate_left
    rotate_left
    rw [Finmap.union_assoc]
    intro _ h
    intro h₁
    cases Finmap.mem_union.mp h₁
    · simp only [Finmap.Disjoint] at *
      tauto
    · simp only [Finmap.Disjoint, Finmap.mem_union] at *
      tauto
  simp

nr_def weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

-- nr_def assert<>(x : bool) -> Unit {
--   #assert(x) : Unit;
-- }

nr_def assert2<>(x : bool, y: bool) -> Unit {
  #assert(x):Unit;
  #assert(y):Unit;
}

example : STHoare p Γ True (assert2.fn.body _ h![] h![a, b]) (fun _ => ⟦a ∧ b⟧) := by
  unfold assert2
  simp
  apply letIn_intro
  apply letIn_intro
  aesop
  intro
  apply ramified_frame_top
  apply assert_intro
  simp
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  apply SLP.pure_left
  intro h
  rw [h]
  apply SLP.ent_star_top
  intro
  apply letIn_intro
  apply ramified_frame_top
  apply var_intro
  simp
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  apply SLP.ent_star_top
  intro
  apply ramified_frame_top
  apply assert_intro
  aesop

nr_def simple_rw<>(x : bool) -> bool {
  let mut y = x;
  y
}

@[aesop safe]
theorem ref_intro:
    STHoare p Γ
    ⟦⟧
    (.call h![] [tp] tp.ref (.builtin .ref) h![v])
    (fun r => [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare THoare
  intro _ st _
  constructor
  constructor
  intro ref
  simp only
  intro
  unfold SLP.star
  use (st.insert ref ⟨tp, v⟩), ∅
  simp [Finmap.Disjoint.symm_iff, Finmap.disjoint_empty]
  exists (Finmap.singleton ref ⟨tp, v⟩), st
  simp_all [Finmap.singleton_disjoint_of_not_mem, Finmap.insert_eq_singleton_union, SLP.singleton]

@[aesop safe]
theorem readRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref] tp (.builtin .readRef) h![r])
    (fun v' => ⟦v' = v⟧ ⋆ [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare THoare
  intro _ st h
  rcases h with ⟨_, s, _, _, hl, hr⟩
  cases hl
  subst_vars
  constructor
  constructor
  · simp; rfl
  · simp only [SLP.true_star, SLP.star_assoc]
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro rfl
    apply And.intro
    · simp [SLP.singleton]
    · apply Exists.intro s
      apply Exists.intro ∅
      simp_all
      apply Finmap.Disjoint.symm
      simp only [Finmap.disjoint_empty]
    · assumption

@[aesop safe]
theorem writeRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref, tp] .unit (.builtin .writeRef) h![r, v'])
    (fun _ => [r ↦ ⟨tp, v'⟩]) := by sorry

example : STHoare p Γ ⟦⟧ (simple_rw.fn.body _ h![] h![x]) fun v => v = x := by
  simp only [simple_rw, Lampe.Expr.letMutIn]
  apply letIn_intro
  apply letIn_intro
  apply var_intro
  intro
  apply ramified_frame_top
  apply ref_intro
  · simp
    apply SLP.forall_right
    intro
    apply SLP.wand_intro
    apply SLP.pure_left
    intro
    subst_vars
    apply SLP.ent_star_top
  intro
  apply ramified_frame_top
  apply readRef_intro
  rotate_left
  apply SLP.star_mono_l'
  apply SLP.forall_right
  intro
  apply SLP.wand_intro
  simp
  apply SLP.star_mono_l
  apply SLP.entails_top

nr_def simple_muts<>(x : Field) -> Field {
  let mut y = x;
  let mut z = x;
  z = z;
  y = z;
  y
}

def simple_muts_anf_body : (f : rep .field) → Expr rep .field := fun x =>
  .letIn (.call h![] [.field] (.ref .field) (.builtin .ref) h![x]) fun y =>
  .letIn (.call h![] [.field] (.ref .field) (.builtin .ref) h![x]) fun z =>
  .letIn (.call h![] [.ref .field] (.field) (.builtin .readRef) h![z]) fun zVal =>
  .letIn (.call h![] [.ref .field, .field] (.unit) (.builtin .writeRef) h![z, zVal]) fun _ =>
  .letIn (.call h![] [.ref .field, .field] (.unit) (.builtin .writeRef) h![y, zVal]) fun _ =>
  .letIn (.call h![] [.ref .field] (.field) (.builtin .readRef) h![y]) fun yVal =>
  .var yVal

example : STHoare p Γ ⟦⟧ (simple_muts_anf_body x) fun v => v = x := by sorry
  -- simp only [simple_muts_anf_body]
  -- apply letIn_intro
  -- apply ref_intro
  -- intro
  -- apply letIn_intro
  -- apply consequence_frame_left ref_intro
  -- · simp
  --   apply SLP.entails_self
  -- intro
  -- apply letIn_intro
  -- apply consequence_frame_left readRef_intro
  -- · apply SLP.star_mono_l
  --   apply SLP.entails_self
  -- intro
  -- apply letIn_intro
  -- apply consequence_frame_left writeRef_intro
  -- · rw [SLP.star_assoc, SLP.star_comm, SLP.star_assoc]
  --   apply SLP.star_mono_l
  --   apply SLP.entails_self
  -- intro
  -- apply letIn_intro
  -- apply consequence_frame_left writeRef_intro
  -- · rw [SLP.star_comm, SLP.star_assoc]
  --   apply SLP.star_mono_l
  --   apply SLP.entails_self
  -- intro
  -- apply letIn_intro
  -- apply consequence_frame_left readRef_intro
  -- · apply SLP.star_mono_l
  --   apply SLP.entails_self
  -- intro
  -- apply ramified_frame_top var_intro
  -- · simp
  --   apply SLP.forall_right
  --   intro
  --   apply SLP.wand_intro
  --   rw [SLP.star_comm]
  --   apply SLP.pure_left
  --   intro
  --   rw [SLP.star_assoc]
  --   apply SLP.pure_left
  --   intro
  --   rw [SLP.star_comm, SLP.star_assoc]
  --   apply SLP.pure_left
  --   intro
  --   apply SLP.pure_right
  --   subst_vars; rfl
  --   apply SLP.entails_top

def writeRef {rep tp} (ref : rep $ Tp.ref tp) (val : rep tp): Expr rep .unit :=
  .call h![] [.ref tp, tp] .unit (.builtin .writeRef) h![ref, val]

def fresh tp: Expr rep tp :=
  .call h![] [] tp (.builtin .fresh) h![]

def assert (v : rep .bool): Expr rep .unit :=
  .call h![] [.bool] .unit (.builtin .assert) h![v]

def ref {rep tp} (val : rep tp): Expr rep (Tp.ref tp) :=
  .call h![] [tp] (Tp.ref tp) (.builtin .ref) h![val]

def readRef {rep tp} (ref : rep $ Tp.ref tp): Expr rep tp :=
  .call h![] [.ref tp] tp (.builtin .readRef) h![ref]

def sliceLen {rep tp} (slice : rep $ Tp.slice tp): Expr rep (.u 32) :=
  .call h![] [Tp.slice tp] (.u 32) (.builtin .sliceLen) h![slice]

def slicePushBack {rep tp} (slice : rep $ Tp.slice tp) (val : rep tp): Expr rep (Tp.slice tp) :=
  .call h![] [Tp.slice tp, tp] (Tp.slice tp) (.builtin .slicePushBack) h![slice, val]

def sliceIndex {rep tp} (slice : rep $ Tp.slice tp) (i : rep (.u 32)): Expr rep tp :=
  .call h![] [Tp.slice tp, .u 32] tp (.builtin .sliceIndex) h![slice, i]

def eqF {rep} (x y : rep .field): Expr rep .bool :=
  .call h![] [.field, .field] .bool (.builtin .eq) h![x, y]

def sliceAppendBody {P tp} (self that : Tp.denote P (.slice tp)): Expr (Tp.denote P) (.slice tp) :=
  .letIn (ref self) fun self =>
  .letIn (sliceLen that) fun thatLen =>
  .letIn (.loop 0 thatLen fun i =>
    .letIn (readRef self) fun selfVal =>
    .letIn (sliceIndex that i) fun thatVal =>
    .letIn (slicePushBack selfVal thatVal) fun pushed =>
    writeRef self pushed
  ) fun _ => readRef self

theorem fresh_intro:
    STHoare P Γ ⟦⟧ (fresh tp) (fun _ => ⟦⟧) := by
  intro
  unfold fresh
  unfold THoare
  intro st _
  constructor
  constructor
  intro
  simp only
  use st, ∅
  rw [Finmap.union_empty, Finmap.Disjoint.symm_iff]
  apply And.intro (by apply Finmap.disjoint_empty)
  apply And.intro rfl
  simp_all

theorem eqF_intro {a b : Tp.denote P .field}:
    STHoare P Γ ⟦⟧ (eqF a b) fun v => v = (a = b) := by
  unfold eqF
  intro H
  intro st hp
  constructor
  constructor
  simp_all
  exists st, ∅
  rw [Finmap.Disjoint.symm_iff]
  simp_all [Finmap.disjoint_empty]


theorem sliceLen_intro {slice : Tp.denote P (.slice tp)}:
    STHoare P Γ ⟦⟧ (sliceLen slice) fun v => v = List.length slice ∧ slice.length < 2^32 := by sorry

theorem sliceIndex_intro {slice : Tp.denote P (.slice tp)} {i : U 32}:
    STHoare P Γ ⟦⟧ (sliceIndex slice i) fun v => some v = slice.get? i := by sorry

theorem slicePushBack_intro {slice : Tp.denote P (.slice tp)} {val : Tp.denote P tp}:
    STHoare P Γ ⟦⟧ (slicePushBack slice val) fun v => v = slice ++ [val] := by sorry

theorem loop_intro {a b : U s} {H : SLP p} {Q : Unit → SLP p}:
    (a ≥ b → (H ⊢ Q ())) →
    (a < b → STHoare p Γ H (.letIn (body a) fun _ => .loop (a + 1) b body) Q) →
    STHoare p Γ H (.loop a b body) Q := by sorry

theorem loop_intro' {a b : U s} {H : SLP p} {Q : Unit → SLP p}:
    (a ≥ b → (H ⊢ Q ())) →
    (a < b → STHoare p Γ H ((Expr.loop a (b-1) body).letIn fun _ => .letIn (body b) fun _ => .skip) Q) →
    STHoare p Γ H (.loop a b body) Q := by sorry

lemma U.le_add_one_of_exists_lt {i : U s}  (h: i < j) : i ≤ i + 1 := by
  cases i
  cases j
  simp only [Fin.lt_def] at h
  simp only [Fin.add_def, Fin.le_def]
  rw [Nat.mod_eq_of_lt]
  linarith
  rw [Fin.val_one', Nat.mod_eq_of_lt]
  linarith
  linarith

lemma U.le_plus_one_of_lt {i j : U s} (h: i < j): i + 1 ≤ j := by
  cases i
  cases j
  simp only [Fin.lt_def, Fin.le_def, Fin.add_def, Fin.val_one'] at *
  rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt]
  linarith
  linarith
  rw [Nat.mod_eq_of_lt]
  linarith
  linarith

theorem loop_inv_intro (Inv : (i : U s) → (lo ≤ i) → (i ≤ hi) → SLP p):
    (h: lo ≤ hi) →
    (∀i, (hlo: lo ≤ i) → (hhi: i < hi) → STHoare p Γ (Inv i hlo (le_of_lt hhi)) (body i) (fun _ => Inv (i + 1) (le_trans hlo (U.le_add_one_of_exists_lt hhi)) (U.le_plus_one_of_lt hhi))) →
    STHoare p Γ (Inv lo (le_refl _) h ) (.loop lo hi body) (fun _ => Inv hi h (le_refl _)) := by
  sorry
  -- rcases lo with ⟨lo, _⟩
  -- rcases hi with ⟨hi, _⟩
  -- intro h
  -- simp only [Fin.le_def] at h
  -- generalize h' : hi - lo = d
  -- have : hi = lo + d := by
  --   rw [←h']
  --   rw [Nat.add_sub_of_le h]
  -- cases this
  -- clear h'
  -- have Inv_rw {a b h₁ h₂} (h : a = b): Inv a h₁ h₂ = Inv b (h ▸ h₁) (h ▸ h₂) := by
  --   funext
  --   rw [eq_iff_iff]
  --   apply Iff.intro
  --   · intro h'; exact (h ▸ h')
  --   · intro h'; exact (h.symm ▸ h')

  -- induction d generalizing lo with
  -- | zero =>
  --   intro
  --   apply loop_intro
  --   · simp [SLP.entails_self]
  --   · intro h; simp at h
  -- | succ d ih =>
  --   intro hp
  --   apply loop_intro
  --   · intro h; simp at h
  --   · intro h; simp only [Fin.lt_def] at h;
  --     apply letIn_intro
  --     · apply hp
  --       simp
  --     · intro
  --       have : Fin.mk (n := 2^s) lo (by assumption) + 1 = Fin.mk (lo + 1) (by linarith) := by
  --         simp only [Fin.add_def, Fin.val_one']
  --         ext
  --         simp only
  --         rw [Nat.mod_eq_of_lt]
  --         · simp
  --           by_contra
  --           have : s = 0 := by simp_all
  --           cases this
  --           simp_all
  --           have : lo = 0 := by apply Nat.lt_one_iff.mp; assumption
  --           cases this
  --           linarith
  --         · rw [Nat.mod_eq_of_lt]
  --           linarith
  --           linarith
  --       rw [Inv_rw this]
  --       conv => arg 4; arg 1; rw [this]
  --       have : Fin.mk (n := 2^s) (lo + (d + 1)) (by assumption) = Fin.mk ((lo + 1) + d) (by linarith) := by
  --         simp_arith
  --       rw [Inv_rw this]
  --       conv => arg 4; arg 2; rw [this]
  --       apply ih (Inv := fun i hlo hhi => Inv i (by simp [Fin.le_def, Fin.lt_def] at *; linarith) (by simp [Fin.le_def, Fin.lt_def] at *; linarith))
  --       · simp
  --       · simp
  --       · intros; rename_i h; cases h; rfl
  --       · intros
  --         apply_assumption
  --         simp [Fin.lt_def, Fin.le_def] at *
  --         linarith

theorem STHoare.pure_left : (P → STHoare p Γ H e Q) → STHoare p Γ (⟦P⟧ ⋆ H) e Q := by
  intro
  unfold STHoare
  intro
  unfold THoare
  intro _ h
  rw [SLP.star_assoc] at h
  rcases h with ⟨_, _, _, _, hP, _⟩
  cases hP
  subst_vars
  apply_assumption
  simp_all
  simp_all

-- macro "steps" : tactic => `(tactic|
--   try (first
--   | apply letIn_intro; (on_goal 2 => intro; try steps)
--   )
-- )

-- example {self that : Tp.denote P (.slice tp)} : STHoare P Γ ⟦⟧ (sliceAppendBody self that) fun v => v = self ++ that := by
--   simp only [sliceAppendBody]
--   steps

--   apply letIn_intro; (on_goal 2 => intro; steps); (on_goal 1 => steps);
--   steps



  -- steps

/-
  apply letIn_intro ref_intro
  intro selfRef
  apply letIn_intro
  apply consequence_frame_left sliceLen_intro
  · aesop
  intro
  apply STHoare.pure_left
  intro_cases
  subst_vars
  apply letIn_intro
  apply consequence_frame_left
  apply loop_inv_intro (fun i _ _ => [selfRef ↦ ⟨.slice tp, self ++ that.take i.val⟩]) (by simp)
  · intro i _ _
    rcases i with ⟨i, _⟩
    have : i + 1 < 2^32 := by
      simp_all [Fin.lt_def, Nat.mod_eq_of_lt]
      linarith
    apply letIn_intro
    apply readRef_intro
    intro selfV
    apply letIn_intro
    apply consequence_frame_left sliceIndex_intro
    · simp; aesop
    intro
    apply STHoare.pure_left
    intro
    apply STHoare.pure_left
    intro
    subst_vars
    apply letIn_intro
    apply consequence_frame_left slicePushBack_intro
    · simp; apply SLP.entails_self
    intro
    apply STHoare.pure_left
    rintro rfl
    simp_all [Fin.lt_def, Fin.add_def, Nat.mod_eq_of_lt, List.take_succ]
    apply writeRef_intro
  · simp
    apply SLP.star_mono_l'
    apply SLP.entails_self
  · intro
    apply ramified_frame_top readRef_intro
    · apply SLP.star_mono_l
      apply SLP.forall_right; intro
      apply SLP.wand_intro
      apply SLP.pure_left; intro
      apply SLP.pure_left; rintro rfl
      simp_all [Nat.mod_eq_of_lt, SLP.entails_top]
-/
