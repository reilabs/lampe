import Lampe
import Lampe.Assignable.Unifs
import Lean

open Lean Elab.Tactic Parser.Tactic Lean.Meta
open Lampe

namespace Lampe.Assignable

def AssignableWithState {tp} (p : Prime) (Γ : Env) (e : Expr (Tp.denote p) tp) (preState postState : State p) (result : tp.denote p) :=
  ¬Omni p Γ preState e (fun r => r ≠ (postState, result))

def AssignableMain {tp} (p : Prime) (Γ : Env) (e : Expr (Tp.denote p) tp) (result : tp.denote p) :=
  ∃postState, AssignableWithState p Γ e (State.mk default default) postState result

theorem AssignableWithState.var:
    AssignableWithState p Γ (.var v) state state v := by
  intro hp
  cases hp
  simp_all

theorem AssignableWithState.callDecl {fnRef} {func : Function}
    (hfn_ref: fnRef = (.decl fnName kinds generics))
    (hpfunique: ∀ func', ⟨fnName, func'⟩ ∈ Γ.functions → func' = func)
    (hkc : func.generics = kinds)
    (htci : (func.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp)
    (hfuncCorr : AssignableWithState p Γ (htco ▸ (func.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) pre post res):
    AssignableWithState p Γ (Expr.call argTps outTp fnRef args) pre post res := by
  intro hp
  cases hfn_ref
  cases hp
  · rename FuncRef.decl _ _ _ = _ => h
    cases h
  · rename FuncRef.decl _ _ _ = _ => h
    cases h
  rename Function => fn₁
  casesm FuncRef.decl _ _ _ = _
  have : fn₁ = func := by
    apply hpfunique
    assumption
  cases this
  apply hfuncCorr
  assumption

theorem AssignableWithState.letIn
    (h1 : AssignableWithState p Γ e pre post v)
    (h2 : AssignableWithState p Γ (b v) post post' res):
    AssignableWithState p Γ (Expr.letIn e b) pre post' res := by
  intro hp
  cases hp
  apply h2
  apply_assumption
  by_contra
  apply h1
  apply Omni.consequence
  assumption
  intros
  rintro rfl
  contradiction

theorem AssignableWithState.fieldLit:
    AssignableWithState p Γ (Expr.litNum .field n) state state n := by
  intro hp
  cases hp
  contradiction

theorem AssignableWithState.genericPureBuiltin_intro {A} {a : A}
    {sgn : A → List Tp × Tp}
    {desc : {p : Prime}
      → (a : A)
      → (args : HList (Tp.denote p) (sgn a).fst)
      → (h : Prop) × (h → (Tp.denote p (sgn a).snd))}
    {args : HList (Tp.denote p) aTps}
    (hAUniq : ∀ a', sgn a' = (aTps, outTp) → a' = a)
    (hATps : aTps = (sgn a).fst)
    (hOTp : outTp = (sgn a).snd)
    (h : (desc a $ hATps ▸ args).fst):
    AssignableWithState p Γ
      (Expr.callBuiltin aTps outTp (Builtin.newGenericPureBuiltin sgn desc) args)
      st st (hOTp ▸ (desc a $ hATps ▸ args).snd h) := by
  intro hp
  unfold Builtin.newGenericPureBuiltin at hp
  cases hp
  rename_i hp
  simp only at hp
  cases hp
  · rename_i hp
    rename A => a'
    simp [mapToValHeapCondition] at hp
    have : a' = a := hAUniq _ rfl
    cases this
    contradiction
  · rename A => a'
    have : a' = a := hAUniq _ rfl
    cases this
    contradiction

theorem AssignableWithState.mkSlice_intro:
    AssignableWithState p env
      (Expr.callBuiltin (List.replicate n tp) tp.slice Builtin.mkSlice args)
      st st (args.toList rfl) := by
  apply AssignableWithState.genericPureBuiltin_intro (a := (n, tp))
  · simp
    intros
    tauto
  · simp
  · simp
  · simp

-- theorem AssignableWithState.ref_intro


noir_def std::slice::for_each<T: Type, Env: Type>(self: Slice<T>, f: λ(T) -> Unit) -> Unit := {
  let ζi0 = self;
  for ζi1 in (0: u32) .. (#_arrayLen returning u32)(ζi0) do {
    let elem = (#_sliceIndex returning T)(ζi0, (#_cast returning u32)(ζi1));
    {
      (f as λ(T) -> Unit)(elem);
      #_skip
    }
  };
  #_skip
}

noir_def std::slice::test::for_each_example<>() -> Unit := {
  let a = (#_mkSlice returning Slice<Field>)((1: Field), (2: Field), (3: Field));
  let mut b = (#_mkSlice returning Slice<Field>)();
  let b_ref = (#_ref returning & Slice<Field>)(b);
  (std::slice::for_each<Field, Tuple<& Slice<Field> > > as λ(Slice<Field>, λ(Field) -> Unit) -> Unit)(a, (fn(a: Field): Unit := {
    (*b_ref: Slice<Field>) = (#_slicePushBack returning Slice<Field>)((#_readRef returning Slice<Field>)(b_ref), (#_fMul returning Field)(a, (2: Field)));
    #_skip
  }));
  (#_assert returning Unit)(((Slice<Field> as std::cmp::Eq<>)::eq<> as λ(Slice<Field>, Slice<Field>) -> bool)(b, (#_mkSlice returning Slice<Field>)((2: Field), (4: Field), (6: Field))));
  #_skip
}

def env := Env.mk [«std::slice::for_each», «std::slice::test::for_each_example»] []

partial def solve (goal : MVarId): TacticM (List MVarId) := do
  let target ← goal.instantiateMVarsInType
  let_expr AssignableWithState tp p Γ e pre post res ← target
    | throwError "Goal is not of the form AssignableWithState p Γ e pre post res"
  match_expr e with
  | Expr.letIn _ _ _ e b =>
    let eGoal :: bGoal :: impls ← goal.apply (.const ``AssignableWithState.letIn [])
      | throwError "Failed to apply letIn"
    let eGoals ← try solve eGoal catch _ => return [eGoal, bGoal] ++ impls
    let bGoals ← try solve bGoal catch _ => return eGoals ++ [bGoal] ++ impls
    return eGoals ++ bGoals ++ impls
  | Expr.litNum _ tp n => match_expr tp with
    | Tp.field =>
      let impl ← goal.apply (.const ``AssignableWithState.fieldLit [])
      return impl
    | _ => throwError "No applicable rules"
  | Expr.callBuiltin _ _ _ b _ =>
    match_expr b with
    | Builtin.mkSlice =>
      let impl ← goal.apply (.const ``AssignableWithState.mkSlice_intro [])
      return impl
    | _ => throwError "No applicable rules"
  | _ => throwError "No applicable rules"

elab "crush" : tactic => do
  let goal ← getMainGoal
  replaceMainGoal (← solve goal)

-- unif_hint (p : Prime) (tp tp' : Tp) where
--   Tp.slice tp' =?= tp
--   ⊢ Tp.denote p tp =?= List (Tp.denote p tp')


example : AssignableMain p env («std::slice::test::for_each_example».call h![] h![]) () := by
  apply Exists.intro
  apply AssignableWithState.callDecl
  · rfl
  · simp [env]
    rintro _ (h | h)
    · apply_fun FunctionDecl.name at h
      conv at h => congr <;> whnf
      simp at h
    · apply_fun FunctionDecl.fn at h
      conv at h => congr <;> whnf
      cases h
      rfl
  rotate_left
  · rfl
  · rfl
  · rfl
  rotate_left
  simp only
  crush
