import Lampe
import Lampe.Assignable.Unifs
import Lean

open Lean Elab.Tactic Parser.Tactic Lean.Meta
open Lampe

namespace Lampe.Assignable

structure CState (p : Prime) where
  vals : Array (AnyValue p)
  lambdas : Array (Lambda (Tp.denote p))

instance : Inhabited (CState p) where
  default := ⟨default, default⟩

theorem CState.default_def : default = @CState.mk p #[] #[] := rfl

def CState.toState (self : CState p) : State p :=
  State.mk
    (self.vals.toList.zipIdx.map (fun (v, i) => Sigma.mk (Ref.mk i) v) |>.toFinmap)
    (self.lambdas.toList.zipIdx.map (fun (l, i) => Sigma.mk (Ref.mk i) l) |>.toFinmap)

def CState.ref {p : Prime} (self : CState p) {tp} (v : Tp.denote p tp) : (Ref × CState p) :=
  (Ref.mk self.vals.size, { self with vals := self.vals.push ⟨tp, v⟩ })

def CState.lam {p : Prime} (self : CState p) {inTps outTp} (body : HList (Tp.denote p) inTps → Expr (Tp.denote p) outTp) : (Ref × CState p) :=
  (Ref.mk self.lambdas.size, { self with lambdas := self.lambdas.push ⟨inTps, outTp, body⟩ })

theorem CState.ref_toState_eq_toState_insert {v : Tp.denote p tp}:
    (CState.ref self v).2.toState = self.toState.insertVal (CState.ref self v).1 ⟨tp, v⟩ := by
  rw [State.eq_constructor]
  congr 1
  simp only [toState, ref, Array.toList_push, State.insertVal]
  apply Finmap.ext_lookup
  intro x
  by_cases h : x = Ref.mk self.vals.size
  · cases h
    simp only [List.zipIdx_append, zero_add, List.zipIdx_cons, List.zipIdx_nil,
      List.map_append, List.map_cons, List.map_nil, Finmap.dlookup_list_toFinmap,
      List.dlookup_append, List.dlookup_cons_eq, Option.or_some, Finmap.lookup_insert,
      Option.some.injEq]
    have : (List.dlookup (Ref.mk self.vals.size) (List.map (fun x ↦ (⟨{ val := x.2 }, x.1⟩ : Sigma (fun _ => AnyValue p))) self.vals.toList.zipIdx)) = none := by
      rw [List.dlookup_eq_none]
      simp only [List.keys, List.map_map, List.mem_map, Function.comp_apply, Ref.mk.injEq,
        Prod.exists, exists_eq_right, not_exists]
      intro _ hp
      have := List.mem_zipIdx hp
      have := this.2.1
      simp at this
    simp [this]
  · simp [h, List.zipIdx_append, List.dlookup_append]

theorem CState.lam_toState_eq_toState_insert {body : HList (Tp.denote p) inTps → Expr (Tp.denote p) outTp}:
    (CState.lam self body).2.toState = self.toState.insertLam (CState.lam self body).1 ⟨inTps, outTp, body⟩ := by
  rw [State.eq_constructor]
  congr 1
  simp only [toState, lam, Array.toList_push, State.insertLam]
  apply Finmap.ext_lookup
  intro x
  by_cases h : x = Ref.mk self.lambdas.size
  · cases h
    simp only [List.zipIdx_append, zero_add, List.zipIdx_cons, List.zipIdx_nil,
      List.map_append, List.map_cons, List.map_nil, Finmap.dlookup_list_toFinmap,
      List.dlookup_append, List.dlookup_cons_eq, Option.or_some, Finmap.lookup_insert,
      Option.some.injEq]
    have : (List.dlookup (Ref.mk self.lambdas.size) (List.map (fun x ↦ (⟨{ val := x.2 }, x.1⟩ : Sigma (fun _ => Lambda (Tp.denote p)))) self.lambdas.toList.zipIdx)) = none := by
      rw [List.dlookup_eq_none]
      simp only [List.keys, List.map_map, List.mem_map, Function.comp_apply, Ref.mk.injEq,
        Prod.exists, exists_eq_right, not_exists]
      intro _ hp
      have := List.mem_zipIdx hp
      have := this.2.1
      simp at this
    simp [this]
  · simp [h, List.zipIdx_append, List.dlookup_append]

theorem CState.toState_lookup_eq_getElem {self : CState p} {ref : Ref}:
    (CState.toState self).vals.lookup ref = self.vals[ref.val]? := by
  sorry


def AssignableWithState {tp} (p : Prime) (Γ : Env) (e : Expr (Tp.denote p) tp) (preState postState : CState p) (result : tp.denote p) :=
  ¬Omni p Γ preState.toState e (fun r => r ≠ (postState.toState, result))

def AssignableMain {tp} (p : Prime) (Γ : Env) (e : Expr (Tp.denote p) tp) (result : tp.denote p) :=
  ∃postState, AssignableWithState p Γ e  default postState result

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

theorem AssignableWithState.litU_intro:
    AssignableWithState p Γ (Expr.litNum (.u s) n) state state n := by
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

theorem AssignableWithState.sliceLen_intro:
    AssignableWithState p env
      (Expr.callBuiltin [Tp.slice tp] (.u 32) Builtin.arrayLen h![slice])
      st st slice.length := by
  apply AssignableWithState.genericPureBuiltin_intro (a := Builtin.ArrayLenCase.slice tp)

theorem AssignableWithState.ref_intro {tp} {v : Tp.denote p tp}:
    AssignableWithState p Γ (Expr.ref v) state (state.ref v).2 (state.ref v).1 := by
  intro hp
  cases hp
  rename_i hp
  cases hp
  rename_i hp
  apply hp (state.ref v).1
  · cases state
    simp only [CState.toState, CState.ref, Finmap.mem_list_toFinmap, List.mem_map, Sigma.mk.injEq,
      Ref.mk.injEq, heq_eq_eq, Prod.exists, existsAndEq, true_and, exists_eq_right, not_exists]
    rw [Array.size_eq_length_toList]
    intro
    intro h
    have := (List.mem_zipIdx h).2.1
    simp at this
  · simp only [Option.map_some, CState.ref_toState_eq_toState_insert, Option.some.injEq,
    Prod.mk.injEq, State.eq_constructor, and_true]
    congr 1

theorem AssignableWithState.lam_intro:
    AssignableWithState p Γ (Expr.lam argTps outTp b) state (state.lam b).2 (FuncRef.lambda (state.lam b).1) := by
  intro hp
  cases hp
  rename_i hp
  apply hp (state.lam b).1
  · cases state
    simp only [CState.toState, CState.lam, Finmap.mem_list_toFinmap, List.mem_map, Sigma.mk.injEq,
      Ref.mk.injEq, heq_eq_eq, Prod.exists, existsAndEq, true_and, exists_eq_right, not_exists]
    rw [Array.size_eq_length_toList]
    intro
    intro h
    have := (List.mem_zipIdx h).2.1
    simp at this
  · simp only [Option.map_some, CState.lam_toState_eq_toState_insert, Option.some.injEq,
    Prod.mk.injEq, State.eq_constructor, and_true]
    congr 1

theorem AssignableWithState.readRef_intro:
    (h_ix : ix.val < pre.vals.size) →
    (h_tp : (pre.vals[ix.val]'h_ix).1 = tp) →
    AssignableWithState p Γ (Expr.readRef ix) pre pre (h_tp ▸ (pre.vals[ix.val]'h_ix).2) := by
  intro h_ix h_tp
  intro hp
  cases hp
  rename_i hp
  cases hp
  simp_all [mapToValHeapCondition, CState.toState_lookup_eq_getElem]
  rename pre.vals[_] = _ => hp
  generalize h: pre.vals[ix.val]'h_ix = x
  apply_assumption
  rename tp.denote p => v
  have h_tp' := h_tp
  rw [h] at h_tp'
  have : h_tp ▸ pre.vals[ix.val].snd = h_tp' ▸ x.snd := by
    cases h
    rfl
  rw [this]
  rw [h] at hp
  cases hp
  rfl

theorem AssignableWithState.fn_intro:
    AssignableWithState p Γ (Expr.fn _ _ r) pre pre r := by
  intro hp
  cases hp
  simp_all

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

syntax "norm": tactic
macro_rules | `(tactic|norm) => `(tactic
  | try simp only [CState.ref, CState.default_def,
    List.size_toArray, List.length_nil, List.length_cons, HList.toList,
    List.push_toArray, List.nil_append])

partial def solve (goal : MVarId): TacticM (List MVarId) := do
  let [goal] ← evalTacticAt (← `(tactic| norm)) goal
    | throwError "Failed to simplify goal"
  let target ← goal.instantiateMVarsInType
  let_expr AssignableWithState tp p Γ e pre post res ← target
    | throwError "Goal is not of the form AssignableWithState p Γ e pre post res"
  let target := mkAppN (.const ``AssignableWithState []) #[tp, p, Γ, e, pre, post, res]
  let goal ← goal.change target
  match_expr e with
  | Expr.letIn _ _ _ e b =>
    let eGoal :: bGoal :: impls ← goal.apply (.const ``AssignableWithState.letIn [])
      | throwError "Failed to apply letIn"
    let eGoals ← try solve eGoal catch _ => return [eGoal, bGoal] ++ impls
    let bGoals ← try solve bGoal catch _ => return eGoals ++ [bGoal] ++ impls
    return eGoals ++ bGoals ++ impls
  | Expr.var _ _ _ =>
    let impl ← goal.apply (.const ``AssignableWithState.var [])
    return impl
  | Expr.litNum _ tp _ => match_expr tp with
    | Tp.field =>
      let impl ← goal.apply (.const ``AssignableWithState.fieldLit [])
      return impl
    | Tp.u _ =>
      let impl ← goal.apply (.const ``AssignableWithState.litU_intro [])
      return impl
    | _ => throwError "No applicable rules"
  | Expr.fn _ _ _ _ =>
    let impl ← goal.apply (.const ``AssignableWithState.fn_intro [])
    return impl
  | Expr.lam _ _ _ _ =>
    -- return [goal]
    let impl ← goal.apply (.const ``AssignableWithState.lam_intro [])
    return impl
  | Expr.callBuiltin _ aTps _ b _ =>
    match_expr b with
    | Builtin.mkSlice =>
      let impl ← goal.apply (.const ``AssignableWithState.mkSlice_intro [])
      return impl
    | Builtin.ref =>
      let impl ← goal.apply (.const ``AssignableWithState.ref_intro [])
      return impl
    | Builtin.arrayLen =>
      let_expr List.cons _ tp _ ← aTps
        | throwError "arrayLen should have one argument"
      match_expr tp with
      | Tp.slice _ => sorry
      | Tp.array _ _ => sorry
      | _ => throwError "arrayLen should take a slice or array"
    | _ => throwError "No applicable rules"
  | Expr.ref _ _ _ =>
    let impl ← goal.apply (.const ``AssignableWithState.ref_intro [])
    return impl
  | Expr.readRef _ _ _ =>
    let tp_ok :: ix_ok :: impls ← goal.apply (.const ``AssignableWithState.readRef_intro [])
      | throwError "Failed to apply readRef_intro"
    let [] ← evalTacticAt (← `(tactic| norm; decide)) ix_ok
      | throwError "Failed to prove index is in bounds"
    tp_ok.refl
    return impls
  | _ => throwError "No applicable rules"

elab "crush" : tactic => do
  let goal ← getMainGoal
  replaceMainGoal (←solve goal)

-- unif_hint (p : Prime) (tp tp' : Tp) where
--   Tp.slice tp' =?= tp
--   ⊢ Tp.denote p tp =?= List (Tp.denote p tp')

theorem HList.toList_nil : (@HList.nil α β).toList p = [] := by rfl

-- set_option Lampe.pp.Expr true

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
  crush

  apply AssignableWithState.callDecl
  · rfl
  · simp [env]
    rintro _ (h | h)
    · apply_fun FunctionDecl.fn at h
      conv at h => congr <;> whnf
      cases h
      rfl
    · apply_fun FunctionDecl.name at h
      conv at h => congr <;> whnf
      simp at h
  rotate_left
  · rfl
  · rfl
  · rfl

  rotate_right
  crush
