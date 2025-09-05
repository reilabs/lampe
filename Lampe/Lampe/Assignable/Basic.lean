import Lampe

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

theorem AssignableWithState.callDecl {fnRef}
    (hpf: ∃func,
      (fnRef = (.decl fnName kinds generics)) ∧
      ⟨fnName, func⟩ ∈ Γ.functions ∧
      ∃(hkc : func.generics = kinds),
      ∃(htci : (func.body (Tp.denote p) (hkc ▸ generics) |>.argTps) = argTps),
      ∃(htco : (func.body (Tp.denote p) (hkc ▸ generics) |>.outTp) = outTp),
      AssignableWithState p Γ (htco ▸ (func.body (Tp.denote p) (hkc ▸ generics) |>.body (htci ▸ args))) pre post res):
    AssignableWithState p Γ (Expr.call argTps outTp fnRef args) pre post res := by
  intros
  intro hp
  cases hp
  apply_assumption



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

example : AssignableMain p env («std::slice::test::for_each_example».call h![] h![]) () := by
  apply Exists.intro
