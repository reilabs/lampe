import Lampe.Builtin.Basic
namespace Lampe.Builtin

inductive Member : Tp → List Tp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

@[reducible]
def indexTpl (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) : Tp.denote p tp := match tps with
| tp :: _ => match tpl, mem with
  | (h, _), .head => h
  | (_, rem), .tail m => indexTpl rem m

def exampleTuple {p} : Tp.denoteArgs p [.bool, .field, .field] := (true, 4, 5)

example : indexTpl (p := p) exampleTuple Member.head = true := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail = 4 := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail.tail = 5 := rfl

@[reducible]
def replaceTpl (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) (v : Tp.denote p tp) : Tp.denoteArgs p tps := match tps with
| tp :: _ => match tpl, mem with
  | (_, rem), .head => (v, rem)
  | (h, rem), .tail m => (h, replaceTpl rem m v)

example : replaceTpl (p := p) exampleTuple Member.head false = (false, 4, 5) := rfl
example : replaceTpl (p := p) exampleTuple Member.head.tail 3 = (true, 3, 5) := rfl
example : replaceTpl (p := p) exampleTuple Member.head.tail.tail 2 = (true, 4, 2) := rfl

@[simp]
theorem index_replaced_tpl :
  indexTpl (replaceTpl tpl mem v') mem = v' := by
  induction mem <;> aesop

@[reducible]
def HList.toProd (hList : HList rep tps) : (listRep rep) tps := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toProd args⟩

def mkTuple := newGenericPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple name fieldTps)⟩)
  (fun _ fieldExprs => ⟨True,
    fun _ => listRep_tp_denote_is_tp_denote_tuple ▸ HList.toProd fieldExprs⟩)

def projectTuple (mem : Member outTp fieldTps) := newGenericPureBuiltin
  (fun name => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => ⟨True, fun _ => indexTpl tpl mem⟩)

inductive tupleWriteMemberOmni (mem : Member tp tps) : Omni where
| mk {tpl : Tp.denote p $ .tuple name tps}  {v : Tp.denote p tp} {Q} :
  (_ : st.lookup ref = some ⟨.tuple name tps, tpl⟩) →
  Q (some (st.insert ref ⟨.tuple name tps, replaceTpl tpl mem v⟩, ())) →
  tupleWriteMemberOmni mem p st [.ref $ .tuple name tps, tp] .unit h![ref, v] Q

def tupleWriteMember (mem : Member tp tps) : Builtin := {
  omni := tupleWriteMemberOmni mem
  conseq := by
    unfold omni_conseq
    intros
    cases_type tupleWriteMemberOmni
    . constructor <;> tauto
  frame := by
    unfold omni_frame
    intros p st₁ st₂ argTps outTp args Q _ hd
    cases_type tupleWriteMemberOmni
    rename Ref => ref
    generalize h₃ : (Finmap.insert ref _ _) = st₃ at *
    apply tupleWriteMemberOmni.mk <;> tauto
    . rw [Finmap.lookup_union_left]
      assumption
      apply Finmap.mem_of_lookup_eq_some <;> tauto
    . simp_all only [Finmap.insert_union]
      exists st₃, st₂
      apply And.intro
      . simp only [LawfulHeap.disjoint]
        rw [←h₃]
        apply Finmap.disjoint_insert <;> tauto
      apply And.intro <;> try simp_all
}

end Lampe.Builtin
