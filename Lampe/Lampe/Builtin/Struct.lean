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
def listRep (rep : Tp → Type _) : List Tp → Type := fun l => match l with
| tp :: tps => (rep tp) × (listRep rep tps)
| [] => Unit

@[reducible]
def HList.toProd (hList : HList rep tps) : (listRep rep) tps := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toProd args⟩

lemma listRep_tp_denote_is_tp_denote_tuple :
  listRep (Tp.denote p) tps = Tp.denote p (.tuple name tps) := by
  induction tps <;> {
    unfold listRep Tp.denoteArgs
    tauto
  }

@[reducible]
def replaceTuple' (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) (v : Tp.denote p tp) : Tp.denoteArgs p tps := match tps with
| tp :: _ => match tpl, mem with
  | (_, rem), .head => (v, rem)
  | (h, rem), .tail m => (h, replaceTuple' rem m v)

example : replaceTuple' (p := p) exampleTuple Member.head false = (false, 4, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail 3 = (true, 3, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail.tail 2 = (true, 4, 2) := rfl

@[simp]
theorem index_replaced_tpl :
  indexTpl (replaceTuple' tpl mem v') mem = v' := by
  induction mem <;> aesop

/--
Defines the builtin tuple constructor.
-/
def mkTuple := newGenericPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple name fieldTps)⟩)
  (fun _ fieldExprs => ⟨True,
    fun _ => listRep_tp_denote_is_tp_denote_tuple ▸ HList.toProd fieldExprs⟩)

/--
Defines the indexing/projection of a tuple with a `Member`.
-/
def projectTuple (mem : Member outTp fieldTps) := newGenericPureBuiltin
  (fun name => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => ⟨True, fun _ => indexTpl tpl mem⟩)


def replaceTuple (mem : Member tp tps) := newGenericPureBuiltin
  (fun name => ⟨[.tuple name tps, tp], (.tuple name tps)⟩)
  (fun _ h![tpl, v] => ⟨True,
    fun _ => replaceTuple' tpl mem v⟩)

end Lampe.Builtin
