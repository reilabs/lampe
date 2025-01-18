import Mathlib.Algebra.PUnitInstances.Algebra -- TODO: This import is necessary for the
                                              -- `CommRing Unit` instance, but shouldn't be needed
import Lampe.Builtin.Basic

namespace Lampe.Builtin

inductive Member : CTp → List CTp → Type where
| head : Member tp (tp :: tps)
| tail : Member tp tps → Member tp (tp' :: tps)

@[reducible]
def indexTpl (tpl : CTp.denoteArgs p tps) (mem : Member tp tps) : Tp.denote p tp := match tps with
| tp :: _ => match tpl, mem with
  | (h, _), .head => h
  | (_, rem), .tail m => indexTpl rem m

def exampleTuple {p} : CTp.denoteArgs p [.bool, .field, .field] := (true, 4, 5)

example : indexTpl (p := p) exampleTuple Member.head = true := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail = 4 := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail.tail = 5 := rfl

@[reducible]
def replaceTuple' (tpl : CTp.denoteArgs p tps) (mem : Member tp tps) (v : Tp.denote p tp) : CTp.denoteArgs p tps := match tps with
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
  (fun (name, (fieldTps : List CTp)) => ⟨fieldTps, (CTp.tuple name fieldTps)⟩)
  (fun (name, fieldTps) fieldExprs => ⟨HList.getTps fieldExprs = fieldTps,
    fun h => HList.toTuple (HList.toCTps fieldExprs h) name⟩)

/--
Defines the indexing/projection of a tuple with a `Member`.
-/
def projectTuple (mem : Member outTp fieldTps) := newGenericPureBuiltin
  (fun name => ⟨[CTp.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => ⟨True, fun _ => indexTpl tpl mem⟩)


end Lampe.Builtin
