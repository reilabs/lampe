import Mathlib.Algebra.PEmptyInstances
import Mathlib.FieldTheory.Finite.Basic

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

@[simp]
theorem indexTpl_head (a : Tp.denote p tp) (rest : Tp.denoteArgs p tps) :
    indexTpl (p := p) (Prod.mk a rest) Member.head = a := rfl

@[simp]
theorem indexTpl_tail (a : Tp.denote p tp') (rest : Tp.denoteArgs p tps) (m : Member tp tps) :
    indexTpl (p := p) (Prod.mk a rest) (Member.tail m) = indexTpl rest m := rfl

def exampleTuple {p} : Tp.denoteArgs p [.bool, .field, .field] := (true, 4, 5)

example : indexTpl (p := p) exampleTuple Member.head = true := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail = 4 := rfl
example : indexTpl (p := p) exampleTuple Member.head.tail.tail = 5 := rfl


@[reducible]
def replaceTuple' (tpl : Tp.denoteArgs p tps) (mem : Member tp tps) (v : Tp.denote p tp) : Tp.denoteArgs p tps := match tps with
| tp :: _ => match tpl, mem with
  | (_, rem), .head => (v, rem)
  | (h, rem), .tail m => (h, replaceTuple' rem m v)

@[simp]
theorem replaceTuple'_head (a : Tp.denote p tp) (rest : Tp.denoteArgs p tps) (v : Tp.denote p tp) :
    replaceTuple' (p := p) (Prod.mk a rest) Member.head v = (v, rest) := rfl

@[simp]
theorem replaceTuple'_tail (a : Tp.denote p tp') (rest : Tp.denoteArgs p tps) (m : Member tp tps) (v : Tp.denote p tp) :
    replaceTuple' (p := p) (Prod.mk a rest) (Member.tail m) v = (a, replaceTuple' rest m v) := rfl

example : replaceTuple' (p := p) exampleTuple Member.head false = (false, 4, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail 3 = (true, 3, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail.tail 2 = (true, 4, 2) := rfl

-- simp should reduce indexTpl on Tp.denote-typed tuples (as they appear after `steps`)
example (tpl : Tp.denote p (.tuple (some "Complex") [.field, .field])) (h : tpl = (ar, ai, ())) :
    indexTpl (p := p) tpl Member.head.tail = ai := by
  subst h; simp only [indexTpl_tail, indexTpl_head]

-- simp works when the tuple has an explicit Tp.denoteArgs annotation (as in exampleTuple above).
-- With an untyped literal, the elaborator can't infer the implicit `tps` list, because
-- unification of `Bool × U 32 × U 32 × Unit` with `Tp.denoteArgs p tps` doesn't solve for tps
-- even though Tp.denoteArgs is @[reducible].
--
-- The line below elaboration-fails (no annotation):
--   indexTpl (p := p) (s, n, d, ()) Member.head.tail
--
-- With a type ascription, simp fires normally:
example (p : Prime) (s : Bool) (n d : U 32) :
    let tpl : Tp.denoteArgs p [.bool, .u 32, .u 32] := (s, n, d, ())
    indexTpl (p := p) tpl Member.head.tail = n := by
  simp [indexTpl_tail, indexTpl_head]

@[simp]
theorem index_replaced_tpl :
  indexTpl (replaceTuple' tpl mem v') mem = v' := by
  induction mem <;> aesop

/--
Defines the builtin tuple constructor.
-/
def makeData := newGenericTotalPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple name fieldTps)⟩)
  (fun {p} (name, _) fieldExprs => HList.toTuple p fieldExprs name)

/--
Defines the indexing/projection of a tuple with a `Member`.
-/
def getMember (mem : Member outTp fieldTps) := newGenericTotalPureBuiltin
  (fun name => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => indexTpl tpl mem)

/--
Defines the builtin tuple constructor.
-/
def mkTuple := newGenericTotalPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple name fieldTps)⟩)
  (fun {p} (name, _) fieldExprs => HList.toTuple p fieldExprs name)

/--
Defines the indexing/projection of a tuple with a `Member`.
-/
def projectTuple (mem : Member outTp fieldTps) := newGenericTotalPureBuiltin
  (fun name => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => indexTpl tpl mem)


end Lampe.Builtin
