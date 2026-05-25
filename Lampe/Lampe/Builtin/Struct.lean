import Mathlib.Algebra.PEmptyInstances
import Mathlib.FieldTheory.Finite.Basic

import Lampe.Builtin.Basic

namespace Lampe.Builtin

export Lampe (Member)

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

/-- Projection-form `indexTpl_head` that fires when the tuple is opaque (not syntactically a
`Prod.mk`). v4.29 simp no longer η-expands `Tp.denoteArgs` automatically. Low priority so
downstream domain-specific simp lemmas (`option_fst_eq_toOption_isSome`, etc.) fire first. -/
@[simp 900]
theorem indexTpl_head_proj (tpl : Tp.denoteArgs p (tp :: tps)) :
    indexTpl tpl Member.head = tpl.1 := by
  obtain ⟨_, _⟩ := tpl; rfl

/-- Projection-form `indexTpl_tail`. See `indexTpl_head_proj`. -/
@[simp 900]
theorem indexTpl_tail_proj (tpl : Tp.denoteArgs p (tp' :: tps)) (m : Member tp tps) :
    indexTpl tpl (Member.tail m) = indexTpl tpl.2 m := by
  obtain ⟨_, _⟩ := tpl; rfl

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

/-- Projection-form `replaceTuple'_head` — fires when the tuple is opaque
(v4.29 simp no longer η-expands `Tp.denoteArgs`). Low priority so domain-specific
simp lemmas can take precedence. -/
@[simp 900]
theorem replaceTuple'_head_proj (tpl : Tp.denoteArgs p (tp :: tps)) (v : Tp.denote p tp) :
    replaceTuple' tpl Member.head v = (v, tpl.2) := by
  obtain ⟨_, _⟩ := tpl; rfl

/-- Projection-form `replaceTuple'_tail`. See `replaceTuple'_head_proj`. -/
@[simp 900]
theorem replaceTuple'_tail_proj (tpl : Tp.denoteArgs p (tp' :: tps)) (m : Member tp tps)
    (v : Tp.denote p tp) :
    replaceTuple' tpl (Member.tail m) v = (tpl.1, replaceTuple' tpl.2 m v) := by
  obtain ⟨_, _⟩ := tpl; rfl

example : replaceTuple' (p := p) exampleTuple Member.head false = (false, 4, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail 3 = (true, 3, 5) := rfl
example : replaceTuple' (p := p) exampleTuple Member.head.tail.tail 2 = (true, 4, 2) := rfl

-- simp should reduce indexTpl on Tp.denote-typed tuples (as they appear after `steps`)
example (tpl : Tp.denote p (.tuple (some "Complex") [.field, .field])) (h : tpl = (ar, ai, ())) :
    indexTpl (p := p) tpl Member.head.tail = ai := by
  subst h; rfl

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
  intro tpl
  rfl

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
