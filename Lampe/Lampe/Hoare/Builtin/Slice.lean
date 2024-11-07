import Lampe.Ast
import Lampe.Tp
import Lampe.Semantics
import Lampe.SeparationLogic
import Lampe.Hoare.Total
import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem sliceLen_intro {l}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.u 32) (.builtin .sliceLen) h![l])
      fun v => v = l.length ∧ l.length < 2^32 := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceIndex_intro {l} {i : U 32}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32] tp (.builtin .sliceIndex) h![l, i])
      fun v => some v = l[i.toNat]? := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePushBack_intro {l val}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, tp] (.slice tp) (.builtin .slicePushBack) h![l, val])
      fun v => v = l ++ [val] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePushFront_intro {l val}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, tp] (.slice tp) (.builtin .slicePushFront) h![l, val])
      fun v => v = [val] ++ l := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceInsert_intro {l i e}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32, tp] (.slice tp) (.builtin .sliceInsert) h![l, i, e])
      fun v => v = l.insertNth i.toNat e := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePopFront_intro {l}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.struct [tp, .slice tp]) (.builtin .slicePopFront) h![l])
      fun v => ∃h, v = (l.head h, l.tail, ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePopBack_intro {l}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.struct [.slice tp, tp]) (.builtin .slicePopBack) h![l])
      fun v => ∃h, v = (l.dropLast, l.getLast h, ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceRemove_intro {l i}:
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32] (.struct [.slice tp, tp]) (.builtin .sliceRemove) h![l, i])
      fun v => ∃h, v = (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

end Lampe.STHoare
