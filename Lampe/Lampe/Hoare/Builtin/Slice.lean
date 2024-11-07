import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem sliceLen_intro {sl} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.u 32) (.builtin .sliceLen) h![sl])
      fun v => v = sl.length ∧ sl.length < 2^32 := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceIndex_intro {sl i} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32] tp (.builtin .sliceIndex) h![sl, i])
      fun v => some v = sl[i.toNat]? ∧ i.toNat < sl.length := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePushBack_intro {sl e} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, tp] (.slice tp) (.builtin .slicePushBack) h![sl, e])
      fun v => v = sl ++ [e] := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePushFront_intro {sl e} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, tp] (.slice tp) (.builtin .slicePushFront) h![sl, e])
      fun v => v = [e] ++ sl := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceInsert_intro {sl i e} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32, tp] (.slice tp) (.builtin .sliceInsert) h![sl, i, e])
      fun v => v = sl.insertNth i.toNat e ∧ i.toNat < sl.length := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePopFront_intro {sl} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.struct [tp, .slice tp]) (.builtin .slicePopFront) h![sl])
      fun v => ∃h, v = (sl.head h, sl.tail, ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem slicePopBack_intro {sl} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp] (.struct [.slice tp, tp]) (.builtin .slicePopBack) h![sl])
      fun v => ∃h, v = (sl.dropLast, sl.getLast h, ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

theorem sliceRemove_intro {sl i} :
    STHoare p Γ
      ⟦⟧
      (.call h![] [.slice tp, .u 32] (.struct [.slice tp, tp]) (.builtin .sliceRemove) h![sl, i])
      fun v => ∃h, v = (sl.eraseIdx i.toNat, sl.get (Fin.mk i.toNat h), ()) := by
  apply pureBuiltin_intro_consequence <;> try rfl
  simp

end Lampe.STHoare
