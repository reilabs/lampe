import Lampe.Builtin.Basic
namespace Lean.Builtin
open Lampe.Builtin


inductive sliceIndexOmni : Omni where
| ok {P st tp l i Q} :
  (h: i.toNat < l.length)
    → Q (some (st, l.get (Fin.mk i.toNat h)))
    → sliceIndexOmni P st [.slice tp, .u 32] tp h![l, i] Q
| err {P st tp l i Q} :
  (i.toNat >= l.length)
    → Q none
    → sliceIndexOmni P st [.slice tp, .u 32] tp h![l, i] Q

/--
Defines the indexing of a slice `l : List tp` with `i : U 32`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def sliceIndex : Lampe.Builtin := {
  omni := sliceIndexOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type sliceIndexOmni
    . constructor <;> simp_all
    . apply sliceIndexOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type sliceIndexOmni
    . constructor
      . constructor <;> tauto
    . apply sliceIndexOmni.err <;> assumption
}

inductive sliceLenOmni : Omni where
| ok {P st tp l Q} :
  (h: l.length < 2^32)
    → Q (some (st, l.length))
    → sliceLenOmni P st [.slice tp] (.u 32) h![l] Q
| err {P st tp l Q} :
  (l.length >= 2^32)
    → Q none
    → sliceLenOmni P st [.slice tp] (.u 32) h![l] Q

/--
Defines the builtin that returns the length of a slice `l : List tp`
We make the following assumptions:
- If `l.length < 2^32`, then the builtin returns `l.length : U 32`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `fn len(self) -> u32` implemented for `[T]`.
-/
def sliceLen : Lampe.Builtin := {
  omni := sliceLenOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type sliceLenOmni
    . constructor <;> simp_all
    . apply sliceLenOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type sliceLenOmni
    . constructor
      tauto
      constructor <;> tauto
    . apply sliceLenOmni.err <;> assumption
}
inductive slicePushBackOmni : Omni where
| mk {P st tp l e Q} :
  Q (some (st, l ++ [e]))
    → slicePushBackOmni P st [.slice tp, tp] (.slice tp) h![l, e] Q

/--
Defines the builtin that pushes back an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir, this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushBack : Lampe.Builtin := {
  omni := slicePushBackOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type slicePushBackOmni
    constructor
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type slicePushBackOmni
    constructor
    constructor <;> tauto
}

inductive slicePushFrontOmni : Omni where
| mk {P st tp l e Q} :
  Q (some (st, [e] ++ l))
    → slicePushFrontOmni P st [.slice tp, tp] (.slice tp) h![l, e] Q

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront : Lampe.Builtin := {
  omni := slicePushFrontOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type slicePushFrontOmni
    constructor
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type slicePushFrontOmni
    constructor
    constructor <;> tauto
}

inductive sliceInsertOmni : Omni where
| ok {P st tp l i e Q} :
  i.toNat < l.length
    → Q (some (st, l.insertNth i.toNat e))
    → sliceInsertOmni P st [.slice tp, .u 32, tp] (.slice tp) h![l, i, e] Q
| err {P st tp l i e Q} :
  i.toNat >= l.length
    → Q none
    → sliceInsertOmni P st [.slice tp, .u 32, tp] (.slice tp) h![l, i, e] Q

/--
Defines the insertion of an element `e : Tp.denote tp` at index `i : U 32` to a slice `l : List tp`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def sliceInsert : Lampe.Builtin := {
  omni := sliceInsertOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type sliceInsertOmni
    . constructor <;> simp_all
    . apply sliceInsertOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type sliceInsertOmni
    constructor
    assumption
    simp
    . constructor <;> tauto
    . apply sliceInsertOmni.err <;> tauto
}

inductive slicePopFrontOmni : Omni where
| ok {P st tp l Q} :
  (h : l ≠ [])
    → Q (some (st, (l.head h, (l.tail, ()))))
    → slicePopFrontOmni P st [.slice tp] (.struct [tp, .slice tp]) h![l] Q
| err {P st tp l Q} :
  l = []
    → Q none
    → slicePopFrontOmni P st [.slice tp] (.struct [tp, .slice tp]) h![l] Q

/--
Defines the builtin that pops the first element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[0], l[1:])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_front(self) -> (T, Self)` implemented for `[T]`.
-/
def slicePopFront : Lampe.Builtin := {
  omni := slicePopFrontOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type slicePopFrontOmni
    . constructor <;> simp_all
    . apply slicePopFrontOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type slicePopFrontOmni
    . constructor
      . constructor <;> tauto
    . apply slicePopFrontOmni.err <;> assumption
}

inductive slicePopBackOmni : Omni where
| ok {P st tp l Q} :
  (h : l ≠ [])
    → Q (some (st, (l.dropLast, (l.getLast h, ()))))
    → slicePopBackOmni P st [.slice tp] (.struct [.slice tp, tp]) h![l] Q
| err {P st tp l Q} :
  l = []
    → Q none
    → slicePopBackOmni P st [.slice tp] (.struct [.slice tp, tp]) h![l] Q

/--
Defines the builtin that pops the last element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[:l.length-1], l[l.length-1])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_back(self) -> (Self, T)` implemented for `[T]`.
-/
def slicePopBack : Lampe.Builtin := {
  omni := slicePopBackOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type slicePopBackOmni
    . constructor <;> simp_all
    . apply slicePopBackOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type slicePopBackOmni
    . constructor
      . constructor <;> tauto
    . apply slicePopBackOmni.err <;> assumption
}

inductive sliceRemoveOmni : Omni where
| ok {P st tp l i Q} :
  (h : i.toNat < l.length)
    → Q (some (st, (l.eraseIdx i.toNat, (l.get (Fin.mk i.toNat h), ()))))
    → sliceRemoveOmni P st [.slice tp, .u 32] (.struct [.slice tp, tp]) h![l, i] Q
| err {P st tp l i Q} :
  i.toNat >= l.length
    → Q none
    → sliceRemoveOmni P st [.slice tp, .u 32] (.struct [.slice tp, tp]) h![l, i] Q

/--
Defines the removal of the element at the index `i : U 32` from a slice `l : List tp`.
We make the following assumptions:
- If `i < l.length`, then the builtin returns `(l', l[i])`
where `l'` is `l` except that the element at index `i` is removed, and all the elements with indices larger than `i` are shifted to the left.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn remove(self, index: u32) -> (Self, T)` implemented for `[T]`.
-/
def sliceRemove : Lampe.Builtin := {
  omni := sliceRemoveOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type sliceRemoveOmni
    . constructor <;> simp_all
    . apply sliceRemoveOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type sliceRemoveOmni
    . constructor
      . constructor <;> tauto
    . apply sliceRemoveOmni.err <;> assumption
}

end Lean.Builtin
