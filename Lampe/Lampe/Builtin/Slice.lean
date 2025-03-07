import Lampe.Builtin.Basic

namespace Lampe.Builtin

@[reducible]
def replaceSlice' (s : Tp.denote p $ .slice tp) (i : Fin s.length) (v : Tp.denote p tp) : Tp.denote p $ .slice tp :=
  List.modify (fun _ => v) i s

@[simp]
theorem replaceSlice_length_eq_length :
    (replaceSlice' s i v).length = s.length := by
  simp_all [List.length_modify]

@[simp]
theorem index_replaced_slice :
    (replaceSlice' s idx v).get ⟨idx.val, h⟩ = v := by
  simp_all [List.modify_eq_set_get?, List.getElem_eq_iff]

/--
Defines the builtin slice constructor.
-/
def mkSlice (n : Nat) := newGenericPureBuiltin
  (fun (argTps, tp) => ⟨argTps, (.slice tp)⟩)
  (fun (argTps, tp) args => ⟨argTps = List.replicate n tp,
    fun h => HList.toList args h⟩)

/--
Defines the indexing of a slice `l : List tp` with `i : U 32`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def sliceIndex := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, .u 32], tp⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/--
Defines the builtin that returns the length of a slice `l : List tp`
We make the following assumptions:
- If `l.length < 2^32`, then the builtin returns `l.length : U 32`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `fn len(self) -> u32` implemented for `[T]`.
-/
def sliceLen := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp], .u 32⟩)
  (fun _ h![l] => ⟨l.length < 2^32,
    fun _ => l.length⟩)


/--
Defines the builtin that pushes back an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir, this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushBack := newGenericTotalPureBuiltin
  (fun tp => ⟨[.slice tp, tp], .slice tp⟩)
  (fun _ h![l, e] => l ++ [e])

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront := newGenericTotalPureBuiltin
  (fun tp => ⟨[.slice tp, tp], .slice tp⟩)
  (fun _ h![l, e] => [e] ++ l)

/--
Defines the insertion of an element `e : Tp.denote tp` at index `i : U 32` to a slice `l : List tp`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def sliceInsert := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, .u 32, tp], .slice tp⟩)
  (fun _ h![l, i, e] => ⟨i.toNat < l.length,
    fun _ => l.insertIdx i.toNat e⟩)


/--
Defines the builtin that pops the first element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[0], l[1:])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_front(self) -> (T, Self)` implemented for `[T]`.
-/
def slicePopFront := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp], .tuple none [tp, .slice tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.head h, l.tail, ())⟩)

/--
Defines the builtin that pops the last element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[:l.length-1], l[l.length-1])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_back(self) -> (Self, T)` implemented for `[T]`.
-/
def slicePopBack := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp], .tuple none [.slice tp, tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.dropLast, l.getLast h, ())⟩)

/--
Defines the removal of the element at the index `i : U 32` from a slice `l : List tp`.
We make the following assumptions:
- If `i < l.length`, then the builtin returns `(l', l[i])`
where `l'` is `l` except that the element at index `i` is removed, and all the elements with indices larger than `i` are shifted to the left.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn remove(self, index: u32) -> (Self, T)` implemented for `[T]`.
-/
def sliceRemove := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, .u 32], .tuple none [.slice tp, tp]⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ())⟩)

end Lampe.Builtin
