import Lampe.Builtin.Basic

namespace Lampe.Builtin

@[reducible]
def replaceSlice' (s : Tp.denote p $ .vector tp) (i : Fin s.length) (v : Tp.denote p tp) : Tp.denote p $ .vector tp :=
  List.modify s i (fun _ => v)

@[simp]
theorem replaceSlice_length_eq_length :
    (replaceSlice' s i v).length = s.length := by
  simp_all [List.length_modify]

@[simp]
theorem index_replaced_slice :
    (replaceSlice' s idx v).get ⟨idx.val, h⟩ = v := by
  simp_all [List.modify_eq_set_getElem?, List.getElem_eq_iff]

/--
Defines the builtin slice constructor.
-/
def mkSlice := newGenericTotalPureBuiltin
  (fun (n, tp) => ⟨List.replicate n tp, (.vector tp)⟩)
  (fun _ args => HList.toList args rfl)

/--
Defines the builtin for repeated slices
-/
def mkRepeatedSlice := newGenericTotalPureBuiltin
  (fun (a : Tp)=> ⟨[Tp.u 32, a], (.vector a)⟩)
  (fun _ h![n, val] => List.replicate n.toNat val)

/--
Defines the indexing of a slice `l : List tp` with `i : U 32`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def vectorIndex := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32], tp⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/--
Defines the builtin that pushes back an element `e : Tp.denote tp` to a vector `l : List tp`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir (≥ beta.14), this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def vectorPushBack := newGenericTotalPureBuiltin
  (fun tp => ⟨[.vector tp, tp], .vector tp⟩)
  (fun _ h![l, e] => l ++ [e])

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a vector `l : List tp`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir (≥ beta.14), this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def vectorPushFront := newGenericTotalPureBuiltin
  (fun tp => ⟨[.vector tp, tp], .vector tp⟩)
  (fun _ h![l, e] => [e] ++ l)

/--
Defines the insertion of an element `e : Tp.denote tp` at index `i : U 32` to a vector `l : List tp`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir (≥ beta.14), this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def vectorInsert := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32, tp], .vector tp⟩)
  (fun _ h![l, i, e] => ⟨i.toNat < l.length,
    fun _ => l.insertIdx i.toNat e⟩)


/--
Defines the builtin that pops the first element of a vector `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[0], l[1:])`.
- Else (empty vector), an exception is thrown.

In Noir (≥ beta.14), this builtin corresponds to `fn pop_front(self) -> (T, Self)` implemented for `[T]`.
-/
def vectorPopFront := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp], .tuple none [tp, .vector tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.head h, l.tail, ())⟩)

/--
Defines the builtin that pops the last element of a vector `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[:l.length-1], l[l.length-1])`.
- Else (empty vector), an exception is thrown.

In Noir (≥ beta.14), this builtin corresponds to `fn pop_back(self) -> (Self, T)` implemented for `[T]`.
-/
def vectorPopBack := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp], .tuple none [.vector tp, tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.dropLast, l.getLast h, ())⟩)

/--
Defines the removal of the element at the index `i : U 32` from a vector `l : List tp`.
We make the following assumptions:
- If `i < l.length`, then the builtin returns `(l', l[i])`
where `l'` is `l` except that the element at index `i` is removed, and all the elements with indices larger than `i` are shifted to the left.
- Else (out of bounds access), an exception is thrown.

In Noir (≥ beta.14), this builtin corresponds to `fn remove(self, index: u32) -> (Self, T)` implemented for `[T]`.
-/
def vectorRemove := newGenericPureBuiltin
  (fun tp => ⟨[.vector tp, .u 32], .tuple none [.vector tp, tp]⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ())⟩)

end Lampe.Builtin
