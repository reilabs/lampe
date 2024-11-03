import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the indexing of a slice `l : List tp` with `i : U 32`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def sliceIndex := newGenPureBuiltin
  (fun tp => ⟨[.slice tp, .i 32], tp⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/--
Defines the builtin that returns the length of a slice `l : List tp`
We make the following assumptions:
- If `l.length < 2^32`, then the builtin returns `l.length : U 32`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `fn len(self) -> u32` implemented for `[T]`.
-/
def sliceLen := newGenPureBuiltin
  (fun tp => ⟨[.slice tp], .i 32⟩)
  (fun _ h![l] => ⟨l.length < 2^32,
    fun _ => l.length⟩)


/--
Defines the builtin that pushes back an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir, this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushBack := newGenPureBuiltin
  (fun tp => ⟨[.slice tp, tp], .slice tp⟩)
  (fun _ h![l, e] => ⟨True,
    fun _ => l ++ [e]⟩)

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront := newGenPureBuiltin
  (fun tp => ⟨[.slice tp, tp], .slice tp⟩)
  (fun _ h![l, e] => ⟨True,
    fun _ => [e] ++ l⟩)

/--
Defines the insertion of an element `e : Tp.denote tp` at index `i : U 32` to a slice `l : List tp`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def sliceInsert := newGenPureBuiltin
  (fun tp => ⟨[.slice tp, .i 32, tp], .slice tp⟩)
  (fun _ h![l, i, e] => ⟨i.toNat < l.length,
    fun _ => l.insertNth i.toNat e⟩)


/--
Defines the builtin that pops the first element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[0], l[1:])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_front(self) -> (T, Self)` implemented for `[T]`.
-/
def slicePopFront := newGenPureBuiltin
  (fun tp => ⟨[.slice tp], .struct [tp, .slice tp]⟩)
  (fun _ h![l] => ⟨l ≠ [],
    fun h => (l.head h, l.tail, ())⟩)

/--
Defines the builtin that pops the last element of a slice `l : List tp`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[:l.length-1], l[l.length-1])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_back(self) -> (Self, T)` implemented for `[T]`.
-/
def slicePopBack := newGenPureBuiltin
  (fun tp => ⟨[Tp.slice tp], Tp.struct [Tp.slice tp, tp]⟩)
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
def sliceRemove := newGenPureBuiltin
  (fun tp => ⟨[.slice tp, Tp.i 32], .struct [.slice tp, tp]⟩)
  (fun _ h![l, i] => ⟨i.toNat < l.length,
    fun h => (l.eraseIdx i.toNat, l.get (Fin.mk i.toNat h), ())⟩)

end Lampe.Builtin
