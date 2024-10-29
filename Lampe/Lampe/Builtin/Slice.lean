import Lampe.Builtin.Prelude

namespace Lean.Builtin
open Lampe.Builtin

/--
Defines the indexing of a slice `l : Tp.denote _ (.slice tp)` with `i : Tp.denote _ (.u 32)`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def sliceIndex {tp} := newBuiltin
  [(.slice tp), (.u 32)] tp
  (fun h![l, i] => i.toNat < l.length)
  (fun h![l, i] v => l.get (Fin.mk i.toNat v))

/--
Defines the builtin that returns the length of a slice `l : Tp.denote _ (.slice tp)`
We make the following assumptions:
- If `l.length < 2^32`, then the builtin returns `l.length : Tp.denote _ (.u 32)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `fn len(self) -> u32` implemented for `[T]`.
-/
def sliceLen {tp} := newBuiltin
  [(.slice tp)] (.u 32)
  (fun h![l] => l.length < 2^(32))
  (fun h![l] _ => l.length)

/--
Defines the builtin that pushes back an element `e : Tp.denote tp` to a slice `l : Tp.denote _ (.slice tp)`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir, this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushBack {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => l ++ [e])

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : Tp.denote _ (.slice tp)`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => [e] ++ l)

/--
Defines the insertion of an element `e : Tp.denote tp` at index `i : Tp.denote _ (.u 32)` to a slice `l : Tp.denote _ (.slice tp)`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def sliceInsert {tp} := newBuiltin
  [(.slice tp), (.u 32), tp] (.slice tp)
  (fun h![l, i, _] => i < l.length)
  (fun h![l, i, e] _ => List.insertNth i.toNat e l)

/--
Defines the builtin that pops the first element of a slice `l : Tp.denote _ (.slice tp)`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[0], l[1:])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_front(self) -> (T, Self)` implemented for `[T]`.
-/
def slicePopFront {tp} := newBuiltin
  [(.slice tp)] (.struct [tp, .slice tp])
  (fun h![l] => l ≠ [])
  (fun h![l] v => (l.head v, (l.tail, ())))

/--
Defines the builtin that pops the last element of a slice `l : Tp.denote _ (.slice tp)`.
We make the following assumptions:
- If `l ≠ []`, then the builtin returns `(l[:l.length-1], l[l.length-1])`.
- Else (empty slice), an exception is thrown.

In Noir, this builtin corresponds to `fn pop_back(self) -> (Self, T)` implemented for `[T]`.
-/
def slicePopBack {tp} := newBuiltin
  [(.slice tp)] (.struct [.slice tp, tp])
  (fun h![l] => l ≠ [])
  (fun h![l] v => (l.dropLast, (l.getLast v, ())))

/--
Defines the removal of the element at the index `i : Tp.denote _ (.u 32)` from a slice `l : Tp.denote _ (.slice tp)`.
We make the following assumptions:
- If `i < l.length`, then the builtin returns `(l', l[i])`
where `l'` is `l` except that the element at index `i` is removed, and all the elements with indices larger than `i` are shifted to the left.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn remove(self, index: u32) -> (Self, T)` implemented for `[T]`.
-/
def sliceRemove {tp} := newBuiltin
  [(.slice tp), (.u 32)] (.struct [.slice tp, tp])
  (fun h![l, i] => i.toNat < l.length)
  (fun h![l, i] v => (l.eraseIdx i.toNat, (l.get (Fin.mk i.toNat v), ())))

end Lean.Builtin
