import Lampe.Builtin.Basic
namespace Lampe.Builtin

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
def slicePushBack := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, tp], .slice tp⟩)
  (fun _ h![l, e] => ⟨True,
    fun _ => l ++ [e]⟩)

/--
Defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : List tp`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront := newGenericPureBuiltin
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
def sliceInsert := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, .u 32, tp], .slice tp⟩)
  (fun _ h![l, i, e] => ⟨i.toNat < l.length,
    fun _ => l.insertNth i.toNat e⟩)


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

@[reducible]
def replaceSl (s : Tp.denote p $ .slice tp) (i : Nat) (v : Tp.denote p tp) : Tp.denote p $ .slice tp :=
  s.eraseIdx i |>.insertNth i v

def replaceSlice := newGenericPureBuiltin
  (fun tp => ⟨[.slice tp, .u 32, tp], (.slice tp)⟩)
  (fun _ h![sl, idx, v] => ⟨True,
    fun _ => replaceSl sl idx.toNat v⟩)

inductive sliceWriteIndexOmni : Omni where
| ok {p st tp} {s : Tp.denote p $ .slice tp} {v : Tp.denote p tp} {Q} :
  (_ : st.lookup ref = some ⟨.slice tp, s⟩ ∧ idx.toNat < s.length) →
  Q (some (st.insert ref ⟨.slice tp, replaceSl s idx.toNat v⟩, ())) →
  sliceWriteIndexOmni p st [.ref $ .slice tp, .u 32, tp] .unit h![ref, idx, v] Q
| err {p st tp} {s : Tp.denote p $ .slice tp} {v : Tp.denote p tp} {Q} :
  (st.lookup ref = some ⟨.slice tp, s⟩ ∧ idx.toNat ≥ s.length) →
  Q none →
  sliceWriteIndexOmni p st [.ref $ .slice tp, .u 32, tp] .unit h![ref, idx, v] Q

def sliceWriteIndex : Builtin := {
  omni := sliceWriteIndexOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type sliceWriteIndexOmni
    . apply sliceWriteIndexOmni.ok <;> tauto
    . apply sliceWriteIndexOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type sliceWriteIndexOmni
    . apply sliceWriteIndexOmni.ok <;> tauto
      rw [Finmap.lookup_union_left]
      assumption
      apply Finmap.mem_of_lookup_eq_some <;> tauto
      repeat apply Exists.intro
      apply And.intro ?_
      . simp_all only [Finmap.insert_union]
        apply And.intro rfl (by tauto)
      . apply Finmap.disjoint_insert <;> tauto
    . apply sliceWriteIndexOmni.err
      rw [Finmap.lookup_union_left]
      tauto
      rename_i h
      apply Finmap.mem_of_lookup_eq_some h.left
      tauto
}

end Lampe.Builtin
