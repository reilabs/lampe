import Lampe.State
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.SeparationLogic
import Mathlib

namespace Lampe

abbrev Builtin.Omni := ∀(P:Prime),
    State P →
    (argTps : List Tp) →
    (outTp : Tp) →
    HList (Tp.denote P) argTps →
    (Option (State P × Tp.denote P outTp) → Prop) →
    Prop

def Builtin.omni_conseq (omni : Builtin.Omni) : Prop :=
  ∀{P st argTps outTp args Q Q'}, omni P st argTps outTp args Q → (∀ r, Q r → Q' r) → omni P st argTps outTp args Q'

def Builtin.omni_frame (omni : Builtin.Omni) : Prop :=
  ∀{P st₁ st₂ argTps outTp args Q}, omni P st₁ argTps outTp args Q → st₁.Disjoint st₂ →
    omni P (st₁ ∪ st₂) argTps outTp args (fun r => match r with
      | some (st, v) => ((fun st => Q (some (st, v))) ⋆ (fun st => st = st₂)) st
      | none => Q none
    )

structure Builtin where
  omni : Builtin.Omni
  conseq : Builtin.omni_conseq omni
  frame : Builtin.omni_frame omni

namespace Builtin

inductive assertOmni : Omni where
| t {st Q} : Q (some (st, ())) → assertOmni P st [.bool] .unit h![true] Q
| f {st Q} : Q none → assertOmni P st [.bool] .unit h![false] Q

def assert : Builtin := {
  omni := assertOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type assertOmni <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type assertOmni
    · constructor
      repeat apply Exists.intro
      tauto
    · constructor; tauto
}

inductive eqOmni : Omni
| f {P st a b Q} : Q (some (st, a == b)) → eqOmni P st [.field, .field] .bool h![a, b] Q
| u {P st s a b Q} : Q (some (st, a == b)) → eqOmni P st [.u s, .u s] .bool h![a, b] Q

def eq : Builtin := {
  omni := eqOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type eqOmni <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type eqOmni <;> {
      constructor
      repeat apply Exists.intro
      tauto
    }
}

inductive freshOmni : Omni where
| mk {P st tp Q} : (∀ v, Q (some (st, v))) → freshOmni P st [] tp h![] Q

def fresh : Builtin := {
  omni := freshOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type freshOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type freshOmni
    constructor
    intro
    repeat apply Exists.intro
    tauto
}

inductive refOmni : Omni where
| mk {P st tp Q v}: (∀ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, ref))) →
  refOmni P st [tp] (tp.ref) h![v] Q

def ref : Builtin := {
  omni := refOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type refOmni
    constructor
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type refOmni
    constructor
    intros
    repeat apply Exists.intro
    apply And.intro ?_
    apply And.intro ?_
    apply And.intro
    apply_assumption
    simp_all
    rfl
    simp [Finmap.insert_union]
    simp_all [Finmap.insert_eq_singleton_union, Finmap.disjoint_union_left]
}

inductive readRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → Q (some (st, v)) →
  readRefOmni P st [tp.ref] tp h![ref] Q

def readRef : Builtin := {
  omni := readRefOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type readRefOmni
    constructor
    assumption
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type readRefOmni
    constructor
    rw [Finmap.lookup_union_left]
    assumption
    apply Finmap.mem_of_lookup_eq_some
    assumption
    repeat apply Exists.intro
    tauto
}

inductive builtinOmni
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → (HList (Tp.denote p) argTps) → Prop)
  (comp : {p : Prime} → (args: HList (Tp.denote p) argTps) → (pred args) → (Tp.denote p outTp)) : Omni where
  | ok {p st args Q}:
    (h : pred args)
      → Q (some (st, comp args h))
      → (builtinOmni argTps outTp pred comp) p st argTps outTp args Q
  | err {p st args Q}:
    ¬(pred args)
      → Q none
      → (builtinOmni argTps outTp pred comp) p st argTps outTp args Q

/--
A `Builtin` definition.
Takes a list of input types `argTps : List Tp`, an output type `outTp : Tp`, a predicate `pred` and evaluation function `comp`.
For `args: HList (Tp.denote p) argTps`, we assume that a builtin function *fails* when `¬(pred args)`, and it *succeeds* when `pred args`.

If the builtin succeeds, it evaluates to `some (comp args (h : pred))`.
Otherwise, it evaluates to `none`.
```
```
-/
def newBuiltin
  (argTps : List Tp)
  (outTp : Tp)
  (pred : {p : Prime} → (HList (Tp.denote p) argTps) → Prop)
  (comp : {p : Prime} → (args: HList (Tp.denote p) argTps) → (pred args) → (Tp.denote p outTp)) : Builtin := {
  omni := (builtinOmni argTps outTp pred comp)
  conseq := by
    unfold omni_conseq
    intros
    cases_type builtinOmni
    . constructor <;> simp_all
    . apply builtinOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type builtinOmni
    . constructor
      . constructor <;> tauto
    . apply builtinOmni.err <;> assumption
}

/--
For `s ∈ ℕ`, defines the addition of two `s`-bit uints: `(a b: Tp.denote (Tp.u s))`.
We make the following assumptions:
- If `(a + b) < 2^s`, then the builtin returns `(a + b) : Tp.denote (Tp.u s)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for unsigned integers `a`, `b` of bit-length `s`.
-/
def uAdd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a + b) < 2^s)
  (fun h![a, b] _ => a + b)

/--
For `s ∈ ℕ`, defines the multiplication of two `s`-bit uints: `(a b: Tp.denote (Tp.u s))`.
We make the following assumptions:
- If `(a * b) < 2^s`, then the builtin returns `(a * b) : Tp.denote (Tp.u s)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for unsigned integers `a`, `b` of bit-length `s`.
-/
def uMul {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a * b) < 2^s)
  (fun h![a, b] _ => a * b)

/--
For `s ∈ ℕ`, defines the subtraction of two `s`-bit uints: `(a b: Tp.denote (Tp.u s))`.
We make the following assumptions:
- If `(a - b) ≥ 0`, then the builtin returns `(a - b) : Tp.denote (Tp.u s)`
- Else (integer underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for unsigned integers `a`, `b` of bit-length `s`.
-/
def uSub {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => b ≤ a)
  (fun h![a, b] _ => a - b)

/--
For `s ∈ ℕ`, defines the division of two `s`-bit uints: `(a b: Tp.denote (Tp.u s))`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin returns `(a / b) : Tp.denote (Tp.u s)`
- Else (divide by zero), an exception is thrown.
- If `a / b` is not an integer, then the result is truncated.

In Noir, this builtin corresponds to `a / b` for unsigned integers `a`, `b` of bit-length `s`.
-/
def uDiv {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a / b)

/--
For `s ∈ ℕ`, defines the modulus of two `s`-bit uints: `(a b: Tp.denote (Tp.u s))`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin returns `(a % b) : Tp.denote (Tp.u s)`
- Else (mod by zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for unsigned integers `a`, `b` of bit-length `s`.
-/
def uRem {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a % b)

def bigIntAdd : Builtin := sorry
def bigIntSub : Builtin := sorry
def bigIntMul : Builtin := sorry
def bigIntDiv : Builtin := sorry
def bigIntFromLeBytes : Builtin := sorry
def bigIntToLeBytes : Builtin := sorry

/--
For `tp : Tp`, defines the indexing of a slice `l : Tp.denote (.slice tp)` with `i : Tp.denote (.u 32)`
We make the following assumptions:
- If `i < l.length`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T]` and `i: uint32`.
-/
def sliceIndex {tp} := newBuiltin
  [(.slice tp), (.u 32)] tp
  (fun h![l, i] => i.val < l.length)
  (fun h![l, i] v => l.get (Fin.mk i v))

/--
For `tp : Tp`, defines the builtin that returns the length of a slice `l : Tp.denote (.slice tp)`
We make the following assumptions:
- If `l.length < 2^32`, then the builtin returns `l.length : Tp.denote (.u 32)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `fn len(self) -> u32` implemented for `[T]`.
-/
def sliceLen {tp} := newBuiltin
  [(.slice tp)] (.u 32)
  (fun h![l] => l.length < 2^(32))
  (fun h![l] _ => l.length)

/--
For `tp : Tp`, defines the builtin that pushes back an element `e : Tp.denote tp` to a slice `l : Tp.denote (.slice tp)`.
On these inputs, the builtin is assumed to return `l ++ [e]`.

In Noir, this builtin corresponds to `fn push_back(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushBack {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => l ++ [e])

/--
For `tp : Tp`, defines the builtin that pushes front an element `e : Tp.denote tp` to a slice `l : Tp.denote (.slice tp)`.
On these inputs, the builtin is assumed to return `[e] ++ l`.

In Noir, this builtin corresponds to `fn push_front(self, elem: T) -> Self` implemented for `[T]`.
-/
def slicePushFront {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => [e] ++ l)

/--
For `tp : Tp`, defines the insertion of an element `e : Tp.denote tp` at index `i : Tp.denote (.u 32)` to a slice `l : Tp.denote (.slice tp)`.
We make the following assumptions:
- If `0 ≤ i < l.length`, then the builtin returns `l'`
where `l'` is `l` except that `e` is inserted at index `i`, and all the elements with indices larger than `i` are shifted to the right.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn insert(self, index: u32, elem: T) -> Self` implemented for `[T]`.
-/
def sliceInsert {tp} := newBuiltin
  [(.slice tp), (.u 32), tp] (.slice tp)
  (fun h![l, i, _] => i < l.length)
  (fun h![l, i, e] _ => List.insertNth i e l)

/--
For `tp : Tp`, defines the builtin that pops the first element of a slice `l : Tp.denote (.slice tp)`.
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
For `tp : Tp`, defines the builtin that pops the last element of a slice `l : Tp.denote (.slice tp)`.
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
For `tp : Tp`, defines the removal of the element at the index `i : Tp.denote (.u 32)` from a slice `l : Tp.denote (.slice tp)`.
We make the following assumptions:
- If `i < l.length`, then the builtin returns `(l', l[i])`
where `l'` is `l` except that the element at index `i` is removed, and all the elements with indices larger than `i` are shifted to the left.
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `fn remove(self, index: u32) -> (Self, T)` implemented for `[T]`.
-/
def sliceRemove {tp} := newBuiltin
  [(.slice tp), (.u 32)] (.struct [.slice tp, tp])
  (fun h![l, i] => i.val < l.length)
  (fun h![l, i] v => (l.eraseIdx i, (l.get (Fin.mk i v), ())))

def arrayLen : Builtin := sorry
def arrayAsSlice : Builtin := sorry

def strAsBytes : Builtin := sorry

def fToLeBits : Builtin := sorry
def fToBeBits : Builtin := sorry
def fToLeRadix : Builtin := sorry
def fToBeRadix : Builtin := sorry
def fApplyRangeConstraint : Builtin := sorry
def fModNumBits : Builtin := sorry
def fModBeBits : Builtin := sorry
def fModLeBits : Builtin := sorry
def fModBeBytes : Builtin := sorry
def fModLeBytes : Builtin := sorry

def zeroed : Builtin := sorry
def fromField : Builtin := sorry
def asField : Builtin := sorry
def asWitness : Builtin := sorry

def assertConstant : Builtin := sorry
def staticAssert : Builtin := sorry

def isUnconstrained : Builtin := sorry

def derivePedersenGenerators : Builtin := sorry

def qtAsTraitConstraint : Builtin := sorry
def qtAsType : Builtin := sorry

def traitConstraintEq : Builtin := sorry
def traintConstraintHash : Builtin := sorry

def traitDefAsTraitConstraint : Builtin := sorry

def structDefAsType : Builtin := sorry
def structDefGenerics : Builtin := sorry
def structDefFields : Builtin := sorry

end Lampe.Builtin
