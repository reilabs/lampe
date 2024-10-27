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

-- Generic Builtin definition constructor
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

-- a + b
-- Assumption: Integer overflow throws a runtime exception.
def uAdd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a + b) < 2^s)
  (fun h![a, b] _ => a + b)

-- a * b
-- Assumption: Integer overflow throws a runtime exception.
def uMul {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a * b) < 2^s)
  (fun h![a, b] _ => a * b)

-- a - b
-- Assumption: Integer underflow throws a runtime exception.
def uSub {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => b ≤ a)
  (fun h![a, b] _ => a - b)

-- a / b
-- Assumption: Divide by zero throws a runtime exception.
def uDiv {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a / b)

-- a % b
-- Assumption: Mod by 0 throws a runtime exception.
def uRem {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a.val % b.val)

def iAdd : Builtin := sorry
def iSub : Builtin := sorry
def iMul : Builtin := sorry
def iDiv : Builtin := sorry
def iRem : Builtin := sorry
def iNeg : Builtin := sorry

def bigIntAdd : Builtin := sorry
def bigIntSub : Builtin := sorry
def bigIntMul : Builtin := sorry
def bigIntDiv : Builtin := sorry
def bigIntFromLeBytes : Builtin := sorry
def bigIntToLeBytes : Builtin := sorry

-- Assumption: Out of bounds access throws a runtime exception.
def sliceIndex {tp} := newBuiltin
  [(.slice tp), (.u 32)] tp
  (fun h![l, i] => i.val < l.length)
  (fun h![l, i] v => l.get (Fin.mk i v))

-- Assumption: If the slice's size cannot be represented by a u32, an exception is thrown.
def sliceLen {tp} := newBuiltin
  [(.slice tp)] (.u 32)
  (fun h![l] => l.length < 2^(32))
  (fun h![l] _ => l.length)

-- Assumption: Slices can grow infinitely.
def slicePushBack {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => l ++ [e])

-- Assumption: Slices can grow infinitely.
def slicePushFront {tp} := newBuiltin
  [(.slice tp), tp] (.slice tp)
  (fun _ => True)
  (fun h![l, e] _ => [e] ++ l)

-- Assumption: Trying to insert at an index that doesn't exist throws a runtime exception.
def sliceInsert {tp} := newBuiltin
  [(.slice tp), (.u 32), tp] (.slice tp)
  (fun h![l, i, _] => i < l.length)
  (fun h![l, i, e] _ => List.insertNth i e l)

-- Assumption: Popping from an empty slice throws a runtime exception.
def slicePopFront {tp} := newBuiltin
  [(.slice tp)] (.struct [tp, .slice tp])
  (fun h![l] => l ≠ [])
  (fun h![l] v => (l.head v, (l.tail, ())))

-- Assumption: Popping from an empty slice throws a runtime exception.
def slicePopBack {tp} := newBuiltin
  [(.slice tp)] (.struct [.slice tp, tp])
  (fun h![l] => l ≠ [])
  (fun h![l] v => (l.dropLast, (l.getLast v, ())))

-- Assumption (5): Removing an index that doesn't exist throws a runtime exception.
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
