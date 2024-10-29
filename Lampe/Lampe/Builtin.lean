import Lampe.State
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.SeparationLogic
import Lampe.Helpers
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
Defines the negation of a bool: `a: Tp.denote Tp.bool`
which evaluates to `(¬a) : Tp.denote Tp.bool`.

In Noir, this builtin corresponds to `!a` for bool `a`.
-/

def bNot := newBuiltin
  [(.bool)] .bool
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the OR of two bools: `(a b: Tp.denote Tp.bool)`
which evaluates to `(a || b) : Tp.denote Tp.bool`.

In Noir, this builtin corresponds to `a | b` for bools `a`, `b`.
-/
def bOr := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a || b)

/--
Defines the AND of two bools: `(a b: Tp.denote Tp.bool)`
which evaluates to `(a && b) : Tp.denote Tp.bool`.

In Noir, this builtin corresponds to `a & b` for bools `a`, `b`.
-/
def bAnd := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a && b)

/--
Defines the XOR of two bools: `(a b: Tp.denote Tp.bool)`
which evaluates to `(a.xor b) : Tp.denote Tp.bool`.

In Noir, this builtin corresponds to `a ^ b` for bools `a`, `b`.
-/
def bXor := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)


/--
Defines the addition of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`.
We make the following assumptions:
- If `(a + b) < 2^s`, then the builtin returns `(a + b) : Tp.denote _ (Tp.u s)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for uints `a`, `b` of width `s`.
-/
def uAdd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a + b) < 2^s)
  (fun h![a, b] _ => a + b)

/--
Defines the multiplication of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`.
We make the following assumptions:
- If `(a * b) < 2^s`, then the builtin returns `(a * b) : Tp.denote _ (Tp.u s)`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for uints `a`, `b` of width `s`.
-/
def uMul {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => (a * b) < 2^s)
  (fun h![a, b] _ => a * b)

/--
Defines the subtraction of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`.
We make the following assumptions:
- If `(a - b) ≥ 0`, then the builtin returns `(a - b) : Tp.denote _ (Tp.u s)`
- Else (integer underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for uints `a`, `b` of width `s`.
-/
def uSub {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![a, b] => b ≤ a)
  (fun h![a, b] _ => a - b)

/--
Defines the division of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin returns `(a / b) : Tp.denote _ (Tp.u s)`
- Else (divide by zero), an exception is thrown.
- If `a / b` is not an integer, then the result is truncated.

In Noir, this builtin corresponds to `a / b` for uints `a`, `b` of width `s`.
-/
def uDiv {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a.udiv b)

/--
Defines the modulus of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin returns `(a % b) : Tp.denote _ (Tp.u s)`
- Else (mod by zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for uints `a`, `b` of width `s`.
-/
def uRem {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a % b)

/--
Defines the bitwise negation of an `s`-bit uint: `a: Tp.denote _ (Tp.u s)`
which evaluates to `(¬a) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `!a` for uint `a` of width `s`.
-/
def uNot {s} := newBuiltin
  [(.u s)] (.u s)
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the bitwise OR of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`
which evaluates to `(a ||| b) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `a | b` for uints `a`, `b` of width `s`.
-/
def uOr {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a ||| b)

/--
Defines the bitwise AND of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`
which evaluates to `(a &&& b) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `a & b` for uints `a`, `b` of width `s`.
-/
def uAnd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a &&& b)

/--
Defines the bitwise XOR of two `s`-bit uints: `(a b: Tp.denote _ (Tp.u s))`
which evaluates to `(a.xor b) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `a ^ b` for uints `a`, `b` of width `s`.
-/
def uXor {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)

/--
Defines the bitwise left shift of an `s`-bit uint `a: Tp.denote _ (Tp.u s)`
with an amount represented by an 8-bit uint `b : Tp.denote _ (Tp.u 8)`.
This is assumed to evaluate to `(a <<< b) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `a <<< b` for an uint `a` of width `s` and an uint `b` of width `8`.
-/
def uShl {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a <<< b)

/--
Defines the bitwise right shift of an `s`-bit uint `a: Tp.denote _ (Tp.u s)`
with an amount represented by an 8-bit uint `b : Tp.denote _ (Tp.u 8)`.
This is assumed to evaluate to `(a >>> b) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `a >>> b` for an uint `a` of width `s` and an uint `b` of width `8`.
-/
def uShr {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a >>> b)

/--
Defines the addition of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a + b) < 2^(s-1)`, then the builtin returns `(a + b) : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for signed ints `a`, `b` of width `s`.
-/
def iAdd {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] (.i s)
  (fun h![a, b] => canContain s (a.toInt + b.toInt))
  (fun h![a, b] _ => a + b)

/--
Defines the subtraction of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a - b) < 2^(s-1)`, then the builtin returns `(a - b) : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for signed ints `a`, `b` of width `s`.
-/
def iSub {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] (.i s)
  (fun h![a, b] => canContain s (a.toInt - b.toInt))
  (fun h![a, b] _ => a - b)

/--
Defines the multiplication of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a * b) < 2^(s-1)`, then the builtin returns `(a * b) : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for signed ints `a`, `b` of width `s`.
-/
def iMul {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] (.i s)
  (fun h![a, b] => canContain s (a.toInt * b.toInt))
  (fun h![a, b] _ => a * b)

/--
Defines the division of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a / b) < 2^(s-1)` and `b ≠ 0`, then the builtin returns `(a / b) : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow or division-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a / b` for signed ints `a`, `b` of width `s`.
-/
def iDiv {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] (.i s)
  (fun h![a, b] => canContain s (a.toInt / b.toInt) ∧ b ≠ 0)
  (fun h![a, b] _ => a.sdiv b)

/--
Defines the modulus of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a % b) < 2^(s-1)` and `b ≠ 0`, then the builtin returns `(a % b) : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow or mod-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for signed ints `a`, `b` of width `s`.
-/
def iRem {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] (.i s)
  (fun h![a, b] => canContain s (a.toInt % b.toInt) ∧ b ≠ 0)
  (fun h![a, b] _ => a % b)

/--
Defines the negation of a `s`-bit int: `a: Tp.denote _ (Tp.i s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ -a < 2^(s-1)`, then the builtin returns `-a : Tp.denote _ (Tp.i s)`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `-a` for a signed integer `a` of width `s`.
-/
def iNeg {s : Nat}: Builtin := newBuiltin
  [(.i s)] (.i s)
  (fun h![a] => canContain s (-a.toInt))
  (fun h![a] _ => -a)

/--
Defines the bitwise negation of an `s`-bit int: `a: Tp.denote _ (Tp.i s)`
which evaluates to `(¬a) : Tp.denote _ (Tp.u s)`.

In Noir, this builtin corresponds to `!a` for an int `a` of width `s`.
-/
def iNot {s} := newBuiltin
  [(.i s)] (.i s)
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the bitwise OR of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`
which evaluates to `(a ||| b) : Tp.denote _ (Tp.i s)`.

In Noir, this builtin corresponds to `a | b` for ints `a`, `b` of width `s`.
-/
def iOr {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a ||| b)

/--
Defines the bitwise AND of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`
which evaluates to `(a &&& b) : Tp.denote _ (Tp.i s)`.

In Noir, this builtin corresponds to `a & b` for ints `a`, `b` of width `s`.
-/
def iAnd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a &&& b)

/--
Defines the bitwise XOR of two `s`-bit ints: `(a b: Tp.denote _ (Tp.i s))`
which evaluates to `(a.xor b) : Tp.denote _ (Tp.i s)`.

In Noir, this builtin corresponds to `a ^ b` for ints `a`, `b` of width `s`.
-/
def iXor {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)

/--
Defines the bitwise left shift of an `s`-bit int `a: Tp.denote _ (Tp.i s)`
with an amount represented by an 8-bit uint `b : Tp.denote _ (Tp.u 8)`.
This is assumed to evaluate to `(a <<< b) : Tp.denote _ (Tp.i s)`.

In Noir, this builtin corresponds to `a <<< b` for an int `a` of width `s` and an uint `b` of width `8`.
-/
def iShl {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a <<< b)

/--
Defines the bitwise right shift of an `s`-bit int `a: Tp.denote _ (Tp.i s)`
with an amount represented by an 8-bit uint `b : Tp.denote _ (Tp.u 8)`.
This is assumed to evaluate to `(a >>> b) : Tp.denote _ (Tp.i s)`.

In Noir, this builtin corresponds to `a >>> b` for an int `a` of width `s` and an uint `b` of width `8`.
-/
def iShr {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a >>> b)

/--
Defines the addition of two field elements `(a b: Tp.denote p Tp.field)` in `ZMod p`.
This is assumed to evaluate to `(a + b) : Tp.denote p Tp.field`.

In Noir, this builtin corresponds to `a + b` for field elements `a`, `b`.
-/
def fAdd : Builtin := newBuiltin
  [(.field), (.field)] .field
  (fun _ => True)
  (fun h![a, b] _ => a + b)

/--
Defines the multiplication of two field elements `(a b: Tp.denote p Tp.field)` in `ZMod p`.
This is assumed to evaluate to `(a * b) : Tp.denote p Tp.field`.

In Noir, this builtin corresponds to `a * b` for field elements `a`, `b`.
-/
def fMul : Builtin := newBuiltin
  [(.field), (.field)] .field
  (fun _ => True)
  (fun h![a, b] _ => a * b)

/--
Defines the subtraction of two field elements `(a b: Tp.denote p Tp.field)` in `ZMod p`.
This is assumed to evaluate to `(a - b) : Tp.denote p Tp.field`.

In Noir, this builtin corresponds to `a - b` for field elements `a`, `b`.
-/
def fSub : Builtin := newBuiltin
  [(.field), (.field)] .field
  (fun _ => True)
  (fun h![a, b] _ => a - b)

/--
Defines the division of two field elements `(a b: Tp.denote p Tp.field)` in `ZMod p`.
We assume the following:
- If `b ≠ 0`, it evaluates to `(a / b) : Tp.denote p Tp.field`.
- Else, an exception is thrown.

In Noir, this builtin corresponds to `a / b` for field elements `a`, `b`.
-/
def fDiv : Builtin := newBuiltin
  [(.field), (.field)] .field
  (fun h![_, b] => b ≠ 0)
  (fun h![a, b] _ => a / b)

/--
Defines the additive inverse of a field element `a: Tp.denote p Tp.field` in `ZMod p`.
This is assumed to evaluate to `-a : Tp.denote p Tp.field`.

In Noir, this builtin corresponds to `-a` for a field element `a`.
-/
def fNeg : Builtin := newBuiltin
  [(.field)] .field
  (fun _ => True)
  (fun h![a] _ => -a)

/--
For a field element `a : Tp.denote p Tp.field` in `ZMod p`, and a bit size `w : Tp.denote p (Tp.u 32)`,
we assume the following:
- If `a < 2^w`, then this builtin evaluates to a list of 1-bit uints `l`, which is the little-endian bit representation of `a`.
Note that `l` is padded up to `w` elements with `0`.
- Otherwise, an exception is thrown.

In Noir, this builtin corresponds to ` fn __to_le_bits(self, bit_size: u32) -> [u1]` implemented for `Field`.
-/
def fToLeBits : Builtin := newBuiltin
  [(.field), (.u 32)] (.slice (.u 1))
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun h![a, w] _ => extList
    (withRadix 2 a.val (by tauto)) (w.toNat) 0)

/--
For a field element `a : Tp.denote p Tp.field` in `ZMod p`, and a bit size `w : Tp.denote p (Tp.u 32)`,
we assume the following:
- If `a < 2^w`, then this builtin evaluates to a list of 1-bit uints `l`, which is the big-endian bit representation of `a`.
Note that `l` is padded down to `w` elements with `0`.
- Otherwise, an exception is thrown.

In Noir, this builtin corresponds to ` fn __to_be_bits(self, bit_size: u32) -> [u1]` implemented for `Field`.
-/
def fToBeBits : Builtin := newBuiltin
  [(.field), (.u 32)] (.slice (.u 1))
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun h![a, w] _ => .reverse (extList
    (withRadix 2 a.val (by tauto)) (w.toNat) 0))

/--
Assumption: 1 < rad < 256
In Noir, this builtin corresponds to `fn __to_le_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToLeRadix : Builtin := newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, l] _ => extList
    (withRadix rad.toNat a.val (by tauto)) l.toNat 0)

/--
Assumption: 1 < rad < 256
In Noir, this builtin corresponds to `fn __to_be_radix(self, radix: u32, result_len: u32) -> [u8]` implemented for `Field`.
-/
def fToBeRadix : Builtin :=  newBuiltin
  [(.field), (.u 32), (.u 32)] (.slice (.u 8))
  (fun h![_, rad, _] => 1 < rad ∧ rad < 256)
  (fun h![a, rad, l] _ => .reverse (extList
    (withRadix rad.toNat a.val (by tauto)) l.toNat 0))

/--
Assumption: a < 2^w
In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented for `Field`.
-/
def fApplyRangeConstraint : Builtin := newBuiltin
  [.field, (.u 32)] .unit
  (fun h![a, w] => a.val < 2^w.toNat)
  (fun _ _ => ())

/--
Assumption: p < 2^64
In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits : Builtin := newBuiltin
  [.field] (.u 64)
  (@fun P _ => P.val < 2^64)
  (@fun P h![_] _ => numBits P.val)

/--

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 2 p.val (by tauto))

/--

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits : Builtin := newBuiltin
  [.field] (.slice (.u 1))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 2 p.val (by tauto)))

/--

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => withRadix 256 p.val (by linarith))

/--

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes : Builtin := newBuiltin
  [.field] (.slice (.u 8))
  (@fun p _ => True)
  (@fun p h![_] _ => .reverse (withRadix 256 p.val (by linarith)))

/--
Defines the addition of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a + b`.

In Noir, this builtin corresponds to `a + b` for bigints `a`, `b`.
-/
def bigIntAdd : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a + b)

/--
Defines the subtraction of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a - b`.

In Noir, this builtin corresponds to `a - b` for bigints `a`, `b`.
-/
def bigIntSub : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a - b)

/--
Defines the multiplication of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a * b`.

In Noir, this builtin corresponds to `a * b` for bigints `a`, `b`.
-/
def bigIntMul : Builtin := newBuiltin
  [.bi, .bi] (.bi)
  (fun _ => True)
  (fun h![a, b] _  => a * b)

/--
Defines the division of two bigints `(a b : Tp.denote Tp.bi)`.
The builtin is assumed to return `a / b`.

In Noir, this builtin corresponds to `a / b` for bigints `a`, `b`.
-/
def bigIntDiv : Builtin := newBuiltin
  [.bi, .bi] .bi
  (fun _ => True)
  (fun h![a, b] _  => a / b)

/-- Not implemented yet.

In Noir, this builtin corresponds to `fn from_le_bytes(bytes: [u8], modulus: [u8])` implemented for `BigInt`.
 -/
def bigIntFromLeBytes : Builtin := newBuiltin
  [.slice (.u 8), .slice (.u 8)] .bi
  (fun _ => True)
  (fun h![bs, m] _ => sorry)

/--
Defines the conversion of `a : Tp.denote .bi` to its byte slice representation `l : Tp.denote _ (.slice (.u 8))` in little-endian encoding.
Note that `l` always contains 32 elements. Hence, for integers that can be represented by less than 32 bytes, the higher bytes are set to zero.

We make the following assumptions:
- If `a` cannot be represented by 32 bytes, an exception is thrown
- Else, the builtin returns `l`.

In Noir, this builtin corresponds to `fn to_le_bytes(self) -> [u8; 32]` implemented for `BigInt`.
-/
def bigIntToLeBytes : Builtin := newBuiltin
  [.bi] (.slice (.u 8))
  (fun h![a] => canContain 256 a)
  (fun h![a] _ => chunksOf (BitVec.ofInt 256 a) 8 (by linarith))

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

def arrayLen : Builtin := sorry
def arrayAsSlice : Builtin := sorry

def strAsBytes : Builtin := sorry

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
