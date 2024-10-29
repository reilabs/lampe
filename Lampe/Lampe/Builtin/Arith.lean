import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

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

end Lampe.Builtin
