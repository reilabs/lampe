import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the addition of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a + b) < 2^s`, then the builtin evaluates to `(a + b) : U s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for uints `a`, `b` of bit size `s`.
-/
def uAdd := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toInt + b.toInt) < 2^s,
    fun _ => a + b⟩)

/--
Defines the multiplication of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a * b) < 2^s`, then the builtin evaluates to `(a * b) : U s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for uints `a`, `b` of bit size `s`.
-/
def uMul := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toInt * b.toInt) < 2^s,
    fun _ => a * b⟩)

/--
Defines the subtraction of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a - b) ≥ 0`, then the builtin evaluates to `(a - b) : U s`
- Else (integer underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for uints `a`, `b` of bit size `s`.
-/
def uSub := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≤ a,
    fun _ => a - b⟩)

/--
Defines the division of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a / b) : U s`
- Else (divide by zero), an exception is thrown.
- If `a / b` is not an integer, then the result is truncated.

In Noir, this builtin corresponds to `a / b` for uints `a`, `b` of bit size `s`.
-/
def uDiv := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.udiv b⟩)

/--
Defines the modulus of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a % b) : U s`
- Else (mod by zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for uints `a`, `b` of bit size `s`.
-/
def uRem := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a % b⟩)

/--
Defines the addition of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a + b) < 2^(s-1)`, then the builtin evaluates to `(a + b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for signed ints `a`, `b` of bit size `s`.
-/
def iAdd := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt + b.toInt),
    fun _ => a + b⟩)

/--
Defines the subtraction of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a - b) < 2^(s-1)`, then the builtin evaluates to `(a - b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for signed ints `a`, `b` of bit size `s`.
-/
def iSub := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt - b.toInt),
    fun _ => a - b⟩)

/--
Defines the multiplication of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a * b) < 2^(s-1)`, then the builtin evaluates to `(a * b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for signed ints `a`, `b` of bit size `s`.
-/
def iMul := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt * b.toInt),
    fun _ => a * b⟩)

/--
Defines the division of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a.sdiv b) : I s`
- Else (division-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a / b` for signed ints `a`, `b` of bit size `s`.
-/
def iDiv := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.sdiv b⟩)

/--
Captures the behavior of the signed integer remainder operation % in Noir.
In particular, for two signed integers `a` and `b`, this returns ` a - ((a.sdiv b) * b)`
-/
def intRem {s: Nat} (a b : I s) : I s := (a - (a.sdiv b) * b)

#eval intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) -- 0
#eval intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-3)) -- -2
#eval intRem (BitVec.ofInt 8 (6)) (BitVec.ofInt 8 (-100)) -- 6
#eval intRem (BitVec.ofInt 8 (127)) (BitVec.ofInt 8 (-3)) -- 1

/--
Defines the integer remainder operation between two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(intRem a b) : I s`
- Else (mod-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for signed ints `a`, `b` of bit size `s`.
-/
def iRem := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => intRem a b⟩)

/--
Defines the negation of a `s`-bit int: `a: I s`.
We make the following assumptions:
- If `-2^(s-1) ≤ -a < 2^(s-1)`, then the builtin evaluates to `-a : I s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `-a` for a signed integer `a` of bit size `s`.
-/
def iNeg := newGenPureBuiltin
  (fun s => ⟨[(.i s)], (.i s)⟩)
  (fun s h![a] => ⟨bitsCanRepresent s (-a.toInt),
    fun _ => -a⟩)

/--
Defines the addition of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a + b) : Fp p`.

In Noir, this builtin corresponds to `a + b` for field elements `a`, `b`.
-/
def fAdd := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a + b⟩)

/--
Defines the multiplication of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a * b) : Fp p`.

In Noir, this builtin corresponds to `a * b` for field elements `a`, `b`.
-/
def fMul := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a * b⟩)

/--
Defines the subtraction of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a - b) : Fp p`.

In Noir, this builtin corresponds to `a - b` for field elements `a`, `b`.
-/
def fSub := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a - b⟩)

/--
Defines the division of two field elements `(a b: Fp p)` in `ZMod p`.
We assume the following:
- If `b ≠ 0`, it evaluates to `(a / b) : Fp p`.
- Else, an exception is thrown.

In Noir, this builtin corresponds to `a / b` for field elements `a`, `b`.
-/
def fDiv := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨b ≠ 0,
    fun _ => a / b⟩)

/--
Defines the additive inverse of a field element `a: Fp p` in `ZMod p`.
This is assumed to evaluate to `-a : Fp p`.

In Noir, this builtin corresponds to `-a` for a field element `a`.
-/
def fNeg := newPureBuiltin
  ⟨[(.field)], .field⟩
  (fun h![a] => ⟨True,
    fun _ => -a⟩)

end Lampe.Builtin