import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the negation of a bool: `a: Bool`
which evaluates to `(¬a) : Bool`.

In Noir, this builtin corresponds to `!a` for bool `a`.
-/
def bNot := newBuiltin
  [(.bool)] .bool
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the logical OR of two bools: `(a b: Bool)`
which evaluates to `(a || b) : Bool`.

In Noir, this builtin corresponds to `a | b` for bools `a`, `b`.
-/
def bOr := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a || b)

/--
Defines the logical AND of two bools: `(a b: Bool)`
which evaluates to `(a && b) : Bool`.

In Noir, this builtin corresponds to `a & b` for bools `a`, `b`.
-/
def bAnd := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a && b)

/--
Defines the logical XOR of two bools: `(a b: Bool)`
which evaluates to `(a.xor b) : Bool`.

In Noir, this builtin corresponds to `a ^ b` for bools `a`, `b`.
-/
def bXor := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)

/--
Defines the bitwise negation of an `s`-bit uint: `a: U s`
which evaluates to `(¬a) : U s`.

In Noir, this builtin corresponds to `!a` for uint `a` of bit-size `s`.
-/
def uNot {s} := newBuiltin
  [(.u s)] (.u s)
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the bitwise OR of two `s`-bit uints: `(a b: U s)`
which evaluates to `(a ||| b) : U s`.

In Noir, this builtin corresponds to `a | b` for uints `a`, `b` of bit-size `s`.
-/
def uOr {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a ||| b)

/--
Defines the bitwise AND of two `s`-bit uints: `(a b: U s)`
which evaluates to `(a &&& b) : U s`.

In Noir, this builtin corresponds to `a & b` for uints `a`, `b` of bit-size `s`.
-/
def uAnd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a &&& b)

/--
Defines the bitwise XOR of two `s`-bit uints: `(a b: U s)`
which evaluates to `(a.xor b) : U s`.

In Noir, this builtin corresponds to `a ^ b` for uints `a`, `b` of bit-size `s`.
-/
def uXor {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)

/--
Defines the bitwise left shift of an `s`-bit uint `a: U s`
with an amount represented by an 8-bit uint `b : U 8`.
This is assumed to evaluate to `(a <<< b) : U s`.

In Noir, this builtin corresponds to `a << b` for an uint `a` of bit-size `s` and an uint `b` of bit-size `8`.
-/
def uShl {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a <<< b)

/--
Defines the bitwise right shift of an `s`-bit uint `a: U s`
with an amount represented by an 8-bit uint `b : U 8`.
This is assumed to evaluate to `(a >>> b) : U s`.

In Noir, this builtin corresponds to `a >> b` for an uint `a` of bit-size `s` and an uint `b` of bit-size `8`.
-/
def uShr {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a >>> b)

/--
Defines the bitwise negation of an `s`-bit int: `a: I s`
which evaluates to `(¬a) : U s`.

In Noir, this builtin corresponds to `!a` for an int `a` of bit-size `s`.
-/
def iNot {s} := newBuiltin
  [(.i s)] (.i s)
  (fun _ => True)
  (fun h![a] _ => a.not)

/--
Defines the bitwise OR of two `s`-bit ints: `(a b: I s)`
which evaluates to `(a ||| b) : I s`.

In Noir, this builtin corresponds to `a | b` for ints `a`, `b` of bit-size `s`.
-/
def iOr {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a ||| b)

/--
Defines the bitwise AND of two `s`-bit ints: `(a b: I s)`
which evaluates to `(a &&& b) : I s`.

In Noir, this builtin corresponds to `a & b` for ints `a`, `b` of bit-size `s`.
-/
def iAnd {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a &&& b)

/--
Defines the bitwise XOR of two `s`-bit ints: `(a b: I s)`
which evaluates to `(a.xor b) : I s`.

In Noir, this builtin corresponds to `a ^ b` for ints `a`, `b` of bit-size `s`.
-/
def iXor {s} := newBuiltin
  [(.u s), (.u s)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a.xor b)

/--
Defines the bitwise left shift of an `s`-bit int `a: I s`
with an amount represented by an 8-bit uint `b : U 8`.
This is assumed to evaluate to `(a <<< b) : I s`.

In Noir, this builtin corresponds to `a << b` for an int `a` of bit-size `s` and an uint `b` of bit-size `8`.
-/
def iShl {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a <<< b)

/--
Defines the bitwise right shift of an `s`-bit int `a: I s`
with an amount represented by an 8-bit uint `b : U 8`.
This is assumed to evaluate to `(a >>> b) : I s`.

In Noir, this builtin corresponds to `a >> b` for an int `a` of bit-size `s` and an uint `b` of bit-size `8`.
-/
def iShr {s} := newBuiltin
  [(.u s), (.u 8)] (.u s)
  (fun _ => True)
  (fun h![a, b] _ => a >>> b)


end Lampe.Builtin
