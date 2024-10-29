import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

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


end Lampe.Builtin
