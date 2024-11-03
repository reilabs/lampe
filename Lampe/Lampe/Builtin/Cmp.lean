import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the equality comparison between unit values.
We assume that `() == ()` always evaluates to `true`.

In Noir, this builtin corresponds to `() == ()` implemented for `Unit`.
-/
def unitEq := newPureBuiltin
  ⟨[(.unit), (.unit)], .bool⟩
  (fun _ => ⟨True,
    fun _ => True⟩)

/--
Defines the equality comparison between boolean values.
We assume that the comparison between two boolean values evaluates to `true` if and only if they are equal.

In Noir, this builtin corresponds to `a == b` for booleans `a`, `b`.
 -/
def bEq := newPureBuiltin
  ⟨[(.bool), (.bool)], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b ⟩)

/--
Defines the equality comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if they are equal.

In Noir, this builtin corresponds to `a == b` for uints `a`, `b`.
 -/
def uEq := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a == b⟩)

/--
Defines the equality comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if they are equal.

In Noir, this builtin corresponds to `a == b` for ints `a`, `b`.
 -/
def iEq := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a == b⟩)

/--
Defines the equality comparison between field elements.
We assume that the comparison between two field elements evaluates to `true` if and only if they are equal.

In Noir, this builtin corresponds to `a == b` for field elements `a`, `b`.
 -/
def fEq := newPureBuiltin
  ⟨[(.field), (.field)], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b⟩)

/--
Defines the less-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a < b` for uints `a`, `b`.
-/
def uLt := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the less-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a < b` for ints `a`, `b`.
-/
def iLt := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the greater-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a > b` for uints `a`, `b`.
-/
def uGt := newGenPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)

/--
Defines the greater-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a > b` for ints `a`, `b`.
-/
def iGt := newGenPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)
