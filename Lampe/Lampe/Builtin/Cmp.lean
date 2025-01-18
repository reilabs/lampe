import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the equality comparison between two units, which always returns `True`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `Unit`.
-/
def unitEq := newPureBuiltin
  ⟨[CTp.unit, CTp.unit], CTp.bool⟩
  (fun _ => ⟨True,
    fun _ => True⟩)

/--
Defines the equality comparison between two booleans.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `bool`.
-/
def bEq := newPureBuiltin
  ⟨[CTp.bool, CTp.bool], CTp.bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two field elements.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `Field`.
-/
def fEq := newPureBuiltin
  ⟨[CTp.field, CTp.field], CTp.bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two uints of size `s`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of uints.
-/
def uEq := newGenericPureBuiltin
  (fun s => ⟨[CTp.u s, CTp.u s], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two ints of size `s`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of ints.
-/
def iEq := newGenericPureBuiltin
  (fun s => ⟨[CTp.i s, CTp.i s], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two strings of length `n`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of `str<n>`.
-/
def strEq := newGenericPureBuiltin
  (fun n => ⟨[CTp.str n, CTp.str n], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)


/--
Defines the less-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a < b` for uints `a`, `b`.
-/
def uLt := newGenericPureBuiltin
  (fun s => ⟨[(CTp.u s), (CTp.u s)], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the less-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a < b` for ints `a`, `b`.
-/
def iLt := newGenericPureBuiltin
  (fun s => ⟨[(CTp.i s), (CTp.i s)], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the greater-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a > b` for uints `a`, `b`.
-/
def uGt := newGenericPureBuiltin
  (fun s => ⟨[(CTp.u s), (CTp.u s)], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)

/--
Defines the greater-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a > b` for ints `a`, `b`.
-/
def iGt := newGenericPureBuiltin
  (fun s => ⟨[(CTp.i s), (CTp.i s)], CTp.bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)
