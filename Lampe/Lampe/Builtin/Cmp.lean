import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `T`.
-/

def eq := newPureBuiltin
  ⟨[.field, .field], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b⟩)

def unitEq := newPureBuiltin
  ⟨[.unit, .unit], .bool⟩
  (fun _ => ⟨True,
    fun _ => true⟩)

def bEq := newPureBuiltin
  ⟨[.bool, .bool], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b⟩)

def uEq := newGenericPureBuiltin
  (fun s => ⟨[.u s, .u s], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a == b⟩)

def iEq := newGenericPureBuiltin
  (fun s => ⟨[.u s, .u s], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a == b⟩)

def fEq := newPureBuiltin
  ⟨[.field, .field], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b⟩)

def biEq := newPureBuiltin
  ⟨[.bi, .bi], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a == b⟩)

def strEq := newGenericPureBuiltin
  (fun n => ⟨[.str n, .str n], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a == b⟩)

/--
Defines the less-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a < b` for uints `a`, `b`.
-/
def uLt := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the less-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a < b` for ints `a`, `b`.
-/
def iLt := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a < b⟩)

/--
Defines the greater-than comparison between uint values of bit size `s`.
We assume that the comparison between two uints evaluates to `true` if and only if the first uint is less than the second uint.

In Noir, this builtin corresponds to `a > b` for uints `a`, `b`.
-/
def uGt := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)

/--
Defines the greater-than comparison between int values of bit size `s`.
We assume that the comparison between two ints evaluates to `true` if and only if the first int is less than the second uint.

In Noir, this builtin corresponds to `a > b` for ints `a`, `b`.
-/
def iGt := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a > b⟩)
