import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

def tpEq {p : Prime} (tp : Tp) : Option (BEq (Tp.denote p tp)) :=
  match tp with
  -- references cannot be compared
  | .ref _ => none
  -- () == () always evaluates to true
  | .unit => some ⟨fun _ _ => true⟩
  | .bool => some ⟨fun a b => a == b⟩
  | .u _ => some ⟨fun a b => a == b⟩
  | .i _ => some ⟨fun a b => a == b⟩
  | .field => some ⟨fun a b => a == b⟩
  | .str _ => some ⟨fun a b => a == b⟩
  | .bi => some ⟨fun a b => a == b⟩
  -- two structs are equal if all of their fields can be compared and are equal
  | .struct fields =>
    match fields with
    | [] => some ⟨fun _ _ => true⟩
    | tp :: fs => do
      let f ← tpEq tp
      let g ← tpEq (.struct fs)
      some ⟨fun (a, a') (b, b') => (f.beq a b) && (g.beq a' b')⟩
  -- two arrays are equal if their elements can be compared and are equal
  | .array tp' _ => do
    let f ← tpEq tp'
    some ⟨fun a b => (a.toList.zip b.toList).all (fun (a, b) => f.beq a b)⟩
  -- two slices are equal if their lengths are equal and their elements can be compared and are equal
  | .slice tp' => do
    let f ← tpEq tp'
    some ⟨fun a b => a.length == b.length
      ∧ (a.zip b).all (fun (a, b) => f.beq a b)⟩

/--
Defines the equality comparison between two values of type `T : Tp.denote _ tp` where the equality operation is defined by `(tpEq _ tp)`.
If `T` cannot be compared, i.e., `tpEq _ tp` is `none`, then this builtin throws an exception.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `T`.
-/
def eq := newGenPureBuiltin
  (fun tp => ⟨[tp, tp], .bool⟩)
  (fun tp h![a, b] => ⟨(tpEq tp).isSome,
    fun h => ((tpEq tp).get h).beq a b⟩)

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
