import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the equality comparison between two units, which always returns `True`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `Unit`.
-/
def unitEq := newPureBuiltin
  ⟨[.unit, .unit], .bool⟩
  (fun _ => ⟨True,
    fun _ => True⟩)

/--
Defines the equality comparison between two booleans.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `bool`.
-/
def bEq := newPureBuiltin
  ⟨[.bool, .bool], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two field elements.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `Field`.
-/
def fEq := newPureBuiltin
  ⟨[.field, .field], .bool⟩
  (fun h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two uints of size `s`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of uints.
-/
def uEq := newGenericPureBuiltin
  (fun s => ⟨[.u s, .u s], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two ints of size `s`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of ints.
-/
def iEq := newGenericPureBuiltin
  (fun s => ⟨[.i s, .i s], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)

/--
Defines the equality comparison between two strings of length `n`.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of `str<n>`.
-/
def strEq := newGenericPureBuiltin
  (fun n => ⟨[.str n, .str n], .bool⟩)
  (fun _ h![a, b] => ⟨True,
    fun _ => a = b⟩)


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

class EqTp (tp : Tp) where
  eq {p} : (a b : tp.denote p) → Bool

class NeqTp (tp : Tp) where
  neq {p} : (a b : tp.denote p) → Bool

class LtTp (tp : Tp) where
  lt {p} : (a b : tp.denote p) → Bool

class LeqTp (tp : Tp) where
  leq {p} : (a b : tp.denote p) → Bool

class GtTp (tp : Tp) where
  gt {p} : (a b : tp.denote p) → Bool

class GeqTp (tp : Tp) where
  geq {p} : (a b : tp.denote p) → Bool

instance : EqTp .unit where
  eq := fun _ _ => True

instance : EqTp .bool where
  eq := fun a b => a = b

instance : EqTp .field where
  eq := fun a b => a = b

instance : EqTp (.u s) where
  eq := fun a b => a = b

instance : EqTp (.i s) where
  eq := fun a b => a = b

instance : EqTp (.str n) where
  eq := fun a b => a = b

inductive eqOmni : Omni where
| eq {p st tp a b Q} [EqTp tp] :
  Q (some (st, EqTp.eq a b)) → eqOmni p st [tp, tp] .bool h![a, b] Q

def eq : Builtin := {
  omni := eqOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type eqOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type eqOmni
    constructor
    simp only [SLP.star]
    tauto
}

instance : NeqTp .unit where
  neq := fun _ _ => False

instance : NeqTp .bool where
  neq := fun a b => a != b

instance : NeqTp .field where
  neq := fun a b => a != b

instance : NeqTp (.u s) where
  neq := fun a b => a != b

instance : NeqTp (.i s) where
  neq := fun a b => a != b

instance : NeqTp (.str n) where
  neq := fun a b => a != b

inductive neqOmni : Omni where
| neq {p st tp a b Q} [NeqTp tp] :
  Q (some (st, NeqTp.neq a b)) → neqOmni p st [tp, tp] .bool h![a, b] Q

def neq : Builtin := {
  omni := neqOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type neqOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type neqOmni
    constructor
    simp only [SLP.star]
    tauto
}

instance : LtTp (.u s) where
  lt := fun a b => a < b

instance : LtTp (.i s) where
  lt := fun a b => a < b

inductive ltOmni : Omni where
| lt {p st tp a b Q} [LtTp tp] :
  Q (some (st, LtTp.lt a b)) → ltOmni p st [tp, tp] .bool h![a, b] Q

def lt : Builtin := {
  omni := ltOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type ltOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type ltOmni
    constructor
    simp only [SLP.star]
    tauto
}
