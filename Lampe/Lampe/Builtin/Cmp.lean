import Lampe.Builtin.Basic
namespace Lampe.Builtin

inductive EqTp : Tp → Prop
  | u s : EqTp (.u s)
  | i s : EqTp (.i s)
  | field : EqTp .field
  | bi : EqTp .bi
  | bool : EqTp .bool
  | unit : EqTp .unit
  | str n : EqTp (.str n)

@[reducible]
def eqOp (_ : EqTp tp) (a b : tp.denote p) : Tp.denote p .bool :=
  match tp with
  -- () == () is always true
  | .unit => true
  | .u _ => a == b
  | .i _ => a == b
  | .bool => a == b
  | .field => a == b
  | .bi => a == b
  | .str _ => a == b

def eq_ := newGenericPureBuiltin
  (fun tp => ⟨[tp, tp], .bool⟩)
  (fun tp h![a, b] => ⟨EqTp tp, fun h => eqOp (by tauto) a b⟩)

inductive eqOmni : Omni where
| unit {p st Q} : Q (some (st, true)) → eqOmni p st [.unit, .unit] .bool h![a, b] Q
| u {p st a b Q} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.u s, .u s] .bool h![a, b] Q
| i {p st a b Q} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.i s, .i s] .bool h![a, b] Q
| bool {p st a b Q} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.bool, .bool] .bool h![a, b] Q
| field {p st Q a b} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.field, .field] .bool h![a, b] Q
| bi {p st Q a b} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.bi, .bi] .bool h![a, b] Q
| str {p st Q a b} : Q (some (st, eqOp (by tauto) a b)) → eqOmni p st [.str n, .str n] .bool h![a, b] Q
| _ {p st tp a b Q} : Q none → eqOmni p st [tp, tp] .bool h![a, b] Q

/--
Defines the equality comparison between values.

In Noir, this builtin corresponds to `a == b` for values `a`, `b` of type `T`.
-/
def eq : Builtin := {
  omni := eqOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type eqOmni <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type eqOmni <;> (constructor; try constructor; tauto)
    tauto
}

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
