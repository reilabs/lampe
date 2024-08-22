import Mathlib

namespace Lampe

variable (P : Nat)

inductive Tp where
| u64
| bool
| unit
| field
| slice : Tp → Tp
deriving DecidableEq

@[reducible]
def InstanceOf : Tp → Type
| .field => ZMod P
| .u64 => UInt64
| .bool => Bool
| .slice tp => List (InstanceOf tp)
| .unit => Unit

@[simp]
theorem InstanceOf.def {tp : Tp} : InstanceOf P tp = match tp with
  | .u64 => UInt64
  | .bool => Bool
  | .unit => Unit
  | .field => ZMod P
  | .slice tp => List (InstanceOf P tp)
  := by cases tp <;> rfl

def InstanceOf.decidableEq : DecidableEq (InstanceOf P tp) := match tp with
  | .u64 => inferInstanceAs (DecidableEq UInt64)
  | .bool => inferInstanceAs (DecidableEq Bool)
  | .unit => inferInstanceAs (DecidableEq Unit)
  | .field => inferInstanceAs (DecidableEq (ZMod P))
  | .slice tp1 =>
    let _ : DecidableEq (InstanceOf P tp1) := decidableEq
    inferInstanceAs (DecidableEq (List (InstanceOf P tp1)))

instance : DecidableEq (InstanceOf P tp) := InstanceOf.decidableEq P

structure Value where
type : Tp
value : InstanceOf P type
deriving DecidableEq

namespace Value

abbrev u64 (i : UInt64) : Value P := ⟨.u64, i⟩
abbrev bool (b : Bool) : Value P := ⟨.bool, b⟩
abbrev unit : Value P := ⟨.unit, ()⟩

instance : Inhabited (Value P) := ⟨Value.unit P⟩

@[simp]
theorem eq_int {a b : UInt64} :  (u64 P a == u64 P b) = (a == b) := by
  simp [BEq.beq]

@[simp]
theorem true_eq_beq_iff_eq {a b : Value P} : @Eq (InstanceOf P .bool) true (a == b) ↔ a = b := by
  simp [InstanceOf]

end Value

end Lampe
