import Mathlib

namespace Lampe

inductive Tp where
| int
| bool
deriving DecidableEq

@[reducible]
def InstanceOf : Tp → Type
| .int => Nat
| .bool => Bool

@[simp]
theorem InstanceOf.def {tp : Tp} : InstanceOf tp = match tp with
  | .int => Nat
  | .bool => Bool
  := by cases tp <;> rfl

instance : DecidableEq (InstanceOf tp) := fun a b => match tp with
  | .int => inferInstanceAs (DecidableEq Nat) a b
  | .bool => inferInstanceAs (DecidableEq Bool) a b

structure Value where
type : Tp
value : InstanceOf type
deriving DecidableEq

namespace Value

abbrev int (n : Nat) : Value := ⟨.int, n⟩
abbrev bool (b : Bool) : Value := ⟨.bool, b⟩

instance : Inhabited Value := ⟨Value.int 0⟩

@[simp]
theorem eq_int {a b : Nat} :  (int a == int b) = (a == b) := by
  simp [BEq.beq]

@[simp]
theorem true_eq_beq_iff_eq {a b : Value} : @Eq (InstanceOf .bool) true (a == b) ↔ a = b := by
  simp [InstanceOf]

end Value

end Lampe
