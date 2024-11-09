import Lampe.Builtin.Basic
namespace Lampe.Builtin

/-- Defines the types that are arithmetic -/
inductive ArithTp : Tp → Prop
  | u s : ArithTp (.u s)
  | i s : ArithTp (.i s)
  | field : ArithTp .field
  | bi : ArithTp .bi

/-- Defines the semantics of a successful addition operation -/
def addOp (_ : ArithTp tp) (a b : tp.denote p) : tp.denote p :=
  match tp with
  | .u _ => a + b
  | .i _ => a + b
  | .field => a + b
  | .bi => a + b

/-- Defines the semantics of a successful subtraction operation -/
def subOp (_ : ArithTp tp) (a b : tp.denote p) : tp.denote p :=
  match tp with
  | .u _ => a - b
  | .i _ => a - b
  | .field => a - b
  | .bi => a - b

/-- Defines the semantics of a successful multiplication operation -/
def mulOp (_ : ArithTp tp) (a b : tp.denote p) : tp.denote p :=
  match tp with
  | .u _ => a * b
  | .i _ => a * b
  | .field => a * b
  | .bi => a * b

/-- Defines the semantics of a successful division operation -/
def divOp (_ : ArithTp tp) (a b : tp.denote p) : tp.denote p :=
  match tp with
  | .u _ => a.udiv b
  | .i _ => a.sdiv b
  | .field => a * b
  | .bi => a * b

/-- Ensures the operation given with `intOp` when applied to `a` and `b`'s int representation doesn't overflow. -/
def noOverflow {tp : Tp}
  (a b : tp.denote p)
  (intOp : Int → Int → Int) : Prop := match tp with
| .u s => (intOp a.toInt b.toInt) < 2^s
| .i s => bitsCanRepresent s (intOp a.toInt b.toInt)
| .field => True
| .bi => True
| _ => False

inductive addOmni : Omni where
| u {p st s a b Q} :
  (noOverflow a b (·+·) → Q (some (st, addOp (by tauto) a b)))
  → (¬noOverflow a b (·+·) → Q none)
  → addOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (noOverflow a b (·+·) → Q (some (st, addOp (by tauto) a b)))
  → (¬noOverflow a b (·+·) → Q none)
  → addOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, addOp (by tauto) a b))
  → addOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, addOp (by tauto) a b))
  → addOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → addOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the addition builtin.

In Noir, this corresponds to the addition of two values with `+`.
-/
def add : Builtin := {
  omni := addOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type addOmni <;> tauto
    repeat (constructor; aesop; aesop)
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type addOmni
    rename_i s a b _ _ _
    repeat (first | constructor | tauto | intro)
}

inductive mulOmni : Omni where
| u {p st s a b Q} :
  (noOverflow a b (·*·) → Q (some (st, mulOp (by tauto) a b)))
  → (¬noOverflow a b (·*·) → Q none)
  → mulOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (noOverflow a b (·*·) → Q (some (st, mulOp (by tauto) a b)))
  → (¬noOverflow a b (·*·) → Q none)
  → mulOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, mulOp (by tauto) a b))
  → mulOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, mulOp (by tauto) a b))
  → mulOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → mulOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the multiplication builtin.

In Noir, this corresponds to the multiplication of two values with `*`.
-/
def mul : Builtin := {
  omni := mulOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type mulOmni <;> tauto
    repeat (constructor; aesop; aesop)
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type mulOmni
    rename_i s a b _ _ _
    repeat (first | constructor | tauto | intro)
}

/-- Ensures the operation given with `intOp` when applied to `a` and `b`'s int representation doesn't underflow. -/
def noUnderflow {tp : Tp}
  (a b : tp.denote p)
  (intOp : Int → Int → Int) : Prop := match tp with
| .u _ => b ≤ a
| .i s => bitsCanRepresent s (intOp a.toInt b.toInt)
| .field => True
| .bi => True
| _ => False

inductive subOmni : Omni where
| u {p st s a b Q} :
  (noUnderflow a b (·-·) → Q (some (st, subOp (by tauto) a b)))
  → (¬noUnderflow a b (·-·) → Q none)
  → subOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (noUnderflow a b (·-·) → Q (some (st, subOp (by tauto) a b)))
  → (¬noUnderflow a b (·-·) → Q none)
  → subOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, subOp (by tauto) a b))
  → subOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, subOp (by tauto) a b))
  → subOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → subOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the subtraction builtin.

In Noir, this corresponds to the subtraction of two values with `-`.
-/
def sub : Builtin := {
  omni := subOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type subOmni <;> tauto
    repeat (constructor; aesop; aesop)
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type subOmni
    rename_i s a b _ _ _
    repeat (first | constructor | tauto | intro)
}

/-- Ensures that `b` can divide `a`, i.e., `b ≠ 0`.-/
def canDivide {tp : Tp}
  (_ b : tp.denote p) : Prop := match tp with
| .u _ => b ≠ 0
| .i _ => b ≠ 0
| .field => b ≠ 0
| .bi => b ≠ 0
| _ => False

inductive divOmni : Omni where
| u {p st s a b Q} :
  (canDivide a b → Q (some (st, divOp (by tauto) a b)))
  → (¬canDivide a b → Q none)
  → divOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (canDivide a b → Q (some (st, divOp (by tauto) a b)))
  → (¬canDivide a b → Q none)
  → divOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  (canDivide a b → Q (some (st, divOp (by tauto) a b)))
  → (¬canDivide a b → Q none)
  → divOmni p st [.field, .field] (.field) h![a, b] Q
| bi {p st a b Q} :
  (canDivide a b → Q (some (st, divOp (by tauto) a b)))
  → (¬canDivide a b → Q none)
  → divOmni p st [.bi, .bi] (.bi) h![a, b] Q
| _ {p st a b Q} : Q none → divOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the division builtin.

In Noir, this corresponds to the division of two values with `/`.
-/
def div : Builtin := {
  omni := divOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type divOmni <;> tauto
    repeat (constructor; aesop; aesop)
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type divOmni
    rename_i s a b _ _ _
    repeat (first | constructor | tauto | intro)
}

/--
Captures the behavior of the signed integer remainder operation % in Noir.
In particular, for two signed integers `a` and `b`, this returns ` a - ((a.sdiv b) * b)`
-/
def intRem {s: Nat} (a b : I s) : I s := (a - (a.sdiv b) * b)

example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = 0 := by rfl
example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-3)) = -2 := by rfl
example : intRem (BitVec.ofInt 8 (6)) (BitVec.ofInt 8 (-100)) = 6 := by rfl
example : intRem (BitVec.ofInt 8 (127)) (BitVec.ofInt 8 (-3)) = 1 := by rfl

inductive remOmni : Omni where
| u {p st s a b Q} :
  (canDivide a b → Q (some (st, a % b)))
  → (¬canDivide a b → Q none)
  → remOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (canDivide a b → Q (some (st, intRem a b)))
  → (¬canDivide a b → Q none)
  → remOmni p st [.i s, .i s] (.i s) h![a, b] Q
| _ {p st a b Q} : Q none → remOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the remainder operation builtin.

In Noir, this corresponds to the modulus of two values with `%`.
-/
def rem : Builtin := {
  omni := remOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type remOmni <;> tauto
    repeat (constructor; aesop; aesop)
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type remOmni
    rename_i s a b _ _ _
    repeat (first | constructor | tauto | intro)
}

inductive negOmni : Omni where
| i {p st s a Q} :
  Q (some (st, -a))
  → negOmni p st [.i s] (.i s) h![a] Q
| field {p st a Q} :
  Q (some (st, -a))
  → negOmni p st [.field] (.field) h![a] Q
| bi {p st a Q} :
  Q (some (st, -a))
  → negOmni p st [.bi] (.bi) h![a] Q
| _ {p st a b Q} : Q none → negOmni p st [tp, tp] tp h![a, b] Q

/--
Defines the negation builtin.

In Noir, this corresponds to the negation of a value with `-`.
-/
def neg : Builtin := {
  omni := negOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type negOmni <;> tauto
  frame := by
    unfold omni_frame
    intros p st1 st2 argTps outTp args Q omni1 hd
    cases_type negOmni
    repeat (first | constructor | tauto | intro)
}

end Lampe.Builtin
