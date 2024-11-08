import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Captures the behavior of the signed integer remainder operation % in Noir.
In particular, for two signed integers `a` and `b`, this returns ` a - ((a.sdiv b) * b)`
-/
def intRem {s: Nat} (a b : I s) : I s := (a - (a.sdiv b) * b)

example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = 0 := by rfl
example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-3)) = -2 := by rfl
example : intRem (BitVec.ofInt 8 (6)) (BitVec.ofInt 8 (-100)) = 6 := by rfl
example : intRem (BitVec.ofInt 8 (127)) (BitVec.ofInt 8 (-3)) = 1 := by rfl

inductive addOmni : Omni where
| u {p st s a b Q} :
  ((a.toInt + b.toInt) < 2^s → Q (some (st, a + b)))
  → ((a.toInt + b.toInt) >= 2^s → Q none)
  → addOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (bitsCanRepresent s (a.toInt + b.toInt) → Q (some (st, a + b)))
  → (¬(bitsCanRepresent s (a.toInt + b.toInt)) → Q none)
  → addOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, a + b))
  → addOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, a + b))
  → addOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → addOmni p st [tp, tp] tp h![a, b] Q

def add : Builtin := {
  omni := addOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type addOmni <;> tauto
    rename _ + _ < 2^_ → _ => hok
    rename _ + _ ≥ 2^_ → _ => herr
    rename_i hm
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
  ((a.toInt * b.toInt) < 2^s → Q (some (st, a * b)))
  → ((a.toInt * b.toInt) >= 2^s → Q none)
  → mulOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (bitsCanRepresent s (a.toInt * b.toInt) → Q (some (st, a * b)))
  → (¬(bitsCanRepresent s (a.toInt * b.toInt)) → Q none)
  → mulOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, a * b))
  → mulOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, a * b))
  → mulOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → mulOmni p st [tp, tp] tp h![a, b] Q

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

inductive subOmni : Omni where
| u {p st s a b Q} :
  (b ≤ a → Q (some (st, a - b)))
  → (b > a → Q none)
  → subOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (bitsCanRepresent s (a.toInt - b.toInt) → Q (some (st, a - b)))
  → (¬(bitsCanRepresent s (a.toInt - b.toInt)) → Q none)
  → subOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  Q (some (st, a - b))
  → subOmni p st [.field, .field] .field h![a, b] Q
| bi {p st a b Q} :
  Q (some (st, a - b))
  → subOmni p st [.bi, .bi] .bi h![a, b] Q
| _ {p st a b Q} : Q none → subOmni p st [tp, tp] tp h![a, b] Q

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

inductive divOmni : Omni where
| u {p st s a b Q} :
  (b ≠ 0 → Q (some (st, a.udiv b)))
  → (b = 0 → Q none)
  → divOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (b ≠ 0 → Q (some (st, a.sdiv b)))
  → (b = 0 → Q none)
  → divOmni p st [.i s, .i s] (.i s) h![a, b] Q
| field {p st a b Q} :
  (b ≠ 0 → Q (some (st, a / b)))
  → (b = 0 → Q none)
  → divOmni p st [.field, .field] (.field) h![a, b] Q
| bi {p st a b Q} :
  (b ≠ 0 → Q (some (st, a / b)))
  → (b = 0 → Q none)
  → divOmni p st [.bi, .bi] (.bi) h![a, b] Q
| _ {p st a b Q} : Q none → divOmni p st [tp, tp] tp h![a, b] Q

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

inductive remOmni : Omni where
| u {p st s a b Q} :
  (b ≠ 0 → Q (some (st, a % b)))
  → (b = 0 → Q none)
  → remOmni p st [.u s, .u s] (.u s) h![a, b] Q
| i {p st s a b Q} :
  (b ≠ 0 → Q (some (st, intRem a b)))
  → (b = 0 → Q none)
  → remOmni p st [.i s, .i s] (.i s) h![a, b] Q
| _ {p st a b Q} : Q none → remOmni p st [tp, tp] tp h![a, b] Q

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


/--
Defines the addition of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a + b) < 2^s`, then the builtin evaluates to `(a + b) : U s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for uints `a`, `b` of bit size `s`.
-/
def uAdd := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toInt + b.toInt) < 2^s,
    fun _ => a + b⟩)

/--
Defines the multiplication of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a * b) < 2^s`, then the builtin evaluates to `(a * b) : U s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for uints `a`, `b` of bit size `s`.
-/
def uMul := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun s h![a, b] => ⟨(a.toInt * b.toInt) < 2^s,
    fun _ => a * b⟩)

/--
Defines the subtraction of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `(a - b) ≥ 0`, then the builtin evaluates to `(a - b) : U s`
- Else (integer underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for uints `a`, `b` of bit size `s`.
-/
def uSub := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≤ a,
    fun _ => a - b⟩)

/--
Defines the division of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a / b) : U s`
- Else (divide by zero), an exception is thrown.
- If `a / b` is not an integer, then the result is truncated.

In Noir, this builtin corresponds to `a / b` for uints `a`, `b` of bit size `s`.
-/
def uDiv := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.udiv b⟩)

/--
Defines the modulus of two `s`-bit uints: `(a b : U s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a % b) : U s`
- Else (mod by zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for uints `a`, `b` of bit size `s`.
-/
def uRem := newGenericPureBuiltin
  (fun s => ⟨[(.u s), (.u s)], (.u s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a % b⟩)

/--
Defines the addition of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a + b) < 2^(s-1)`, then the builtin evaluates to `(a + b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a + b` for signed ints `a`, `b` of bit size `s`.
-/
def iAdd := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt + b.toInt),
    fun _ => a + b⟩)

/--
Defines the subtraction of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a - b) < 2^(s-1)`, then the builtin evaluates to `(a - b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a - b` for signed ints `a`, `b` of bit size `s`.
-/
def iSub := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt - b.toInt),
    fun _ => a - b⟩)

/--
Defines the multiplication of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `-2^(s-1) ≤ (a * b) < 2^(s-1)`, then the builtin evaluates to `(a * b) : I s`
- Else (integer overflow/underflow), an exception is thrown.

In Noir, this builtin corresponds to `a * b` for signed ints `a`, `b` of bit size `s`.
-/
def iMul := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun s h![a, b] => ⟨bitsCanRepresent s (a.toInt * b.toInt),
    fun _ => a * b⟩)

/--
Defines the division of two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(a.sdiv b) : I s`
- Else (division-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a / b` for signed ints `a`, `b` of bit size `s`.
-/
def iDiv := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => a.sdiv b⟩)

/--
Defines the integer remainder operation between two `s`-bit ints: `(a b: I s)`.
We make the following assumptions:
- If `b ≠ 0`, then the builtin evaluates to `(intRem a b) : I s`
- Else (mod-by-zero), an exception is thrown.

In Noir, this builtin corresponds to `a % b` for signed ints `a`, `b` of bit size `s`.
-/
def iRem := newGenericPureBuiltin
  (fun s => ⟨[(.i s), (.i s)], (.i s)⟩)
  (fun _ h![a, b] => ⟨b ≠ 0,
    fun _ => intRem a b⟩)

/--
Defines the negation of a `s`-bit int: `a: I s`.
We make the following assumptions:
- If `-2^(s-1) ≤ -a < 2^(s-1)`, then the builtin evaluates to `-a : I s`
- Else (integer overflow), an exception is thrown.

In Noir, this builtin corresponds to `-a` for a signed integer `a` of bit size `s`.
-/
def iNeg := newGenericPureBuiltin
  (fun s => ⟨[(.i s)], (.i s)⟩)
  (fun s h![a] => ⟨bitsCanRepresent s (-a.toInt),
    fun _ => -a⟩)

/--
Defines the addition of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a + b) : Fp p`.

In Noir, this builtin corresponds to `a + b` for field elements `a`, `b`.
-/
def fAdd := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a + b⟩)

/--
Defines the multiplication of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a * b) : Fp p`.

In Noir, this builtin corresponds to `a * b` for field elements `a`, `b`.
-/
def fMul := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a * b⟩)

/--
Defines the subtraction of two field elements `(a b: Fp p)` in `ZMod p`.
This is assumed to evaluate to `(a - b) : Fp p`.

In Noir, this builtin corresponds to `a - b` for field elements `a`, `b`.
-/
def fSub := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨True,
    fun _ => a - b⟩)

/--
Defines the division of two field elements `(a b: Fp p)` in `ZMod p`.
We assume the following:
- If `b ≠ 0`, it evaluates to `(a / b) : Fp p`.
- Else, an exception is thrown.

In Noir, this builtin corresponds to `a / b` for field elements `a`, `b`.
-/
def fDiv := newPureBuiltin
  ⟨[(.field), (.field)], .field⟩
  (fun h![a, b] => ⟨b ≠ 0,
    fun _ => a / b⟩)

/--
Defines the additive inverse of a field element `a: Fp p` in `ZMod p`.
This is assumed to evaluate to `-a : Fp p`.

In Noir, this builtin corresponds to `-a` for a field element `a`.
-/
def fNeg := newPureBuiltin
  ⟨[(.field)], .field⟩
  (fun h![a] => ⟨True,
    fun _ => -a⟩)

end Lampe.Builtin
