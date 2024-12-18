import Lampe.Builtin.Basic
namespace Lampe.Builtin

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
Captures the behavior of the signed integer remainder operation % in Noir.
In particular, for two signed integers `a` and `b`, this returns ` a - ((a.sdiv b) * b)`
-/
def intRem {s: Nat} (a b : I s) : I s := (a - (a.sdiv b) * b)

example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = 0 := by rfl
example : intRem (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-3)) = -2 := by rfl
example : intRem (BitVec.ofInt 8 (6)) (BitVec.ofInt 8 (-100)) = 6 := by rfl
example : intRem (BitVec.ofInt 8 (127)) (BitVec.ofInt 8 (-3)) = 1 := by rfl

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

class AddTp (tp : Tp) where
  validate {p} : (a b : tp.denote p) → Prop
  compute {p} : (a b : tp.denote p) → (validate a b) → tp.denote p

class SubTp (tp : Tp) where
  validate {p} : (a b : tp.denote p) → Prop
  compute {p} : (a b : tp.denote p) → (validate a b) → tp.denote p

class MulTp (tp : Tp) where
  validate {p} : (a b : tp.denote p) → Prop
  compute {p} : (a b : tp.denote p) → (validate a b) → tp.denote p

class DivTp (tp : Tp) where
  validate {p} : (a b : tp.denote p) → Prop
  compute {p} : (a b : tp.denote p) → (validate a b) → tp.denote p

class NegTp (tp : Tp) where
  validate {p} : (a : tp.denote p) → Prop
  compute {p} : (a : tp.denote p) → (validate a) → tp.denote p

class RemTp (tp : Tp) where
  validate {p} : (a b : tp.denote p) → Prop
  compute {p} : (a b : tp.denote p) → (validate a b) → tp.denote p

-- Field arithmetic semantics

@[simp]
instance : AddTp .field where
  validate := fun _ _ => True
  compute := fun a b _ => a + b

@[simp]
instance : SubTp .field where
  validate := fun _ _ => True
  compute := fun a b _ => a - b

@[simp]
instance : MulTp .field where
  validate := fun _ _ => True
  compute := fun a b _ => a * b

@[simp]
instance : DivTp .field where
  validate := fun _ b => b ≠ 0
  compute := fun a b _ => a / b

@[simp]
instance : NegTp .field where
  validate := fun _ => True
  compute := fun a _ => -a

-- Unsigned integer arithmetic semantics

@[simp]
instance : AddTp (.u s) where
  validate := fun a b => (a.toInt + b.toInt) < 2^s
  compute := fun a b _ => a + b

@[simp]
instance : SubTp (.u s) where
  validate := fun a b => b ≤ a
  compute := fun a b _ => a - b

@[simp]
instance : MulTp (.u s) where
  validate := fun a b => (a.toInt * b.toInt) < 2^s
  compute := fun a b _ => a * b

@[simp]
instance : DivTp (.u s) where
  validate := fun _ b => b ≠ 0
  compute := fun a b _ => a.udiv b

@[simp]
instance : RemTp (.u s) where
  validate := fun _ b => b ≠ 0
  compute := fun a b _ => a % b

-- Signed integer arithmetic semantics

@[simp]
instance : AddTp (.i s) where
  validate := fun a b => bitsCanRepresent s (a.toInt + b.toInt)
  compute := fun a b _ => a + b

@[simp]
instance : SubTp (.i s) where
  validate := fun a b => bitsCanRepresent s (a.toInt - b.toInt)
  compute := fun a b _ => a - b

@[simp]
instance : MulTp (.i s) where
  validate := fun a b => bitsCanRepresent s (a.toInt * b.toInt)
  compute := fun a b _ => a * b

@[simp]
instance : DivTp (.i s) where
  validate := fun _ b => b ≠ 0
  compute := fun a b _ => a / b

@[simp]
instance : NegTp (.i s) where
  validate := fun a => bitsCanRepresent s (-a.toInt)
  compute := fun a _ => -a

@[simp]
instance : RemTp (.i s) where
  validate := fun _ b => b ≠ 0
  compute := fun a b _ => intRem a b

inductive addOmni : Omni where
| ok {tp p st a b Q} [AddTp tp]:
  (h : AddTp.validate a b) →
  Q (some (st, AddTp.compute a b h)) →
  addOmni p st [tp, tp] tp h![a, b] Q
| err {tp p st a b Q} [AddTp tp]:
  ¬AddTp.validate a b →
  Q none →
  addOmni p st [tp, tp] tp h![a, b] Q

def add : Builtin := {
  omni := addOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type addOmni
    · tauto
    · apply addOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type addOmni
    · apply addOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply addOmni.err <;> tauto
}

inductive subOmni : Omni where
| ok {tp p st a b Q} [SubTp tp]:
  (h : SubTp.validate a b) →
  Q (some (st, SubTp.compute a b h)) →
  subOmni p st [tp, tp] tp h![a, b] Q
| err {tp p st a b Q} [SubTp tp]:
  ¬SubTp.validate a b →
  Q none →
  subOmni p st [tp, tp] tp h![a, b] Q

def sub : Builtin := {
  omni := subOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type subOmni
    · tauto
    · apply subOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type subOmni
    · apply subOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply subOmni.err <;> tauto
}

inductive mulOmni : Omni where
| ok {tp p st a b Q} [MulTp tp]:
  (h : MulTp.validate a b) →
  Q (some (st, MulTp.compute a b h)) →
  mulOmni p st [tp, tp] tp h![a, b] Q
| err {tp p st a b Q} [MulTp tp]:
  ¬MulTp.validate a b →
  Q none →
  mulOmni p st [tp, tp] tp h![a, b] Q

def mul : Builtin := {
  omni := mulOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type mulOmni
    · tauto
    · apply mulOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type mulOmni
    · apply mulOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply mulOmni.err <;> tauto
}

inductive divOmni : Omni where
| ok {tp p st a b Q} [DivTp tp]:
  (h : DivTp.validate a b) →
  Q (some (st, DivTp.compute a b h)) →
  divOmni p st [tp, tp] tp h![a, b] Q
| err {tp p st a b Q} [DivTp tp]:
  ¬DivTp.validate a b →
  Q none →
  divOmni p st [tp, tp] tp h![a, b] Q

def div : Builtin := {
  omni := divOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type divOmni
    · tauto
    · apply divOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type divOmni
    · apply divOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply divOmni.err <;> tauto
}

inductive remOmni : Omni where
| ok {tp p st a b Q} [RemTp tp]:
  (h : RemTp.validate a b) →
  Q (some (st, RemTp.compute a b h)) →
  remOmni p st [tp, tp] tp h![a, b] Q
| err {tp p st a b Q} [RemTp tp]:
  ¬RemTp.validate a b →
  Q none →
  remOmni p st [tp, tp] tp h![a, b] Q

def rem : Builtin := {
  omni := remOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type remOmni
    · tauto
    · apply remOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type remOmni
    · apply remOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply remOmni.err <;> tauto
}

inductive negOmni : Omni where
| ok {tp p st a Q} [NegTp tp]:
  (h : NegTp.validate a) →
  Q (some (st, NegTp.compute a h)) →
  negOmni p st [tp] tp h![a] Q
| err {tp p st a Q} [NegTp tp]:
  ¬NegTp.validate a →
  Q none →
  negOmni p st [tp] tp h![a] Q

def neg : Builtin := {
  omni := negOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type negOmni
    · tauto
    · apply negOmni.err <;> tauto
  frame := by
    unfold omni_frame
    intros
    cases_type negOmni
    · apply negOmni.ok <;> tauto
      simp only [SLP.star]
      tauto
    · apply negOmni.err <;> tauto
}

end Lampe.Builtin
