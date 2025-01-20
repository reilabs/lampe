import Lampe.Data.Integers
import Lampe.Data.Field
import Lampe.Data.HList

namespace Lampe

/--
Represents a reference in our memory model.
A reference contains a unique natural number which identifies a value in the heap.
-/
structure Ref where
  val : Nat
deriving DecidableEq

variable (p : Prime)

/--
Represents the "kind" of a generic.
This is used for polymorphic constructions where generic parameters can be types as well as natural numbers.
-/
inductive Kind where
| nat
| type

mutual

/--
Represents a concrete Noir type.
-/
inductive CTp where
| u (size : Nat)
| i (size : Nat)
| bi -- BigInt
| bool
| unit
| str (size: U 32)
| field
| slice (element : CTp)
| array (element: CTp) (size: U 32)
| tuple (name : Option String) (fields : List CTp)
| ref (tp : CTp)
| fn (argTps : List Tp) (outTp : Tp)

/--
Represents a virtual type that can either be a concrete `CTp` or a type that is resolved during verification.
-/
inductive Tp where
| concrete : CTp → Tp
| any : Tp

end

/--
Any concrete type `CTp` can be represented by `Tp` with the `Tp.concrete` constructor.
-/
instance : Coe CTp Tp := ⟨Tp.concrete⟩

/--
The default value of a `CTp` is defined to be the unit type.
This is needed for fallible conversions from `Tp` to `CTp`.
-/
instance : Inhabited CTp := ⟨CTp.unit⟩

mutual

def tpDecEq (a b : Tp) : Decidable (a = b) := match a, b with
| .concrete a', .concrete b' => match ctpDecEq a' b' with
  | isTrue h => isTrue (by tauto)
  | isFalse h => isFalse (by simp_all)
| .any, .any => isTrue rfl
| .concrete _, .any => isFalse (by simp)
| .any, .concrete _ => isFalse (by simp)

def tpsDecEq (a b : List Tp) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _ => isFalse (by simp)
| _ :: _, [] => isFalse (by simp)
| tp₁ :: tps₁, tp₂ :: tps₂ => match tpDecEq tp₁ tp₂, tpsDecEq tps₁ tps₂ with
  | isTrue _, isTrue _ => isTrue (by subst_vars; rfl)
  | isFalse _, _ => isFalse (by simp_all)
  | _, isFalse _ => isFalse (by simp_all)

def ctpsDecEq (a b : List CTp) : Decidable (a = b) := match a, b with
| [], [] => isTrue rfl
| [], _ :: _ => isFalse (by simp)
| _ :: _, [] => isFalse (by simp)
| tp₁ :: tps₁, tp₂ :: tps₂ => match ctpDecEq tp₁ tp₂, ctpsDecEq tps₁ tps₂ with
  | isTrue _, isTrue _ => isTrue (by subst_vars; rfl)
  | isFalse _, _ => isFalse (by simp_all)
  | _, isFalse _ => isFalse (by simp_all)

def ctpDecEq (a b : CTp) : Decidable (a = b) := by
  cases a <;> cases b
  all_goals try { right; rfl }
  all_goals try { left; simp_all }
  all_goals try {
    rename_i n₁ n₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases h
    . left
      simp_all
    . right
      tauto
  }
  all_goals try {
    rename_i tp₁ tp₂
    cases (ctpDecEq tp₁ tp₂)
    . left
      simp_all
    . right
      tauto
  }
  case array.array =>
    rename_i tp₁ n₁ tp₂ n₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases (ctpDecEq tp₁ tp₂) <;> cases h
    all_goals try {left; simp_all}
    right
    subst_vars
    rfl
  case tuple.tuple =>
    rename_i n₁ tps₁ n₂ tps₂
    have h : Decidable (n₁ = n₂) := inferInstance
    cases (ctpsDecEq tps₁ tps₂) <;> cases h
    all_goals try { left; simp_all; }
    right; subst_vars; rfl
  case fn.fn =>
    rename_i args₁ out₁ args₂ out₂
    cases (tpDecEq out₁ out₂) <;> cases (tpsDecEq args₁ args₂)
    all_goals try { left; simp_all; }
    right; subst_vars; rfl

end

instance : DecidableEq CTp := ctpDecEq

instance : DecidableEq Tp := tpDecEq

@[reducible]
def Kind.denote : Kind → Type
| .nat => Nat
| .type => CTp

/--
Represents a function reference in a Noir program.
The constructors should contain all the necessary information to be able to call the function.
-/
inductive FuncRef (argTps : List Tp) (outTp : Tp) where
| lambda (r : Ref)
| decl (fnName : String) (kinds : List Kind) (generics : HList Kind.denote kinds)
| trait (selfTp : Option CTp)
  (traitName : String) (traitKinds : List Kind) (traitGenerics : HList Kind.denote traitKinds)
  (fnName : String) (fnKinds : List Kind) (fnGenerics : HList Kind.denote fnKinds)

mutual

@[reducible]
def CTp.denoteArgs : List CTp → Type
| [] => Unit
| tp :: tps => denote tp × denoteArgs tps

@[reducible]
def CTp.denote : CTp → Type
| .u n => U n
| .i n => I n
| .bi => Int
| .bool => Bool
| .unit => Unit
| .str n => List.Vector Char n.toNat
| .field => Fp p
| .slice tp => List (denote tp)
| .array tp n => List.Vector (denote tp) n.toNat
| .ref _ => Ref
| .tuple _ fields => CTp.denoteArgs fields
| .fn argTps outTp => FuncRef argTps outTp

end

@[reducible]
def Tp.denote : Tp → Type
| .concrete tp => tp.denote p
| .any => (tp : CTp) × tp.denote p

instance : CoeDep (Tp.denote p .any) ⟨tp, v⟩ (Tp.denote p (.concrete tp)) := ⟨v⟩

instance : CoeDep (Tp.denote p (.concrete tp)) (v) (Tp.denote p .any) := ⟨tp, v⟩

end Lampe
