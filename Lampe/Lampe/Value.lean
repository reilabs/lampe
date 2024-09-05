import Mathlib

import Lampe.Data.Integers

namespace Lampe

variable (P : Nat)

inductive HListI {α : Type v} (β : α → Type u) : List α → Type (max u v) where
| nil : HListI β []
| cons : ∀ {a : α} {as : List α}, β a → HListI β as → HListI β (a :: as)

@[reducible]
def HList (ts : List (Type u)) : Type u := match ts with
| [] => PUnit
| t :: ts => t × HList ts

@[reducible]
def HList' (emb : α → Type) (ts : List α) : Type := match ts with
| [] => PUnit
| t :: ts => emb t × HList' emb ts

-- @[match_pattern] def HList.nil : HList [] := PUnit.unit
-- @[match_pattern] def HList.cons {a : Type} {as : List Type} (x : a) (xs : HList as) : HList (a :: as) := (x, xs)

syntax "h![" term,* "]" : term
macro_rules
| `(h![]) => `(HListI.nil)
| `(h![$x]) => `(HListI.cons $x HList.nil)
| `(h![$x, $xs,*]) => `(HListI.cons $x h![$xs,*])

inductive ClosedType where
| u (size : Nat) : ClosedType
| bool : ClosedType
| unit : ClosedType
| field : ClosedType
| fn : List ClosedType → ClosedType → ClosedType
| slice : ClosedType → ClosedType

#print ClosedType.rec
#print ClosedType._sizeOf_1

def size' : ClosedType → Nat
| .u _ => 1
| .bool => 1
| .unit => 1
| .field => 1
| .fn [] result => 1 + size' result
| .fn (arg :: args) result => 1 + size' arg + size' (ClosedType.fn args result)
| .slice tp => 1 + size' tp

mutual

def ClosedType.denoteArgs : List ClosedType → Type
| [] => PUnit
| tp :: tps => denote tp × denoteArgs tps

def ClosedType.denote : ClosedType → Type
| .u n => U n
| .bool => Bool
| .unit => Unit
| .field => ZMod P
| .fn args result => denoteArgs args → (denote result)
| .slice tp => List (denote tp)

end

inductive PrimKind where
| nat
| type

/--
Specifically exclude
--/
inductive Kind where
| prim : PrimKind → Kind
| tyHList : List PrimKind → Kind
| tyList : PrimKind → Kind
| tyFn : List PrimKind → PrimKind → Kind

abbrev PrimKind.denote : PrimKind → Type
| .nat => Nat
| .type => ClosedType

def PrimKind.toString : PrimKind → String
| .nat => "nat"
| .type => "type"

def Kind.denote : Kind → Type
| .prim k => k.denote
| .tyList k => List k.denote
| .tyHList k => HList' PrimKind.denote k
| .tyFn args result => HListI PrimKind.denote args → result.denote


-- mutual

-- def ClosedType.denoteList : (h: List ClosedType) → HList h
-- | [] => PUnit
-- | tp :: tps => denote tp × denoteList tps

-- def ClosedType.denote : ClosedType → Type
-- | .u n => U n
-- | .bool => Bool
-- | .unit => Unit
-- | .field => ZMod P
-- | .fn args result => denoteList args → denote result
-- | .slice tp => List (denote tp)
-- -- termination_by p => p
-- -- decreasing_by simp_wf

-- end

def Kind.nat : Kind := Kind.prim PrimKind.nat
def Kind.type : Kind := Kind.prim PrimKind.type

inductive Tp' (rep : Kind → Type) : Kind → Type where
| natLit : Nat → Tp' rep .nat
| u : Nat → Tp' rep .type
| bool : Tp' rep .type
| unit : Tp' rep .type
| field : Tp' rep .type
| slice : Tp' rep (.tyFn [.type] .type)
| fn : Tp' rep (.tyList .type) → Tp' rep .type → Tp' rep .type
| nil : Tp' rep (.tyList k)
| cons : Tp' rep (.prim k) → Tp' rep (.tyList k) → Tp' rep (.tyList k)
-- | hNil : Tp' rep (.tyHList [])
-- | hCons : ∀ {x xs}, Tp' rep (.prim x) → Tp' rep (.tyHList xs) → Tp' rep (.tyHList (x :: xs))
| pi : ((HListI (fun i => rep (.prim i)) x) → Tp' rep (.prim y)) → Tp' rep (.tyFn x y)
| var : rep (.prim k) → Tp' rep (.prim k)
| app : Tp' rep (.tyFn a b) → HListI (fun i => Tp' rep (.prim i)) a → Tp' rep (.prim b)

def Tp (kind : Kind) := ∀ rep, Tp' rep kind

set_option pp.universes true
#check Tp
#check Tp'

def Tp.bool : Tp .type := fun _ => Tp'.bool
def Tp.unit : Tp .type := fun _ => Tp'.unit
def Tp.field : Tp .type := fun _ => Tp'.field
def Tp.u (n : Nat) : Tp .type := fun _ => Tp'.u n

mutual

def Tp'.denoteArgs : HListI (fun i => Tp' Kind.denote (.prim i)) args → HListI PrimKind.denote args :=
match args with
| .nil => fun _ => HListI.nil
| .cons a as => fun (HListI.cons a as) => HListI.cons (denote a) (denoteArgs as)

-- @[reducible]
def Tp'.denote : Tp' Kind.denote kind → Kind.denote kind
| .nil => []
| .cons x xs => denote x :: denote xs
-- | .hNil => h![]
-- | .hCons x xs => HList.cons (denote x) (denote xs)
| .natLit n => n
| .pi f => fun x => denote (f x)
| .var x => x
| .app f x => denote f (denoteArgs x)
| .u n => .u n
| .bool => .bool
| .unit => .unit
| .field => .field
| .slice => fun x =>
  match x with
  | .cons x _ => .slice x
| .fn args result => .fn (denote args) (denote result)

end

@[reducible]
def Tp'.denoteTp : Tp' Kind.denote .type → Type := (fun x => x.denote.denote P)


#check Tp'.pi

def polymorphic_id : Tp (.tyFn [.type] .type) := fun _ =>
  Tp'.pi fun h![x] => Tp'.fn (Tp'.cons (Tp'.var x) Tp'.nil) (Tp'.var x)

def pol_instd : Tp .type := fun r => Tp'.app (rep := r) (polymorphic_id r) (Tp'.hCons Tp'.field Tp'.hNil)

def makeArgs (s : Nat) (a : List PrimKind) : HList (fun _ => String) a := match a with
| [] => h![]
| _ :: as => HList.cons ("x" ++ toString s) (makeArgs (s + 1) as)

def pretty (s : Nat) : Tp' (fun _ => String) k → String
| .nil => ""
| .cons x xs =>
  let rest := pretty s xs
  pretty s x ++ if (rest == "") then "" else ", " ++ rest
| .hNil => "h![]"
| .hCons x xs => "h![" ++ pretty s x ++ ", " ++ pretty s xs ++ "]"
| .natLit n => toString n
| @Tp'.pi _ tps _ f =>
  let args := String.join $ List.intersperse "," (tps.mapIdx (fun i x => ("(x" ++ toString (s + i) ++ " : " ++ x.toString ++")")))
  "λ " ++ "<" ++ args ++ "> => " ++ pretty (s + tps.length) (f $ makeArgs s tps)
| .fn args result => "fn(" ++ pretty s args ++ ") -> " ++ pretty s result
| .var x => x
| _ => "not implemented"

#eval pretty 0 (polymorphic_id _)
#eval pretty 0 (pol_instd _)

#reduce ((pol_instd _).denote)

#print polymorphic_id

end Lampe
