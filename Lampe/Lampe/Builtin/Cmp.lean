import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/-- () = () -/
def unitEq : Builtin := newBuiltin
  [(.unit), (.unit)] .bool
  (fun _ => True)
  (fun _ _ => True)

/-- a == b -/
def bEq : Builtin := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a == b -/
def uEq {s : Nat} : Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a == b -/
def iEq {s : Nat} : Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a == b -/
def fEq : Builtin := newBuiltin
  [(.field), (.field)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a < b -/
def uLt {s : Nat} : Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a < b)

/-- a < b -/
def iLt {s : Nat} : Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a < b)

/-- a > b -/
def uGt {s : Nat} : Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a > b)

/-- a > b -/
def iGt {s : Nat} : Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a > b)

-- @[reducible]
-- def Ord := Tp.struct [Tp.field]
-- def Ord.Less : Tp.denote p Ord := (0, ())
-- def Ord.Equal : Tp.denote p Ord := (1, ())
-- def Ord.Greater : Tp.denote p Ord := (2, ())

-- class NoirCmp (α : Type) where
--   cmp : {p : Prime} -> α -> α -> (Tp.denote p Ord)

-- instance {s} : NoirCmp (Tp.denote p (.i s)) where
--   cmp := fun a b =>
--     if a < b then
--       Ord.Less
--     else if a > b then
--       Ord.Greater
--     else
--       Ord.Equal

-- instance {s} : NoirCmp (Tp.denote p (.u s)) where
--   cmp := fun a b =>
--     if a < b then
--       Ord.Less
--     else if a > b then
--       Ord.Greater
--     else
--       Ord.Equal

-- instance : NoirCmp (Tp.denote p .unit) where
--   cmp := fun _ _ => Ord.Equal

-- instance : NoirCmp (Tp.denote p .bool) where
--   cmp := fun a b => match a, b with
--   | true, true => Ord.Equal
--   | true, false => Ord.Greater
--   | false, true => Ord.Less
--   | false, false => Ord.Equal
