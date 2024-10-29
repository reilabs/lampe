import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/-- a == b -/
def refEq {tp : Tp}: Builtin := newBuiltin
  [(.ref tp), (.ref tp)] .bool
  (fun _ => True)
  sorry

/-- a == b -/
def unitEq : Builtin := newBuiltin
  [(.unit), (.unit)] .bool
  (fun _ => True)
  sorry

/-- a == b -/
def bEq : Builtin := newBuiltin
  [(.bool), (.bool)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a == b -/
def uEq {s : Nat}: Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a == b -/
def iEq {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a == b)

/-- a < b -/
def uLt {s : Nat}: Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a < b)

/-- a < b -/
def iLt {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a < b)

/-- a > b -/
def uGt {s : Nat}: Builtin := newBuiltin
  [(.u s), (.u s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a > b)

/-- a > b -/
def iGt {s : Nat}: Builtin := newBuiltin
  [(.i s), (.i s)] .bool
  (fun _ => True)
  (fun h![a, b] _ => a > b)

end Lampe.Builtin
