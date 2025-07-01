import Lampe.Ast
import Lampe.Builtin.Arith
import Lampe.Builtin.Array
import Lampe.Builtin.BigInt
import Lampe.Builtin.Bit
import Lampe.Builtin.Cmp
import Lampe.Builtin.Field
import Lampe.Builtin.Lens
import Lampe.Builtin.Memory
import Lampe.Builtin.Slice
import Lampe.Builtin.Str
import Lampe.Builtin.Struct

namespace Lampe

/-- A utility function for creating a reference expression. -/
@[reducible]
def Expr.ref (val : rep tp) : Lampe.Expr rep tp.ref :=
  Lampe.Expr.callBuiltin _ tp.ref .ref h![val]

/-- A utility function for creating a reference read expression. -/
@[reducible]
def Expr.readRef (ref : rep tp.ref) : Lampe.Expr rep tp :=
  Lampe.Expr.callBuiltin _ tp .readRef h![ref]

/-- A utility function for creating a reference write expression. -/
@[reducible]
def Expr.writeRef (ref : rep tp.ref) (val : rep tp) : Lampe.Expr rep .unit :=
  Lampe.Expr.callBuiltin _ .unit .writeRef h![ref, val]

/-- A utility function for creating a slice expression. -/
@[reducible]
def Expr.mkSlice (n : Nat) (vals : HList rep (List.replicate n tp)) 
  : Lampe.Expr rep (.slice tp) :=
  Lampe.Expr.callBuiltin _ (.slice tp) .mkSlice vals

/-- A utility function for creating an array expression. -/
@[reducible]
def Expr.mkArray (n : Lampe.U 32) (vals : HList rep (List.replicate n.toNat tp)) 
  : Lampe.Expr rep (.array tp n) :=
  Lampe.Expr.callBuiltin _ (.array tp n) .mkArray vals

/-- A utility function for creating a replicated slice expression. -/
@[reducible]
def Expr.mkRepSlice (n : Nat) (val : rep tp) : Lampe.Expr rep (.slice tp) :=
  Lampe.Expr.callBuiltin _ (.slice tp) .mkSlice (HList.replicate val n)

/-- A utility function for creating a replicated array expression. -/
@[reducible]
def Expr.mkRepArray (n : Lampe.U 32) (val : rep tp) : Lampe.Expr rep (.array tp n) :=
  Lampe.Expr.callBuiltin _ (.array tp n) .mkArray (HList.replicate val n.toNat)

/-- A utility function for creating a tuple expression. -/
@[reducible]
def Expr.mkTuple (name : Option String) (args : HList rep tps) 
  : Lampe.Expr rep (.tuple name tps) :=
  Lampe.Expr.callBuiltin tps (.tuple name tps) .mkTuple args

/-- A utility function for creating a lens modification expression. -/
@[reducible]
def Expr.modifyLens (r : rep $ .ref tp₁) (v : rep tp₂) (lens : Lampe.Lens rep tp₁ tp₂)
  : Lampe.Expr rep .unit :=
  Lampe.Expr.callBuiltin [.ref tp₁, tp₂] .unit (.modifyLens lens) h![r, v]

/-- A utility function for creating a lens read expression. -/
@[reducible]
def Expr.getLens (v : rep tp₁) (lens : Lampe.Lens rep tp₁ tp₂) 
  : Lampe.Expr rep tp₂ :=
  Lampe.Expr.callBuiltin _ tp₂ (.getLens lens) h![v]

/-- A utility function for creating a member access. -/
@[reducible]
def Expr.getMember (v : rep (Tp.tuple name tps)) (member : Lampe.Builtin.Member tp tps)
  : Lampe.Expr rep tp := 
  Expr.callBuiltin _ tp (Lampe.Builtin.getMember member) h![v]
