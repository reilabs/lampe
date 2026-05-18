import Lampe.Builtin.Basic
import Lampe.Crypto.EmbeddedCurve
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

def embeddedCurveAddPoint1 {p : Prime}
    (args : HList (Tp.denote p)
      [Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool]) :
    Tp.denote p Lampe.Crypto.EmbeddedCurve.pointTp :=
  match args with
  | h![point1, _, _] => point1

def embeddedCurveAddPoint2 {p : Prime}
    (args : HList (Tp.denote p)
      [Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool]) :
    Tp.denote p Lampe.Crypto.EmbeddedCurve.pointTp :=
  match args with
  | h![_, point2, _] => point2

def embeddedCurveAddDesc {p : Prime}
    (_ : Unit)
    (args : HList (Tp.denote p)
      [Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool])
    : Tp.denote p (.array Lampe.Crypto.EmbeddedCurve.pointTp 1) :=
  ⟨[Lampe.Crypto.EmbeddedCurve.add
    (embeddedCurveAddPoint1 args)
    (embeddedCurveAddPoint2 args)], by simp⟩

/--
Noir's `embedded_curve_add` foreign builtin. The cryptographic addition
is modeled by `Lampe.Crypto.EmbeddedCurve.add` (total tuple-level
extension of Mathlib's `WeierstrassCurve.Affine.Point.add` for
`y² = x³ - 17`).
-/
def embeddedCurveAdd := newGenericTotalPureBuiltin
  (fun (_ : Unit) =>
    ⟨[Lampe.Crypto.EmbeddedCurve.pointTp, Lampe.Crypto.EmbeddedCurve.pointTp, .bool],
      .array Lampe.Crypto.EmbeddedCurve.pointTp 1⟩)
  embeddedCurveAddDesc

def multiScalarMulPoints {p : Prime} {n : U 32}
    (args : HList (Tp.denote p)
      [.array Lampe.Crypto.EmbeddedCurve.pointTp n, .array Lampe.Crypto.EmbeddedCurve.scalarTp n,
        .bool]) :
    Tp.denote p (.array Lampe.Crypto.EmbeddedCurve.pointTp n) :=
  match args with
  | h![points, _, _] => points

def multiScalarMulScalars {p : Prime} {n : U 32}
    (args : HList (Tp.denote p)
      [.array Lampe.Crypto.EmbeddedCurve.pointTp n, .array Lampe.Crypto.EmbeddedCurve.scalarTp n,
        .bool]) :
    Tp.denote p (.array Lampe.Crypto.EmbeddedCurve.scalarTp n) :=
  match args with
  | h![_, scalars, _] => scalars

def multiScalarMulDesc {p : Prime}
    (n : U 32)
    (args : HList (Tp.denote p)
      [.array Lampe.Crypto.EmbeddedCurve.pointTp n, .array Lampe.Crypto.EmbeddedCurve.scalarTp n,
        .bool])
    : Tp.denote p (.array Lampe.Crypto.EmbeddedCurve.pointTp 1) :=
  ⟨[Lampe.Crypto.EmbeddedCurve.multiScalarMul n
    (multiScalarMulPoints args)
    (multiScalarMulScalars args)], by simp⟩

/--
Noir's `multi_scalar_mul_array_return` foreign builtin (the
single-element-array shape underlying `multi_scalar_mul`). Modeled by
`Lampe.Crypto.EmbeddedCurve.multiScalarMul`.
-/
def multiScalarMul := newGenericTotalPureBuiltin
  (fun n =>
    ⟨[.array Lampe.Crypto.EmbeddedCurve.pointTp n, .array Lampe.Crypto.EmbeddedCurve.scalarTp n,
      .bool],
      .array Lampe.Crypto.EmbeddedCurve.pointTp 1⟩)
  multiScalarMulDesc

end Lampe.Builtin
