import «std-1.0.0-beta.12».Extracted
import Lampe

namespace Lampe.Stdlib.EmbeddedCurveOps

open «std-1.0.0-beta.12»

namespace Point

/-- A useful shorthand for the type of the embedded curve point. -/
@[reducible]
def type := «std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurvePoint».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve point. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[reducible]
def mk {p} (x y : Fp p) (isInfinite : Bool) : Point.denote p := (x, y, isInfinite, ())

def x {p} (self : Point.denote p) : Fp p := self.1
def y {p} (self : Point.denote p) : Fp p := self.2.1
def isInfinite {p} (self : Point.denote p) : Bool := self.2.2.1

end Point

namespace Scalar

/-- A useful shorthand for the type of the embedded curve scalar. -/
@[reducible]
def type := «std-1.0.0-beta.12::embedded_curve_ops::EmbeddedCurveScalar».tp h![]

/-- A useful shorthand for declaring the type of values of the embedded curve scalar. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

@[reducible]
def mk {p} (lo hi : Fp p) : Scalar.denote p := (lo, hi, ())

def lo {p} (self : Scalar.denote p) : Fp p := self.1
def hi {p} (self : Scalar.denote p) : Fp p := self.2.1

end Scalar

