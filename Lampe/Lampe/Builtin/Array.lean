import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

inductive arrayLenOmni : Omni where
| mk {P st Q n a} :
  Q (some (st, n)) → arrayLenOmni P st [.array tp n] (.u 32) h![a] Q

/--
Defines the function that evaluates to an array's length `n`.
This builtin evaluates to an `U 32`. Hence, we assume that `n < 2^32`.

In Noir, this corresponds to `fn len(self) -> u32` implemented for `[_; n]`.
-/
def arrayLen : Builtin := {
  omni := arrayLenOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type arrayLenOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type arrayLenOmni
    constructor
    constructor <;> tauto
}

inductive arrayAsSliceOmni : Omni where
| mk {P st Q n a} :
  Q (some (st, a.toList)) → arrayAsSliceOmni P st [.array tp n] (.slice tp) h![a] Q

/--
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def arrayAsSlice : Builtin := {
  omni := arrayAsSliceOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type arrayAsSliceOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type arrayAsSliceOmni
    constructor
    constructor <;> tauto
}

end Lampe.Builtin
