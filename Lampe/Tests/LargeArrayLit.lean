/-
Regression test for GitHub issue #270: stack overflow on large array literals.

Large array/vector literals cause deeply nested HList and Expr.letIn chains during elaboration.
The fix is to increase Lean's thread stack size via `--tstack=65536` in the lakefile.

This test uses a 64-element array literal — v4.22's new compiler makes elaboration of larger
arrays prohibitively slow for CI, so this stays as a smoke check for the stack-size machinery.
-/
import Lampe

open Lampe

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
noir_def large_array_lit<>() -> Array<Field, 64: u32> := {
  (#_mkArray returning Array<Field, 64: u32>)(
    1: Field, 2: Field, 3: Field, 4: Field, 5: Field, 6: Field, 7: Field, 8: Field,
    9: Field, 10: Field, 11: Field, 12: Field, 13: Field, 14: Field, 15: Field, 16: Field,
    17: Field, 18: Field, 19: Field, 20: Field, 21: Field, 22: Field, 23: Field, 24: Field,
    25: Field, 26: Field, 27: Field, 28: Field, 29: Field, 30: Field, 31: Field, 32: Field,
    33: Field, 34: Field, 35: Field, 36: Field, 37: Field, 38: Field, 39: Field, 40: Field,
    41: Field, 42: Field, 43: Field, 44: Field, 45: Field, 46: Field, 47: Field, 48: Field,
    49: Field, 50: Field, 51: Field, 52: Field, 53: Field, 54: Field, 55: Field, 56: Field,
    57: Field, 58: Field, 59: Field, 60: Field, 61: Field, 62: Field, 63: Field, 64: Field
  )
}
