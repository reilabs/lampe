import Lampe.Builtin.Basic
namespace Lampe.Builtin
open Lampe.Builtin

inductive strAsBytesOmni : Omni where
| ok {P st n s Q} :
  (h: s.toList.length = n.toNat)
    → Q (some (st, .map (fun u => u.toNat) ⟨s.toList, (h)⟩))
    → strAsBytesOmni P st [.str n] (.array (.u 8) n) h![s] Q
| err {P st n s Q} :
  (s.toList.length ≠ n.toNat)
    → Q none
    → strAsBytesOmni P st [.str n] (.array (.u 8) n) h![s] Q

/--
Defines the conversion of strings of length `n` to a byte array of length `n`.
Accordingly, we assume that the string has UTF-8 byte length of `n`.

In Noir, this corresponds to `fn as_bytes(self) -> [u8; n]` implemented for `str<n>`.
-/
def strAsBytes : Builtin := {
  omni := strAsBytesOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type strAsBytesOmni
    . constructor <;> simp_all
    . apply strAsBytesOmni.err <;> simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type strAsBytesOmni
    . constructor
      . constructor <;> tauto
    . apply strAsBytesOmni.err <;> assumption
}

end Lampe.Builtin
