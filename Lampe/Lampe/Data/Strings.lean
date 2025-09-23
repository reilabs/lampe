import Mathlib.Data.Vector.Defs
import Lampe.Data.HList

namespace Lampe

/-- A byte in our model of Noir. -/
abbrev NoirByte := BitVec 8

/--
A Lean-level value representation of a Noir string.

Strings in Noir are simply arrays of bytes, with no interpretation of those bytes imposed by the
string itself. The length `n` is _always_ intended to be equal to the number of bytes contained
within the string, and is explicitly _not_ equal to some arbitrary notion of "characters",
"graphemes" or "grapheme clusters" as is seen in some languages.

Note that this does create an impedance mismatch with Lean strings, which interpret every `Char` as
a unicode code-point. To that end, we provide restricted conversions from noir strings back into
Lean strings as they are not useful for theorems.
-/
abbrev NoirStr (n : ℕ) := List.Vector NoirByte n

namespace NoirStr

/-- Creates a fixed length Noir string from the provided bytes. -/
@[reducible]
def mk {n : ℕ} (bytes : List.Vector UInt8 n) : NoirStr n :=
  bytes.map (·.toBitVec)

/-- Gets the length of the noir string in bytes. -/
@[reducible]
def length {n : ℕ} (_ : NoirStr n) : ℕ := n

/--
Converts the provided Lean String into a noir string, interpreting it as a series of UTF-8 encoded
bytes.
-/
@[reducible]
def of (str : String) : NoirStr (str.utf8ByteSize) :=
  let bytes := str.toUTF8.data.toList
  NoirStr.mk ⟨bytes, by
    rw [←String.size_toUTF8, Array.length_toList]
    rfl
  ⟩

/--
Converts the provided Noir string into a standard Lean string, interpreting the byte sequence as
UTF-8 encoded text.
-/
def toString {n : ℕ} (ns : NoirStr n) : String :=
  let bytes := ⟨ns.map UInt8.ofBitVec |>.toList.toArray⟩
  String.fromUTF8! bytes

end NoirStr

instance {n : ℕ} : CoeOut (NoirStr n) String where
  coe := NoirStr.toString
attribute [coe] NoirStr.toString
