import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

/--
Defines the conversion of strings of length `n` to a byte array of length `n`.
Accordingly, we assume that the string has UTF-8 byte length of `n`.

In Noir, this corresponds to `fn as_bytes(self) -> [u8; n]` implemented for `str<n>`.
-/
def strAsBytes {n : U 32} : Builtin := newBuiltin
  [.str] (.array (.u 8) n)
  (fun h![s] => s.utf8ByteSize == n)
  (fun h![s] _ => Array.mk (.map (fun b => b.toNat) s.toUTF8.toList))

end Lampe.Builtin
