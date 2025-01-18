import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the conversion of strings of length `n` to a byte array of length `n`.
Accordingly, we assume that the string has UTF-8 byte length of `n`.

In Noir, this corresponds to `fn as_bytes(self) -> [u8; n]` implemented for `str<n>`.
-/
def strAsBytes := newGenericPureBuiltin
  (fun n => ⟨[CTp.str n], (CTp.array (CTp.u 8) n)⟩)
  (fun n h![s] => ⟨s.toList.length = n.toNat,
    fun h => .map (fun u => u.toNat) ⟨s.toList, h⟩⟩)

end Lampe.Builtin
