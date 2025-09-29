import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the conversion of strings of length `N` to a byte array of length `N`.

It is enforced that Noir strings are uninterpreted bytes, so the length `N` of a string is the
number of bytes it contains, not the number of characters (regardless of the encoding).

In Noir, this corresponds to `fn as_bytes(self: str<N>) -> [u8; N]`.
-/
def strAsBytes := newGenericPureBuiltin
  (fun n => ⟨[.str n], (.array (.u 8) n)⟩)
  (fun n h![s] => ⟨s.length = n.toNat,
    fun _ => s⟩)

end Lampe.Builtin
