import Lampe.Builtin.Basic
import Lampe.Data.Strings

namespace Lampe.Builtin

/--
Defines the conversion of strings of length `N` to a byte array of length `N`.

It is enforced that Noir strings are uninterpreted bytes, so the length `N` of a string is the
number of bytes it contains, not the number of characters (regardless of the encoding).

In Noir, this corresponds to `fn as_bytes<let N: u32>(self: str<N>) -> [u8; N]`.
-/
def strAsBytes := newGenericPureBuiltin
  (fun n => ⟨[.str n], (.array (.u 8) n)⟩)
  (fun n h![s] => ⟨s.length = n.toNat,
    fun _ => s.bytes⟩)

/--
Implements the semantics of the `arrayAsStrUnchecked` builtin in Noir.

In particular it performs no checking as to the validity of the provided bytes and blindly
constructs a string from them.
-/
def arrayAsStr! {N} (array : List.Vector (BitVec 8) N) : NoirStr N := 
  let bytes := array.map (fun x => UInt8.ofBitVec x)
  NoirStr.mk bytes

/--
Defines the conversion of arrays bytes of length `N` to a string of length `N`.

It is enforced that Noir strings are uninterpreted bytes, so the length `N` of the string is the
number of bytes it contains, not the number of characters (regardless of the encoding).

In Noir, this corresponds to `from<let N: u32>(bytes: [u8, N]) -> str<N>`.
-/
def arrayAsStrUnchecked := newGenericTotalPureBuiltin 
  (fun n => ⟨[(Tp.u 8).array n], (.str n)⟩)
  (fun _ h![a] => arrayAsStr! a)

end Lampe.Builtin
