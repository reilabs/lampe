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

/--
Defines the construction of a format string from its literal template and the values interpolated
into it.

Lampe models format strings as their literal template text (`FormatString len tps` is defeq to
`String`), so this returns the template converted to a Lean string and ignores the interpolated
values. The generic parameters are the template length `s`, the format string length `n`, the
types of the interpolated values `argTps`, and the format string's argument tuple type `tp`.

In Noir, this corresponds to the compiler-internal construction of `fmtstr<N, T>` literals.
-/
def mkFormatString := newGenericTotalPureBuiltin
  (fun (a : U 32 × U 32 × List Tp × Tp) => ⟨.str a.1 :: a.2.2.1, .fmtStr a.2.1 a.2.2.2⟩)
  (fun _ args => match args with
    | .cons s _ => NoirStr.toString s)

end Lampe.Builtin
