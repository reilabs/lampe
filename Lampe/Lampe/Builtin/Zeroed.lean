import Lampe.Builtin.Basic
namespace Lampe.Builtin

/-- Returns a `zero` instance of a type -/
def tpZeroed (tp : Tp) : (Tp.denote p tp) := match tp with
| .u _ => 0
| .i _ => 0
| .bi => 0
| .field => 0
| .bool => false
| .unit => ()
| .str _ => Mathlib.Vector.ofFn (fun _ => (Char.ofNat 0))
| .slice _ => List.nil
| .array innerTp _ => Mathlib.Vector.ofFn (fun _ => (tpZeroed innerTp))
| .ref _ => { val := 0 }
| .struct (a :: as) => (tpZeroed a, tpZeroed (Tp.struct as))
| .struct [] => ()

/--
For any type `tp : Tp`, this evaluates to an instance of that type such that all of its field are set to zero.
We assume the following:
- If `tp` is an int, uint, bigint, or a `Field`, this evaluates to `0`.
- If `tp` is bool, this evaluates to `false`.
- If `tp` is unit, this evaluates to `()`.
- If `tp` is a string, this evaluates to `""`.
- If `tp` is a slice, this evaluates to `[]`.
- If `tp` is an array, this evaluates to an array of length `n` with all elements `zeroed`.
- If `tp` is a reference, this evaluates to a reference with value `0`.
- If `tp` is a struct, this evaluates to a struct with all fields `zeroed`.

In Noir, this builtin corresponds to `fn zeroed<T>() -> T` implemented for `T`.
-/
def zeroed := newGenericPureBuiltin
  (fun tp => ⟨[], tp⟩)
  (fun tp h![] => ⟨True,
    fun _ => tpZeroed tp⟩)

end Lampe.Builtin
