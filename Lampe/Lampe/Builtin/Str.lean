import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

def strAsBytes {n : U 32} : Builtin := newBuiltin
  [.str] (.array (.u 8) n)
  (fun h![s] => s.utf8ByteSize == n)
  (fun h![s] _ => Array.mk (.map (fun b => b.toNat) s.toUTF8.toList))

end Lampe.Builtin
