import Lampe.Builtin.Prelude

namespace Lampe.Builtin
open Lampe.Builtin

def arrayLen {tp : Tp} {n : U 32} : Builtin := newBuiltin
  [(.array tp n)] (.u 32)
  (fun _ => True)
  (fun _ _ => n)

def arrayAsSlice {tp : Tp} {n : U 32}: Builtin := newBuiltin
  [(.array tp n)] (.slice tp)
  (fun _ => True)
  (fun h![a] _ => a.toList)

end Lampe.Builtin
