import Lampe.Builtin.Basic
import Lampe.Crypto.Blake3
import Lampe.Data.HList
import Lampe.Data.Field

namespace Lampe.Builtin

def blake3 := newGenericTotalPureBuiltin
  (fun (N : U 32) => ⟨[(Tp.u 8).array N], (Tp.u 8).array (32 : U 32)⟩)
  (fun _N h![input] => Crypto.Blake3.blake3Hash input)

end Lampe.Builtin
