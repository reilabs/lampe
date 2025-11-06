import Lampe.Builtin.Basic

namespace Lampe.Builtin

def isUnconstrained := newTotalPureBuiltin 
  ([], .bool)
  (fun _ => false)

