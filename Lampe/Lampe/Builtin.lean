import Lampe.Ast
import Lampe.State

namespace Lampe.Builtin

inductive assert : Builtin where
| mk {P st} : assert P st [.bool] .unit h![true] .unit st

inductive eq : Builtin where
| f {P st a b} : eq P st [.field, .field] .bool h![a, b] (a == b) st
| u {P st s a b} : eq P st [.u s, .u s] .bool h![a, b] (a == b) st

inductive fresh : Builtin where
| mk {P st tp v} : fresh P st [] tp h![] v st

inductive ref : Builtin where
| mk {P st tp ref} {v : Tp.denote P tp} :
  ref ∉ st → Lampe.Builtin.ref P st [tp] (tp.ref) h![v] ref (st.insert ref ⟨tp, v⟩)

inductive readRef : Builtin where
| mk {P st ref tp} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → readRef P st [tp.ref] tp h![ref] v st

end Lampe.Builtin
