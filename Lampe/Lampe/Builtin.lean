import Lampe.Ast
import Lampe.State

namespace Lampe.Builtin

private abbrev BigStep :=
  (P : Prime) → State P → (argTps : List Tp) → (outTp: Tp) → HList (Tp.denote P) argTps → Option (State P × Tp.denote P outTp) → Prop

private abbrev Omni :=
  (P: Prime) → State P → (argTps : List Tp) → (outTp: Tp) → HList (Tp.denote P) argTps → (Option (State P × Tp.denote P outTp) → Prop) → Prop

inductive assertBS : BigStep where
| mkT {st} : assertBS P st [.bool] .unit h![true] (some (st, unit)) -- TODO FIX
| mkF {st} : assertBS P st [.bool] .unit h![false] none

inductive assertOmni : Omni where
| t {st Q} : Q (some (st, ())) → assertOmni P st [.bool] .unit h![true] Q
| f {st Q} : Q none → assertOmni P st [.bool] .unit h![false] Q

-- theorem assertOmni_conseq :

def assert : Builtin := ⟨assertBS, assertOmni⟩

inductive eqBS : BigStep
| f {P st a b} : eqBS P st [.field, .field] .bool h![a, b] (some (st, (a == b)))
| u {P st s a b} : eqBS P st [.u s, .u s] .bool h![a, b] (some (st, (a == b)))

inductive eqOmni : Omni
| f {P st a b Q} : Q (some (st, a == b)) → eqOmni P st [.field, .field] .bool h![a, b] Q
| u {P st s a b Q} : Q (some (st, a == b)) → eqOmni P st [.u s, .u s] .bool h![a, b] Q

def eq : Builtin := ⟨eqBS, eqOmni⟩

inductive freshBS : BigStep where
| mk {P st tp v} : freshBS P st [] tp h![] (some (st, v))

inductive freshOmni : Omni where
| mk {P st tp Q} : (∀ v, Q (some (st, v))) → freshOmni P st [] tp h![] Q

def fresh : Builtin := ⟨freshBS, freshOmni⟩

inductive refBS : BigStep where
| mk {P st tp ref} {v : Tp.denote P tp} :
  ref ∉ st → refBS P st [tp] (tp.ref) h![v] (some (st.insert ref ⟨tp, v⟩, ref))

inductive refOmni : Omni where
| mk {P st tp Q v}: (∀ref, ref ∉ st → Q (some (st.insert ref ⟨tp, v⟩, ref))) →
  refOmni P st [tp] (tp.ref) h![v] Q

def ref : Builtin := ⟨refBS, refOmni⟩

inductive readRefBS : BigStep where
| mk {P st ref tp} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → readRefBS P st [tp.ref] tp h![ref] (some (st, v))

inductive readRefOmni : Omni where
| mk {P st tp Q ref} {v : Tp.denote P tp} :
  st.lookup ref = some ⟨tp, v⟩ → Q (some (st, v)) →
  readRefOmni P st [tp.ref] tp h![ref] Q

def readRef : Builtin := ⟨readRefBS, readRefOmni⟩

end Lampe.Builtin
