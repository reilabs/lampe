import Lampe.Ast
import Lampe.Builtin.Struct
import Lampe.Builtin.Array
import Lampe.Builtin.Slice

@[simp]
theorem List.get_inserted {l : List α} {v : α} : (l.insertNth idx v).get? idx = some v := by
  sorry

namespace Lampe

inductive Access (rep : Tp → Type _) : Tp → Tp → Type _
| tpl : (mem : Builtin.Member tp tps) → Access rep (.tuple name tps) tp
| arr : (idx : rep $ .u 32) → Access rep (.array tp n) tp
| slice : (idx : rep $ .u 32) → Access rep (.slice tp) tp

def Access.get (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) : Option $ Tp.denote p tp₂ := match acc with
| .tpl mem => Builtin.indexTpl s mem
| .arr (n := n) idx => if h : idx.toNat < n.toNat then s.get ⟨idx.toNat, h⟩ else none
| .slice idx => s.get? idx.toNat

def Access.modify (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) (v' : Tp.denote p tp₂) : Option $ Tp.denote p tp₁ := match acc with
| .tpl mem => Builtin.replaceTuple' s mem v'
| .arr (n := n) idx => if h : idx.toNat < n.toNat then Builtin.replaceArray' s ⟨idx.toNat, h⟩ v' else none
| .slice idx => Builtin.replaceSlice' s idx.toNat v'

@[simp]
theorem Access.modify_get {acc : Access (Tp.denote p) tp₁ tp₂} {h : acc.modify s v' = some s'} :
  acc.get s' = v' := by
  cases acc <;> simp_all only [Access.get, Access.modify]
  . aesop
  . rename_i n idx
    cases em (idx.toNat < n.toNat) <;> aesop
  . rename_i idx
    simp_all only [ite_true, Option.some.injEq]
    rw [←h]
    apply List.get_inserted

inductive Lens (rep : Tp → Type _) : Tp → Tp → Type _
| nil : Lens rep tp tp
| cons : Lens rep tp₁ tp₂ → Access rep tp₂ tp₃ → Lens rep tp₁ tp₃

@[simp]
def Lens.get (lens : Lens (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) : Option $ Tp.denote p tp₂ := match lens with
| .nil => s
| .cons l₁ a₁ => (l₁.get s) >>= a₁.get

@[simp]
def Lens.modify (lens : Lens (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) (v' : Tp.denote p tp₂) : Option $ Tp.denote p tp₁ := match lens with
| .nil => v'
| .cons l₁ a₂ => (l₁.get s) >>= (a₂.modify · v') >>= l₁.modify s

@[simp]
theorem Lens.modify_get {l : Lens (Tp.denote p) tp₁ tp₂} {h : l.modify s v' = some s'} :
 l.get s' = v' := by
  induction l
  . simp_all only [Lens.modify, Lens.get]
  . rename_i tp₁' tp₂' l a ih
    casesm* Access _ _ _
    . sorry
    . sorry
    . sorry


end Lampe