import Lampe.Ast
import Lampe.Builtin.Struct
import Lampe.Builtin.Array
import Lampe.Builtin.Slice

namespace Lampe

inductive Access (rep : Tp → Type _) : Tp → Tp → Type _
| tuple : (mem : Builtin.Member tp tps) → Access rep (.tuple name tps) tp
| array : (idx : rep $ .u 32) → Access rep (.array tp n) tp
| slice : (idx : rep $ .u 32) → Access rep (.slice tp) tp

def Access.get (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) : Option $ Tp.denote p tp₂ := match acc with
| .tuple mem => Builtin.indexTpl s mem
| .array (n := n) idx => if h : idx.toNat < n.toNat then s.get ⟨idx.toNat, h⟩ else none
| .slice idx => if h : idx.toNat < s.length then s.get ⟨idx.toNat, h⟩ else none

def Access.modify (acc : Access (Tp.denote p) tp₁ tp₂) (s : Tp.denote p tp₁) (v' : Tp.denote p tp₂) : Option $ Tp.denote p tp₁ := match acc with
| .tuple mem => Builtin.replaceTuple' s mem v'
| .array (n := n) idx => if h : idx.toNat < n.toNat then Builtin.replaceArray' s ⟨idx.toNat, h⟩ v' else none
| .slice idx => if h : idx.toNat < s.length then Builtin.replaceSlice' s ⟨idx.toNat, h⟩ v' else none

@[simp]
theorem Access.modify_get {acc : Access (Tp.denote p) tp₁ tp₂} {h : acc.modify s v' = some s'} :
  acc.get s' = v' := by
  cases acc <;> simp_all only [Access.get, Access.modify]
  case tuple =>
    aesop
  case array =>
    rename_i n idx
    cases em (idx.toNat < n.toNat) <;> aesop
  case slice =>
    rename_i idx
    cases em (idx.toNat < s.length)
    . simp_all only [reduceDIte, Option.some.injEq, List.get_eq_getElem, dite_some_none_eq_some]
      subst h
      simp_all only [List.length_modifyNth, exists_true_left]
      apply Builtin.index_replaced_slice
    . aesop

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

end Lampe
