import Lampe.Ast
import Lampe.Builtin.Struct
import Lampe.Builtin.Array

namespace Lampe

inductive Access : Tp → Tp → Type _
| tpl : (mem : Builtin.Member tp tps) → Access (.tuple name tps) tp
| arr : (idx : Fin n.toNat) → Access (.array tp n) tp

def Access.get (acc : Access tp₁ tp₂) (s : Tp.denote p tp₁) : Tp.denote p tp₂ := match acc with
| .tpl mem => Builtin.indexTpl s mem
| .arr idx => s.get idx

def Access.modify (acc : Access tp₁ tp₂) (s : Tp.denote p tp₁) (v' : Tp.denote p tp₂) : Tp.denote p tp₁ := match acc with
| .tpl mem => Builtin.replaceTpl s mem v'
| .arr idx => Builtin.replaceArr s idx v'

@[simp]
theorem Access.modify_get {acc : Access tp₁ tp₂} : acc.get (acc.modify s v') = v' := by
  unfold Access.modify Access.get
  cases acc <;> simp_all

inductive Lens : Tp → Tp → Type _
| nil : Lens tp tp
| cons : Lens tp₁ tp₂ → Access tp₂ tp₃ → Lens tp₁ tp₃

@[simp]
def Lens.get (lens : Lens tp₁ tp₂) (s : Tp.denote p tp₁) : Tp.denote p tp₂ := match lens with
| .nil => s
| .cons l₁ a₁ => a₁.get (l₁.get s)

@[simp]
def Lens.modify (lens : Lens tp₁ tp₂) (s : Tp.denote p tp₁) (v' : Tp.denote p tp₂) : Tp.denote p tp₁ := match lens with
| .nil => v'
| .cons l₁ a₂ => l₁.modify s (a₂.modify (l₁.get s) v')

@[simp]
theorem Lens.modify_get {l : Lens tp₁ tp₂} : l.get (l.modify s v') = v' := by
  induction l
  . unfold Lens.modify Lens.get
    simp_all
  . unfold Lens.get Lens.modify Access.get Access.modify
    casesm* Access _ _ <;> simp_all

end Lampe
