import Lampe.Builtin.Basic
namespace Lampe.Builtin

@[reducible]
def listRep (rep : Tp → Type _) : List Tp → Type := fun l => match l with
| tp :: tps => (rep tp) × (listRep rep tps)
| [] => Unit

@[reducible]
def HList.toProd (hList : HList rep tps) : (listRep rep) tps := match hList with
| .nil => ()
| .cons arg args => ⟨arg, HList.toProd args⟩

lemma listRep_tp_denote_is_tp_denote_tuple :
  listRep (Tp.denote p) tps = Tp.denote p (.tuple name tps) := by
  induction tps <;> {
    unfold listRep Tp.denoteArgs
    tauto
  }

def mkTuple := newGenericPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple name fieldTps)⟩)
  (fun _ fieldExprs => ⟨True,
    fun _ => listRep_tp_denote_is_tp_denote_tuple ▸ HList.toProd fieldExprs⟩)

def projectTuple (mem : Member outTp fieldTps) := newGenericPureBuiltin
  (fun name => ⟨[.tuple name fieldTps], outTp⟩)
  (fun _ h![tpl] => ⟨True, fun _ => indexTpl _ tpl mem⟩)

end Lampe.Builtin
