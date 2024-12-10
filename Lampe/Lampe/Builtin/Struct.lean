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

lemma listRep_tp_denote_is_tp_denote_tuple {nameOpt} :
  listRep (Tp.denote p) tps = Tp.denote p (.tuple nameOpt tps) := by
  induction tps <;> {
    unfold listRep Tp.denoteArgs
    tauto
  }

def mkTuple := newGenericPureBuiltin
  (fun fieldTps => ⟨fieldTps, (.tuple none fieldTps)⟩)
  (fun _ fieldExprs => ⟨True,
    fun _ => listRep_tp_denote_is_tp_denote_tuple ▸ HList.toProd fieldExprs⟩)

def mkStruct := newGenericPureBuiltin
  (fun (name, fieldTps) => ⟨fieldTps, (.tuple (some name) fieldTps)⟩)
  (fun (_, _) fieldExprs => ⟨True,
    fun _ => listRep_tp_denote_is_tp_denote_tuple ▸ HList.toProd fieldExprs⟩)

@[reducible]
def tupleNth (p : Prime) (nameOpt : Option String) (fieldTps : List Tp)  (tpl : Tp.denote p (.tuple nameOpt fieldTps)) (n : Fin fieldTps.length) :
 Tp.denote p $ fieldTps.get n := match fieldTps with
  | _ :: tps => match tpl, n with
    | Prod.mk a _, Fin.mk 0 _ => a
    | _, Fin.mk (.succ n') _ => @tupleNth p nameOpt tps tpl.snd (Fin.mk n' (by aesop))

example : ((tupleNth p nameOpt (List.replicate 7 $ .u 16) (0, 1, 2, 3, 4, 5, 6, ())) $ Fin.mk 4 (by simp_all)) = BitVec.ofNat _ 4 := by rfl

inductive projectTupleOmni (n : Fin l) : Omni where
| mk {p st} {tpl Q} :
  (hl : l = fieldTps.length) →
  (ho : outTp = fieldTps.get (hl ▸ n)) →
  Q (some (st, ho ▸ tupleNth p nameOpt fieldTps tpl (hl ▸ n))) →
  projectTupleOmni n p st [.tuple nameOpt fieldTps] outTp h![tpl] Q

def projectTuple (n : Fin l) : Builtin := {
  omni := projectTupleOmni n
  conseq := by
    unfold omni_conseq
    intros
    cases_type projectTupleOmni
    tauto
  frame := by
    unfold omni_frame
    intros
    cases_type projectTupleOmni
    constructor
    simp only
    repeat apply Exists.intro <;> tauto
    assumption
}

end Lampe.Builtin
