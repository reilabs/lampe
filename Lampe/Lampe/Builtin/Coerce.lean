import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Represents the Noir types that can be implicitly coerced to each other.
Coercions are different from casts in the sense that coercions represent implicit value transformations, whereas casts are explicit.
-/
 class CoeTp (tp tp' : Tp) where
   validate : Tp.denote p tp → Prop
   coe : (a : Tp.denote p tp) → (validate a) → Tp.denote p tp'

 @[simp]
 instance : CoeTp tp tp where
   validate := fun _ => True
   coe := fun a _ => a

@[simp]
instance : CoeTp (Tp.concrete tp) (Tp.any) where
  validate := fun _ => True
  coe := fun v _ => ⟨tp, v⟩

@[simp]
instance : CoeTp (Tp.any) (Tp.concrete tp) where
  validate := fun ⟨tp', _⟩ => tp = tp'
  coe := fun ⟨_, v⟩ h => h ▸ v

 inductive coeOmni : Omni where
 | ok {tp tp' v Q} [CoeTp tp tp'] :
   (h : CoeTp.validate tp' v) → Q (some (st, CoeTp.coe v h)) → coeOmni p st [tp] tp' h![v] Q
 | err {tp tp' v Q} [CoeTp tp tp'] :
   ¬(CoeTp.validate tp' v) → Q none → coeOmni p st [tp] tp' h![v] Q

 def coe : Builtin := {
   omni := coeOmni
   conseq := by
     unfold omni_conseq
     intros
     cases_type coeOmni
     . apply coeOmni.ok <;> simp_all
     . apply coeOmni.err <;> simp_all
   frame := by
     unfold omni_frame
     intros
     cases_type coeOmni
     . apply coeOmni.ok
       . constructor <;> tauto
     . apply coeOmni.err <;> assumption
 }

end Lampe.Builtin
