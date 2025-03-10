import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
   Represents the Noir types that can be casted to each other.
 -/
 class CastTp (tp tp' : Tp) where
   cast : Tp.denote p tp → Tp.denote p tp'

 @[simp]
 instance : CastTp tp tp where
   cast := fun a => a

 @[simp]
 instance : CastTp (.u s) (.i s) where
   cast := fun a => a

 @[simp]
 instance : CastTp (.u s) (.field) where
   cast := fun a => a.toNat

 @[simp]
 instance : CastTp (.i s) (.u s) where
   cast := fun a => a

 @[simp]
 instance : CastTp (.i s) (.field) where
   cast := fun a => a.toNat

 @[simp]
 instance : CastTp (.field) (.u s) where
   cast := fun a => a.val

 @[simp]
 instance : CastTp (.field) (.i s) where
   cast := fun a => a.val

 inductive castOmni : Omni where
 | ok {P st tp tp' v Q} [CastTp tp tp'] :
   Q (some (st, CastTp.cast v)) → castOmni P st [tp] tp' h![v] Q

 def cast : Builtin := {
   omni := castOmni
   conseq := by
     unfold omni_conseq
     intros
     cases_type castOmni
     . apply castOmni.ok;
       simp_all
   frame := by
     unfold omni_frame
     intros
     cases_type castOmni
     . apply castOmni.ok
       . constructor <;> tauto
 }

 end Lampe.Builtin
