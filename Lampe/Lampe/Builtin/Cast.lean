import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
   Represents the Noir types that can be casted to each other.
 -/
 class CastTp (tp tp' : CTp) where
   validate : Tp.denote p tp → Prop
   cast : (a : Tp.denote p tp) → (validate a) → Tp.denote p tp'

 @[simp]
 instance : CastTp tp tp where
   validate := fun _ => True
   cast := fun a _ => a

 @[simp]
 instance : CastTp (.u s) (.i s) where
   validate := fun a => a.toNat < 2^(s-1)
   cast := fun a _ => a

 @[simp]
 instance : CastTp (.u s) (.field) where
   validate := fun _ => True
   cast := fun a _ => a.toNat

 @[simp]
 instance : CastTp (.i s) (.u s) where
   validate := fun a => a.toNat ≥ 0
   cast := fun a _ => a

 @[simp]
 instance : CastTp (.i s) (.field) where
   validate := fun _ => True
   cast := fun a _ => a.toNat

 @[simp]
 instance : CastTp (.field) (.u s) where
   validate := fun a => a.val < 2^s
   cast := fun a h => ⟨a.val, h⟩

 @[simp]
 instance : CastTp (.field) (.i s) where
   validate := fun a => a.val < 2^(s-1) ∧ a.val ≥ 0
   cast := fun a h => ⟨a.val, by
     cases s
     . simp_all
     . simp_all only [add_tsub_cancel_right, Nat.pow_succ]
       linarith
   ⟩

 inductive castOmni : Omni where
 | ok {P st tp tp' v Q} [CastTp tp tp'] :
   (h : CastTp.validate tp' v) → Q (some (st, CastTp.cast v h)) → castOmni P st [tp] tp' h![v] Q
 | err {P st tp tp' v Q} [CastTp tp tp'] :
   ¬(CastTp.validate tp' v) → Q none → castOmni P st [tp] tp' h![v] Q

 def cast : Builtin := {
   omni := castOmni
   conseq := by
     unfold omni_conseq
     intros
     cases_type castOmni
     . apply castOmni.ok <;> simp_all
     . apply castOmni.err <;> simp_all
   frame := by
     unfold omni_frame
     intros
     cases_type castOmni
     . apply castOmni.ok
       . constructor <;> tauto
     . apply castOmni.err <;> assumption
 }

 end Lampe.Builtin
