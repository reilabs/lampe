import «FieldArithExtra-0.0.0».Extracted
import Lampe

open Lampe

namespace Spec

set_option Lampe.pp.Expr true 
theorem multi_add_correct
    {p : Prime}
    {N : U 32}
    {elems : Tp.denote p (Tp.array .field N.toNat)}
  : STHoare
      p
      «FieldArithExtra-0.0.0».Extracted.Lib.env
      (⟦⟧)
      («FieldArithExtra-0.0.0».Extracted.multi_add.call h![N] h![elems])
      fun v => v = elems.toList.sum := by
  enter_decl
  steps
  loop_inv (fun i _ _ => [result ↦ ⟨.field, (elems.toList.take i.toNat).sum⟩]) 
  . change 0 ≤ N
    bv_decide
  . intros i _ _
    steps
    apply_assumption
    simp_all only [BitVec.natCast_eq_ofNat, Builtin.instCastTpU, BitVec.ofNat_toNat, 
                   BitVec.setWidth_eq, Lens.modify, Option.isSome_some, Option.get_some, 
                   BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.one_mod]
    apply_assumption
    simp_all only [Lens.modify, Option.isSome_some]
    subst_vars
    sorry
    
  sorry

theorem multi_mul_correct
    {p : Prime}
    {N : U 32}
    {elems : Tp.denote p (Tp.array .field N.toNat)}
  : STHoare
      p
      «FieldArithExtra-0.0.0».Extracted.Lib.env
      (⟦⟧)
      («FieldArithExtra-0.0.0».Extracted.multi_add.call h![N] h![elems])
      fun v => v = elems.toList.prod := by
  sorry

end Spec
