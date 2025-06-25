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
  -- loop_inv fun i _ _ => ()
  

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
