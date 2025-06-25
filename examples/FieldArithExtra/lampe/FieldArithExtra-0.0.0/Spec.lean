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
    congr 1
    casesm* ∃ _, _
    simp_all only [BitVec.natCast_eq_ofNat, Builtin.instCastTpU, BitVec.ofNat_toNat, 
                   BitVec.setWidth_eq, Lens.modify, Option.isSome_some, Option.get_some, 
                   BitVec.ofNat_eq_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.one_mod]

    have : (i.toNat + 1) % 2^32 = i.toNat + 1 := by
      apply Nat.mod_eq_of_lt
      simp only [BitVec.lt_def] at *
      have : (N.toNat < 2^32) := by 
        cases N
        simp
      linarith

    rw [this]

    have : i.toNat < elems.toList.length := by
      simp_all [BitVec.lt_def]

    simp only [List.take_succ_eq_append_getElem, List.sum_append, *]
    congr 1
    simp only [List.Vector.toList_getElem, List.sum_cons, List.sum_nil, add_zero]
    rfl

  . steps
    have : N.toNat = elems.toList.length := by
      simp

    subst_vars
    simp only [this, List.take_length]

theorem multi_mul_correct
    {p : Prime}
    {N : U 32}
    {elems : Tp.denote p (Tp.array .field N.toNat)}
  : STHoare
      p
      «FieldArithExtra-0.0.0».Extracted.Lib.env
      (⟦⟧)
      («FieldArithExtra-0.0.0».Extracted.multi_mul.call h![N] h![elems])
      fun v => v = elems.toList.prod := by
  enter_decl
  steps

  loop_inv nat (fun i _ _ => [result ↦ ⟨.field, (elems.toList.take i).prod⟩])
  . change 0 ≤ N
    bv_decide

  . intros i _ _
    steps
    congr 1
    simp_all only [BitVec.natCast_eq_ofNat, Builtin.instCastTpU, BitVec.ofNat_toNat,
                   BitVec.setWidth_eq, BitVec.toNat_ofNat, Lens.modify, Option.isSome_some,
                   Option.get_some, List.Vector.toList_length, List.prod_take_succ,
                   mul_eq_mul_left_iff, List.prod_eq_zero_iff]
    casesm* ∃ _, _
    simp_all only [Lens.modify, Option.isSome_some]
    
    have eq_mod : i % 2^32 = i := by
      apply Nat.mod_eq_of_lt
      have : N.toNat < 2^32 := by
        cases N
        simp
      linarith

    conv at eq_mod =>
      lhs
      arg 2
      whnf

    simp_all only [eq_mod]
    left
    apply List.Vector.get_eq_get_toList

  . steps
    have nat_eq_len : N.toNat = elems.toList.length := by
      simp

    subst_vars
    simp only [nat_eq_len, List.take_length]

end Spec
