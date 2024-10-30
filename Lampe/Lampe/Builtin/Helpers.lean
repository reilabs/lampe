import Mathlib

namespace Lampe

/-- Extends the given list `a` up to length `len` with the default value of `α` -/
def extList (lst : List α) (len : Nat) (default : α) : List α
  := lst ++ (List.replicate (len - lst.length) default)

def withRadix (r : Nat) (v : Nat) (h : r > 1) : List Nat := match v with
| .zero => List.nil
| v' + 1 => List.cons ((v' + 1) % r) (withRadix r ((v' + 1) / r) h)
decreasing_by
  rw [Nat.succ_eq_add_one, Nat.div_lt_iff_lt_mul]
  rw [Nat.lt_mul_iff_one_lt_right]
  tauto
  exact Nat.succ_pos v'
  rw [<-Nat.ne_zero_iff_zero_lt]
  aesop

-- [3, 2, 1]
#eval (withRadix 10 123 (by linarith))
-- [1, 1, 0, 1, 1, 1, 1]
#eval (withRadix 2 123 (by linarith))

end Lampe
