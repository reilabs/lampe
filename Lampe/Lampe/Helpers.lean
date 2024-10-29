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

/-- Converts a bitvector of width `w` to a list of `BitVec w'`s in little-endian encoding -/
def chunksOf (v : BitVec w) (w' : Nat) (h: w' > 0) : List (BitVec w') := List.map
  (fun i => BitVec.ofNat w' i)
  (withRadix (2^w') v.toNat (by
    apply Nat.lt_pow_of_log_lt
    tauto
    have hp : Nat.log 2 1 = 0 := by tauto
    rw [hp]
    tauto
  ))

-- [44, 1]
#eval List.map (fun i => i.toInt) (chunksOf (BitVec.ofNat 256 300) 8 (by linarith))
-- [-121, -42, 18]
#eval List.map (fun i => i.toInt) (chunksOf (BitVec.ofNat 256 1234567) 8 (by linarith))

#eval List.map (fun i => i.toNat)
  (let w := 256; let a := 300; (extList
    (chunksOf (BitVec.ofNat w a) 8 (by linarith))
    (w / 8)
    (BitVec.zero _)))

end Lampe
