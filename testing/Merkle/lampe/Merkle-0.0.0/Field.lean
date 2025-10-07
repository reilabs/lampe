import Lampe

open Lampe

namespace «Merkle-0.0.0»
namespace Field

def fieldP := 21888242871839275222246405745257275088548364400416034343698204186575808495617

axiom fieldP_prime : Nat.Prime fieldP

lemma fieldP_gt_2 : fieldP > 2 := by unfold fieldP; norm_num

def p := Prime.ofNat fieldP fieldP_prime fieldP_gt_2

abbrev bnField := Fp p

instance : ToString bnField where
  toString b := s!"{b.val}"

instance : Repr bnField where
  reprPrec b _ := toString b

end Field
end «Merkle-0.0.0»
