import Lampe

open Lampe

def p := 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1

axiom pPrime : Nat.Prime (p + 1)

namespace Merkle

abbrev bnField := Fp ⟨p, pPrime⟩

instance : ToString bnField where
  toString b := s!"{b.val}"

instance : Repr bnField where
  reprPrec b _ := toString b

end Merkle
