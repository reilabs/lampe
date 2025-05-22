import Lampe

open Lampe

namespace «Merkle-1.0.0»
namespace Field

def p := 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1

axiom pPrime : Nat.Prime (p + 1)

abbrev bnField := Fp ⟨p, pPrime⟩

instance : ToString bnField where
  toString b := s!"{b.val}"

instance : Repr bnField where
  reprPrec b _ := toString b

end Field
end «Merkle-1.0.0»
