import Lampe.SeparationLogic.ValHeap
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Builtin.Helpers
import Lampe.Builtin.Basic
import Mathlib.Tactic.Lemma

namespace Lampe.Builtin

inductive StubOmni : Omni where

/--
This is a dummy builtin to stub out unimplemented builtins.
It is impossible to construct a proof of this and therefore
any terms that use this builtin will not type be provable, but
they won't cause any unsoundness.
-/
def stub : Builtin := {
  omni := StubOmni,
  conseq := by
    unfold omni_conseq
    intros
    cases_type StubOmni,
  frame := by
    unfold omni_frame
    intros
    cases_type StubOmni
}

def sha256Compression := stub
def keccakf1600 := stub
def blake2s := stub
def blake3 := stub
def derivePedersenGenerators := stub
def poseidon2Permutation := stub
def multiScalarMul := stub
def embeddedCurveAdd := stub
def ecdsaSecp256r1 := stub
def ecdsaSecp256k1 := stub
def isUnconstrained := stub
def applyRangeConstraint := stub
def toLeRadix := stub
def toBeRadix := stub
def toLeBits := stub
def toBeBits := stub
def recursiveAggregation := stub
def assertConstant := stub
def staticAssert := stub
def asWitness := stub
def blackBox := stub
def xcheckedTransmute := stub
def arrayRefcount := stub
def sliceRefcount := stub

end Lampe.Builtin
