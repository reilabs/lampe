import Lampe.SeparationLogic.ValHeap
import Lampe.Data.Field
import Lampe.Data.HList
import Lampe.Builtin.Basic
import Mathlib.Tactic.Lemma

namespace Lampe.Builtin

inductive StubOmni : Omni where

/--
This is a dummy builtin to stub out unimplemented builtins.

It is impossible to construct a proof of this and therefore any terms that use
this builtin will not type be provable, but they won't cause any unsoundness.
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

-- Note that many of the names here explicitly do not follow the Lean naming scheme, as they have
-- to match the name in extracted code that comes from Noir.
def aes128Encrypt := stub
def arrayRefcount := stub
def asWitness := stub
def assertConstant := stub
def blackBox := stub
def blake2S := stub
def blake3 := stub
def checkedTransmute := stub
def derivePedersenGenerators := stub
def ecdsaSecp256K1 := stub
def ecdsaSecp256R1 := stub
def embeddedCurveAdd := stub
def fmtstrAsCtstring := stub
def keccakf1600 := stub
def mkFormatString := stub
def multiScalarMul := stub
/--
Abstract Poseidon2 permutation function.
Opaque for now — to be replaced with the actual mathematical definition later.
-/
opaque poseidon2PermFn (p : Prime) (n : U 32) (state : List.Vector (Fp p) n.toNat)
    : List.Vector (Fp p) n.toNat := state

def poseidon2Permutation := newGenericTotalPureBuiltin
  (fun n : U 32 => ⟨[.array .field n, .u 32], .array .field n⟩)
  (fun n h![state, _width] => poseidon2PermFn _ n state)
def recursiveAggregation := stub
def sha256Compression := stub
def sliceRefcount := stub
def strAsCtstring := stub

end Lampe.Builtin
