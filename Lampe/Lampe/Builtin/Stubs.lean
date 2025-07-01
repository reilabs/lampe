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
def sha256_compression := stub
def keccakf1600 := stub
def blake2s := stub
def blake3 := stub
def derive_pedersen_generators := stub
def poseidon2_permutation := stub
def multi_scalar_mul := stub
def embedded_curve_add := stub
def ecdsa_secp256r1 := stub
def ecdsa_secp256k1 := stub
def is_unconstrained := stub
def apply_range_constraint := stub
def to_le_radix := stub
def to_be_radix := stub
def to_le_bits := stub
def to_be_bits := stub
def recursive_aggregation := stub
def assert_constant := stub
def static_assert := stub
def as_witness := stub
def black_box := stub
def checked_transmute := stub
def array_refcount := stub
def slice_refcount := stub
def aes128_encrypt := stub
def mkFormatString := stub

end Lampe.Builtin
