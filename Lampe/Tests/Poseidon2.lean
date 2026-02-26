import Lampe

open Lampe

namespace Lampe.Tests.Poseidon2

private def bn254P : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
private axiom bn254_prime : Nat.Prime bn254P
private def bn254 : Prime := Prime.ofNat bn254P bn254_prime (by unfold bn254P; omega)

/-- Expected output of Poseidon2 permutation on all-zero input (from Noir/Barretenberg test). -/
private def expected0 : Nat := 0x18DFB8DC9B82229CFF974EFEFC8DF78B1CE96D9D844236B496785C698BC6732E
private def expected1 : Nat := 0x095C230D1D37A246E8D2D5A63B165FE0FADE040D442F61E25F0590E5FB76F839
private def expected2 : Nat := 0x0BB9545846E1AFA4FA3C97414A60A20FC4949F537A68CCECA34C5CE71E28AA59
private def expected3 : Nat := 0x18A4F34C9C6F99335FF7638B82AEED9018026618358873C982BBDDE265B2ED6D

/-- Smoke test: Poseidon2 permutation of [0,0,0,0] matches the known BN254 test vector. -/
theorem permute_zero_correct :
    let state : List.Vector (Fp bn254) 4 := ⟨[0, 0, 0, 0], rfl⟩
    let result := Builtin.Poseidon2.permute state
    result.get ⟨0, by omega⟩ = (expected0 : Fp bn254)
    ∧ result.get ⟨1, by omega⟩ = (expected1 : Fp bn254)
    ∧ result.get ⟨2, by omega⟩ = (expected2 : Fp bn254)
    ∧ result.get ⟨3, by omega⟩ = (expected3 : Fp bn254) := by native_decide

/-- Full sponge hash of [1,2,3,4] matching Noir's `hash_smoke_test`.
    Exercises a non-zero input through two permutation calls (absorb + squeeze). -/
theorem sponge_hash_correct :
    let iv : Fp bn254 := 4 * 18446744073709551616
    -- Absorb [1,2,3] fills cache, absorb 4 triggers duplex → permute([1, 2, 3, iv])
    let state1 := Builtin.Poseidon2.permute (⟨[(1 : Fp bn254), 2, 3, iv], rfl⟩)
    -- Squeeze: duplex with cache [4,0,0] → permute([state1[0]+4, state1[1], state1[2], state1[3]])
    let state2 := Builtin.Poseidon2.permute
      (⟨[state1.get ⟨0, by omega⟩ + 4,
        state1.get ⟨1, by omega⟩,
        state1.get ⟨2, by omega⟩,
        state1.get ⟨3, by omega⟩], rfl⟩)
    state2.get ⟨0, by omega⟩ =
      (0x130bf204a32cac1f0ace56c78b731aa3809f06df2731ebcf6b3464a15788b1b9 : Fp bn254) := by
  native_decide

end Lampe.Tests.Poseidon2
