import Lampe
import ProvenZk

import «hasher-0.0.0».Extracted
import «Merkle-0.0.0».Extracted
import «skyscraper-0.0.0».Extracted

import «skyscraper-0.0.0».Spec

open Lampe

open «Merkle-0.0.0» (env)

open Skyscraper

instance {α H n} : Membership α (MerkleTree α H n) where
  mem t e := ∃p, e = MerkleTree.itemAt t p

lemma weird_assert_eq_intro : STHoare Field.lp env ⟦⟧ («Merkle-0.0.0::witness::weird_assert_eq».call h![] h![a, b]) (fun _ => a = b) := by
  enter_decl
  step_as (⟦⟧) (fun _ => ⟦⟧)
  · steps
    enter_decl
    steps
  steps
  simp_all

def List.Vector.takeF {α : Type} {n : Nat} (v : List.Vector α n) (i : Nat) (hi : i ≤ n) : List.Vector α i :=
  List.Vector.congr (by simp [hi]) (v.take i)

@[simp]
theorem List.Vector.takeF_all {v : List.Vector α n} : List.Vector.takeF v n (by simp) = v := by
  cases v
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, *]

theorem List.Vector.takeF_succ_eq_snoc_get {v : List.Vector α n} : List.Vector.takeF v (i + 1) hi = (List.Vector.takeF v i (by linarith)).snoc (v.get ⟨i, by linarith⟩) := by
  rcases v with ⟨v, rfl⟩
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, List.Vector.snoc, List.Vector.get, List.take_succ]

theorem recover_intro {H N idx proof item}
    (hHash : ∀ {a b}, STHoare Field.lp env
        ⟦True⟧
        («hasher-0.0.0::BinaryHasher».hash h![.field] H h![] h![] h![a,b])
        (fun v => v = H' (a ::ᵥ b ::ᵥ .nil))):
    STHoare Field.lp env ⟦True⟧ («Merkle-0.0.0::mtree_recover».call h![H, N] h![idx, proof, item]) (fun v => v = MerkleTree.recover H' idx.reverse proof.reverse item) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ =>
    [curr_h ↦ ⟨Tp.field,
      MerkleTree.recover H' (List.Vector.takeF idx i (by simpa [←BitVec.lt_def];)).reverse
                 (List.Vector.takeF proof i (by simpa [←BitVec.lt_def])).reverse item⟩]
  · simp only [Int.cast, IntCast.intCast, BitVec.ofInt_ofNat, BitVec.le_def, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.zero_mod, zero_le]
  · intro i _ hi
    steps
    step_as m =>
      ([curr_h ↦ ⟨Tp.field, m⟩])
      (fun _ => [curr_h ↦ ⟨Tp.field, if dir then H' (sibling_root ::ᵥ m ::ᵥ .nil) else H' (m ::ᵥ sibling_root ::ᵥ .nil) ⟩])
    · congr
      rename dir = _ => hdir
      rename sibling_root = _ => hsr
      simp at hdir hsr
      simp [MerkleTree.recover, List.Vector.takeF_succ_eq_snoc_get, ←hdir, ←hsr]
      cases dir <;> rfl

    apply STHoare.ite_intro <;> {
      rintro rfl
      steps [hHash]
    }

  steps
  subst_vars
  simp

set_option maxRecDepth 10000 in
lemma SkyscraperHash_correct: STHoare Field.lp env ⟦⟧
      («hasher-0.0.0::BinaryHasher».hash h![.field] («skyscraper-0.0.0::Skyscraper».tp h![]) h![] h![] h![a,b])
      (fun v => v = Ref.State.compress ⟨[a, b], rfl⟩) := by
  resolve_trait
  steps [Skyscraper.permute_intro]
  subst_vars
  rfl

theorem main_correct [Fact (CollisionResistant Ref.State.compress)]
    {tree : MerkleTree (Fp Field.lp) Ref.State.compress 32}:
    STHoare Field.lp env
        ⟦⟧
        («Merkle-0.0.0::main».call h![] h![tree.root, proof, item, index])
        (fun _ => item ∈ tree) := by
  enter_decl
  steps [recover_intro (H:= «skyscraper-0.0.0::Skyscraper».tp h![]) (N:=32) (hHash := SkyscraperHash_correct), weird_assert_eq_intro]
  use index.reverse
  subst_vars
  rename tree.root = _ => hroot
  rw [Eq.comm, MerkleTree.recover_eq_root_iff_proof_and_item_correct] at hroot
  exact hroot.2
