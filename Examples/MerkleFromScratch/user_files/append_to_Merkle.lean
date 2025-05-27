
open «Merkle-1.0.0».Ref
open «Merkle-1.0.0».Spec
open «Merkle-1.0.0».Extracted

def env := «Merkle-1.0.0».Extracted.Main.env

theorem main_correct [Fact (CollisionResistant «Merkle-1.0.0».Ref.State.compress)] {tree : MerkleTree (Fp lp) «Merkle-1.0.0».Ref.State.compress 32}:
    STHoare lp env
        ⟦⟧
        (main.call h![] h![tree.root, proof, item, index])
        (fun _ => item ∈ tree) := by
  enter_decl
  simp only
  steps [recover_intro (H:= «struct#Skyscraper».tp h![]) (N:=32) (hHash := SkyscraperHash_correct), weird_assert_eq_intro]
  use index.reverse
  subst_vars
  rename tree.root = _ => hroot
  rw [Eq.comm, MerkleTree.recover_eq_root_iff_proof_and_item_correct] at hroot
  exact hroot.2