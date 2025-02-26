import Lampe
import Mathlib
import Mathlib.Data.Nat.Log

open Lampe

namespace Test


/- Extracted Start -/

nr_struct_def BabyHash<> {

}

/- [Todo] Fix impl generics -/
nr_trait_impl[impl_405] <> MHash<Field> for BabyHash<> where  {
    fn «hash_two»<> (_self : BabyHash<>, l : Field, r : Field) -> Field {
      #fMul(#fAdd(l, #fMul(2 : Field, r) : Field) : Field, 3 : Field) : Field;
    }
}

nr_def «mtree_recover»<F, μ0>(h : μ0, idx : [bool], p : [F], item : F) -> F {
  #assert(#uEq(#sliceLen(idx) : u32, #sliceLen(p) : u32) : bool) : Unit;
  let mut curr_h = item;
  for i in 0 : u32 .. #sliceLen(idx) : u32 {
    /- [Todo] Add casts back into index arguments -/
    let dir = #sliceIndex(idx, i) : bool;
    let sibling_root = #sliceIndex(p, i) : F;
    if dir {
      let new_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, sibling_root, curr_h);
      curr_h = new_h;
    } else {
      let new_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, curr_h, sibling_root);
      curr_h = new_h;
    };
  };
  curr_h;
}


def env := Lampe.Env.mk [(«mtree_recover».name, «mtree_recover».fn)] [impl_405]
/- Extracted End -/

example : Struct.tp «struct#BabyHash» h![] = Tp.tuple "BabyHash" [] := rfl

def Hash (t : Type) (n : Nat) := List.Vector t n -> t

def babyHash : Hash (Tp.denote p .field) 2 := fun ⟨[a, b], _⟩ => (a + 2 * b) * 3

inductive MerkleTree (F : Type) (H : Hash F 2) : Nat -> Type
| leaf : F  -> MerkleTree F H 0
| bin : MerkleTree F H depth -> MerkleTree F H depth -> MerkleTree F H (depth+1)
deriving Repr

namespace MerkleTree

def left {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin l _ => l

def leaves {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : List F := match t with
| leaf f => [f]
| bin l r => leaves l ++ leaves r

def right {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) : MerkleTree F H depth := match t with
| bin _ r => r

def treeFor {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H (Nat.succ depth)) (dir : Bool) : MerkleTree F H depth := match dir with
| false => t.left
| true => t.right

def root {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) : F := match t with
| leaf f => f
| bin l r => H ⟨[root l, root r], by tauto⟩

def itemAt {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : List.Vector Bool depth) : F := match depth with
  | Nat.zero => match t with
    | leaf f => f
  | Nat.succ _ => (t.treeFor p.head).itemAt p.tail

def proof {depth : Nat} {F: Type} {H: Hash F 2} (t : MerkleTree F H depth) (p : List.Vector Bool depth) : List.Vector F depth := match depth with
  | Nat.zero => List.Vector.nil
  | Nat.succ _ => List.Vector.cons (t.treeFor !p.head).root ((t.treeFor p.head).proof p.tail)

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : List.Vector Bool depth) (proof : List.Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
    | false => H ⟨[recover', pitem], by tauto⟩
    | true => H ⟨[pitem, recover'], by tauto⟩

end MerkleTree

@[reducible]
def recoverAux {α : Type} [Inhabited α] (h : Hash α 2) (i : Nat) (idx : List Bool) (proof : List α) (item : α) : α := match i with
| 0 => item
| i' + 1 =>
  let dir := idx.reverse.get! i'
  let siblingRoot := proof.reverse.get! i'
  let subRoot := recoverAux h i' idx proof item
  if dir == true then
    h ⟨[siblingRoot, subRoot], rfl⟩
  else
    h ⟨[subRoot, siblingRoot], rfl⟩

theorem recoverAux_eq_MerkleTree_recover [Inhabited (Tp.denote p .field)] {t : MerkleTree (Tp.denote p .field) h d} :
    recoverAux babyHash d idx.toList (t.proof idx).toList (t.itemAt idx) = MerkleTree.recover babyHash idx (t.proof idx) (t.itemAt idx) := by
  induction d
  . rfl
  . rename Nat => n
    rename_i _ ih
    simp [recoverAux, MerkleTree.recover]
    have : idx.toList[0] = idx.head := by sorry
    rw [this]
    cases idx.head <;> (simp; congr)
    . sorry
    . sorry

def babyHash' : Hash Nat 2 := fun ⟨[a, b], _⟩ => (a + 2 * b) * 3

example : (recoverAux (α := Nat) babyHash' 0 [true, false, false] [243, 69, 6] 5) = 5 := rfl

example : (recoverAux (α := Nat) babyHash' 1 [true, false, false] [243, 69, 6] 5) = 51 := rfl

example : (recoverAux (α := Nat) babyHash' 2 [true, false, false] [243, 69, 6] 5) = 567 := rfl

example : (recoverAux (α := Nat) babyHash' 3 [true, false, false] [243, 69, 6] 5) = 4131 := rfl

abbrev babyHashTp := «struct#BabyHash».tp h![]

abbrev babyHashFn := impl_405.snd.impl h![] |>.head (by tauto) |>.snd

theorem hypothesize {_ : P₁ → STHoare p env P₂ e Q} : STHoare p env (⟦P₁⟧ ⋆ P₂) e Q := by
  sorry

theorem hypothesize' {_ : P₁ → STHoare p env (⟦P₁⟧ ⋆ P₂) e Q} : STHoare p env (⟦P₁⟧ ⋆ P₂) e Q := by
  sorry

theorem extract_lift [LawfulHeap α] {P₁ : Prop} {P₂ : SLP α} :
    (⟦P₁⟧ ⋆ P₂) st → P₁ ∧ P₂ st := by sorry

theorem List.reverse_index [Inhabited α] {l : List α} : l.reverse[i]! = l[l.length - 1 - i]! := by
  sorry

set_option maxHeartbeats 500000

example [Inhabited (Tp.denote p .field)] {hd : d < 2^32} {t : MerkleTree (Tp.denote p .field) h d}
  {h₁ : t.proof idx = proof} {h₂ : t.itemAt idx = item} :
    STHoare p env ⟦⟧ (mtree_recover.fn.body _ h![.field, babyHashTp] |>.body h![h', idx.toList.reverse, proof.toList.reverse, item])
    fun v => v = MerkleTree.recover babyHash idx proof item := by
  simp only [mtree_recover]
  steps
  rename Ref => r
  . loop_inv (fun i _ _ => [r ↦ ⟨.field, recoverAux (α := (Tp.denote p .field)) babyHash i.toNat idx.toList proof.toList item⟩])
    intros i hlo hhi
    . simp only
      generalize hrv : recoverAux (α := (Tp.denote p .field)) _ _ _ _ _ = rv
      apply STHoare.letIn_intro
      . steps
      . intros dir
        simp [-Nat.reducePow]
        apply hypothesize'
        intro hdir₁
        obtain ⟨_, hdir₁⟩ := hdir₁
        apply STHoare.letIn_intro
        . steps
        . intros v₁
          apply hypothesize'
          intro hv₁'
          simp at hv₁'
          obtain ⟨_, hv₁'⟩ := hv₁'
          apply STHoare.letIn_intro
          . apply STHoare.ite_intro <;> intro hdir₂
            . apply STHoare.letIn_intro
              . steps
              . intro fRef
                apply STHoare.letIn_intro
                . steps
                . intro v₂
                  apply STHoare.letIn_intro
                  . apply STHoare.callTrait'_intro babyHashTp (Q := fun v => [r ↦ ⟨.field, rv⟩] ⋆ ⟦v₂ = rv⟧ ⋆ ⟦v = (v₁ + 2 * v₂) * 3⟧)
                    sl
                    tauto
                    try_impls_all [] env
                    all_goals try tauto
                    simp_all
                    steps
                    simp_all
                    intros st₁ h v
                    repeat (apply extract_lift at h; obtain ⟨_, h⟩ := h)
                    unfold SLP.wand SLP.star
                    intros st₂ _ _
                    exists st₁, st₂
                    refine ⟨by tauto, by tauto, by tauto, ?_⟩
                    exists ∅, ∅
                    rename_i h'
                    obtain ⟨_, _⟩ := h'
                    refine ⟨by simp, by simp_all, ?_, ?_⟩
                    . unfold SLP.lift
                      refine ⟨?_, by rfl⟩
                      aesop
                    . exists ∅, ∅
                      refine ⟨by simp, by simp, ?_⟩
                      simp_all [SLP.lift]
                  . intro v₃
                    steps
                    on_goal 2 => exact fun _ => [r ↦ ⟨.field, (recoverAux babyHash (i.toNat + 1) idx.toList proof.toList item)⟩]
                    simp_all
                    intros st h
                    simp_all [SLP.wand, SLP.lift]
                    intros st' _ _
                    exists st, st'
                    refine ⟨by tauto, by simp_all, ?_, by simp⟩
                    unfold SLP.exists' SLP.star SLP.lift at h
                    obtain ⟨st₁', st₂', h⟩ := h
                    obtain ⟨_, _, h₀, ⟨_, _, _⟩⟩ := h
                    have _ : v₂ = rv := by tauto
                    have _ : v₃ = (v₁ + 2 * v₂) * 3 := by
                      rename_i hu _
                      rw [←hv₁'] at hu
                      tauto
                    simp [exists_const] at h₀
                    have _ : st₁' = st := by simp_all
                    convert h₀
                    conv =>
                      lhs
                      unfold recoverAux babyHash
                    have : idx.toList.reverse[BitVec.toNat i]! := by
                      have : idx.toList.length = d := by
                        apply List.Vector.toList_length
                      rw [List.reverse_index, this]
                      have : idx.toList[d - 1 - i.toNat]! = idx.toList[d - 1 - i.toNat] := by
                        apply List.getElem!_of_getElem?
                        simp
                      rw [this]
                      tauto
                    simp [this]
                    have : (t.proof idx).toList.reverse[BitVec.toNat i]! = v₁ := by
                      have : proof.toList.length = d := by
                        apply List.Vector.toList_length
                      rw [hv₁', h₁]
                      rw [List.reverse_index]
                      apply List.getElem!_of_getElem?
                      simp
                    subst_vars
                    simp [this]
                    apply Or.inl; apply Or.inl;
                    unfold babyHash
                    rfl
                    tauto
            . apply STHoare.letIn_intro
              . steps
              . intro fRef
                apply STHoare.letIn_intro
                . steps
                . intro v₂
                  apply STHoare.letIn_intro
                  . apply STHoare.callTrait'_intro babyHashTp (Q := fun v => [r ↦ ⟨.field, rv⟩] ⋆ ⟦v₂ = rv⟧ ⋆ ⟦v = (v₂ + 2 * v₁) * 3⟧)
                    sl
                    tauto
                    try_impls_all [] env
                    all_goals try tauto
                    simp_all
                    steps
                    simp_all
                    intros st₁ h v
                    repeat (apply extract_lift at h; obtain ⟨_, h⟩ := h)
                    unfold SLP.wand SLP.star
                    intros st₂ _ _
                    exists st₁, st₂
                    refine ⟨by tauto, by tauto, by tauto, ?_⟩
                    exists ∅, ∅
                    rename_i h'
                    obtain ⟨_, _⟩ := h'
                    refine ⟨by simp, by simp_all, ?_, ?_⟩
                    . unfold SLP.lift
                      refine ⟨?_, by rfl⟩
                      aesop
                    . exists ∅, ∅
                      refine ⟨by simp, by simp, ?_⟩
                      simp_all [SLP.lift]
                  . intro v₃
                    steps
                    congr
                    generalize hrv' : recoverAux (α := (Tp.denote p .field)) _ _ _ _ _ = rv' at *
                    simp_all
                    unfold recoverAux
                    simp_all
                    unfold babyHash
                    simp_all
          . intros _
            steps
            congr
            have : i.toNat + 1 ≤ d := by linarith
            generalize i.toNat = i' at *
            symm
            apply Nat.mod_eq_of_lt
            linarith
    . aesop
    . aesop
  . steps
    simp_all [-Nat.reducePow]
    have : d % (2 ^ 32) = d := by simp_all
    rw [this]
    apply recoverAux_eq_MerkleTree_recover
