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
      curr_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, sibling_root, curr_h);
    } else {
      curr_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, curr_h, sibling_root);
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

def babyHash' : Hash Nat 2 := fun ⟨[a, b], _⟩ => (a + 2 * b) * 3

example : (recoverAux (α := Nat) babyHash' 0 [true, false, false] [243, 69, 6] 5) = 5 := rfl

example : (recoverAux (α := Nat) babyHash' 1 [true, false, false] [243, 69, 6] 5) = 51 := rfl

example : (recoverAux (α := Nat) babyHash' 2 [true, false, false] [243, 69, 6] 5) = 567 := rfl

example : (recoverAux (α := Nat) babyHash' 3 [true, false, false] [243, 69, 6] 5) = 4131 := rfl

abbrev babyHashTp := «struct#BabyHash».tp h![]

abbrev babyHashFn := impl_405.snd.impl h![] |>.head (by tauto) |>.snd

theorem babyHashImpl_intro : STHoare p env ⟦⟧ (babyHashFn.body _ h![] |>.body h![s, l, r])
    fun v => v = (l + 2 * r) * 3 := by
  simp only [babyHashFn, impl_405, List.head_cons]
  steps
  intros
  simp_all [exists_const]

theorem hypothesize {_ : P₁ → STHoare p env P₂ e Q} : STHoare p env (⟦P₁⟧ ⋆ P₂) e Q := by sorry

theorem extract_lift [LawfulHeap α] {P₁ : Prop} {P₂ : SLP α} :
    (⟦P₁⟧ ⋆ P₂) st → P₁ ∧ P₂ st := by sorry


set_option maxHeartbeats 500000

example [Inhabited (Tp.denote p .field)] {t : MerkleTree (Tp.denote p .field) h d}
  {h₁ : t.proof idx = proof} {h₂ : t.itemAt idx = item} :
    STHoare p env ⟦⟧ (mtree_recover.fn.body _ h![.field, babyHashTp] |>.body h![h', idx.toList.reverse, proof.toList.reverse, item])
    fun v => v = MerkleTree.recover h idx proof item := by
  simp only [mtree_recover]
  steps
  rename Ref => r
  . loop_inv (fun i _ _ => [r ↦ ⟨.field, recoverAux (α := (Tp.denote p .field)) h i.toNat idx.toList proof.toList item⟩])
    intros
    . simp only
      generalize hrv : recoverAux (α := (Tp.denote p .field)) _ _ _ _ _ = rv
      steps
      . rename_i v₁ _ _ v₂
        apply STHoare.callTrait'_intro («struct#BabyHash».tp h![]) (Q := fun v => [r ↦ ⟨.field, rv⟩] ⋆ ⟦v = (v₁ + 2 * v₂) * 3⟧)
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
        refine ⟨by simp, by simp_all, ?_, by simp⟩
        unfold SLP.lift
        refine ⟨?_, by rfl⟩
        aesop
      . apply STHoare.letIn_intro
        . rw [SLP.star_comm]
          apply hypothesize
          intros
          apply STHoare.modifyLens_intro
        . intros
          steps
          unfold SLP.exists' SLP.forall'
          intros st₁ h
          simp_all
          unfold SLP.wand
          intros v st₂
          intros
          have : st₂ = ∅ := by simp_all [SLP.lift]
          simp_all
          apply SLP.ent_star_top
          tauto
      . rename_i v₁ _ _ v₂
        apply STHoare.callTrait'_intro («struct#BabyHash».tp h![]) (Q := fun v => [r ↦ ⟨.field, rv⟩] ⋆ ⟦v = (v₂ + 2 * v₁) * 3⟧)
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
        refine ⟨by simp, by simp_all, ?_, by simp⟩
        unfold SLP.lift
        refine ⟨?_, by rfl⟩
        aesop
      . sorry
      . sorry
    . sorry
    simp only [exists_const] at *
    subst_vars
    rename_i h₁ h₂ h₃ h₄ _
    obtain ⟨_, _⟩ := h₁
    obtain ⟨_, _⟩ := h₂
    obtain ⟨_, _⟩ := h₃
    obtain ⟨_, _⟩ := h₄
    subst_vars
    generalize hil₁ : (idx.toList.reverse.length) = l at *
    generalize hil₂ : BitVec.toNat ↑l = l' at *
    have : l' = idx.length := by
      rw [←hil₂, ←hil₁]
      aesop
    clear hil₁ hil₂
    subst_vars
    induction t generalizing l
    . unfold MerkleTree.recover
      aesop
    . unfold MerkleTree.recover recoverAux
      simp_all only [BitVec.ofNat_le_ofNat, Nat.zero_mod, zero_le, List.get!_eq_getElem!,
        List.getElem!_eq_getElem?_getD, List.length_reverse, List.Vector.toList_length,
        lt_add_iff_pos_right, zero_lt_one, List.getElem?_eq_getElem, List.getElem_reverse,
        add_tsub_cancel_right, tsub_self, Bool.default_bool, Option.getD_some, Nat.succ_eq_add_one,
        Nat.add_one_sub_one]
      have : idx.head = idx.toList[0] := by sorry
      rw [this]
      rename_i ih₁ ih₂ _ _ _ _
      cases idx.toList[0]
      . simp_all
        congr
        sorry
