import Lampe
import Mathlib
import Mathlib.Data.Nat.Log

open Lampe

namespace Test

/- Extracted Start -/

nr_def «mtree_recover»<F, μ0>(h : μ0, idx : [bool], p : [F], item : F) -> F {
  #assert(#uEq(#sliceLen(idx) : u32, #sliceLen(p) : u32) : bool) : Unit;
  let mut curr_h = item;
  for i in 0 : u32 .. #sliceLen(idx) : u32 {
    let dir = #sliceIndex(idx, #cast(i) : u32) : bool;
    let sibling_root = #sliceIndex(p, #cast(i) : u32) : F;
    if dir {
      curr_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, sibling_root, curr_h);
    } else {
      curr_h = ((_ as MHash<F>)::hash_two<> as λ(_, F, F) → F)(h, curr_h, sibling_root);
    };
  };
  curr_h;
}


def env := Lampe.Env.mk [(«mtree_recover».name, «mtree_recover».fn)] []
/- Extracted End -/

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
def recoverAux {α : Type} [Inhabited α] (h : Hash α 2) (i : Nat) (idx : List Bool) (proof : List α) (leaf : α) : α := match i with
| 0 => leaf
| i' + 1 =>
  let dir := idx.reverse.get! i'
  let siblingRoot := proof.reverse.get! i'
  let subRoot := recoverAux h i' idx proof leaf
  if dir == true then
    h ⟨[siblingRoot, subRoot], rfl⟩
  else
    h ⟨[subRoot, siblingRoot], rfl⟩

def babyHash' : Hash Nat 2 := fun ⟨[a, b], _⟩ => (a + 2 * b) * 3

example : (recoverAux (α := Nat) babyHash' 0 [true, false, false] [243, 69, 6] 5) = 5 := rfl

example : (recoverAux (α := Nat) babyHash' 1 [true, false, false] [243, 69, 6] 5) = 51 := rfl

example : (recoverAux (α := Nat) babyHash' 2 [true, false, false] [243, 69, 6] 5) = 567 := rfl

example : (recoverAux (α := Nat) babyHash' 3 [true, false, false] [243, 69, 6] 5) = 4131 := rfl

example [Inhabited (Tp.denote p tp)] {t : MerkleTree (Tp.denote p tp) h d} {hh : (Tp.denote p hTp) = Hash (Tp.denote p tp) 2}
  {h₁ : t.proof idx = proof} {h₂ : t.itemAt idx = item} :
    STHoare p env ⟦⟧ (mtree_recover.fn.body _ h![tp, hTp] |>.body h![hh ▸ h, idx.toList.reverse, proof.toList.reverse, item])
    fun v => v = MerkleTree.recover h idx proof item := by
  simp only [mtree_recover]
  steps
  rename Ref => r
  . loop_inv (fun i _ _ => [r ↦ ⟨tp, recoverAux (α := (Tp.denote p tp)) h i.toNat idx.toList proof.toList item⟩])
    intros
    . steps
      stop _
    . simp_all
    . aesop
  . sorry
