import Lampe
import Mathlib
import Mathlib.Data.Nat.Log

lemma List.get!_append_eq_get! [Inhabited α] {l : List α} {h : i < l.length} : (l ++ [a]).get! i = l.get! i := by
  cases h' : l.get? i
  . have _ := List.get?_eq_get h
    simp_all
  . simp only [List.get!_eq_getElem!, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_append_left h]

lemma List.reverse_index [Inhabited α] {l : List α} {h : i < l.length} : l.reverse[i]! = l[l.length - 1 - i]! := by
  simp only [←List.get!_eq_getElem!, List.get!_eq_getD]
  rw [List.getD_reverse (h := h)]

lemma List.Vector.tail_toList_eq_toList_tail {l : List.Vector α n} : l.tail.toList = l.toList.tail := by
  cases l
  simp only [List.tail, List.Vector.tail, List.Vector.toList]
  aesop

lemma List.Vector.head_eq_toList_head {l : List.Vector α (n + 1)} (h : l.toList ≠ []) : l.head = l.toList.head h := by
  cases l
  simp only [List.head, List.Vector.head, List.Vector.toList]
  aesop

open Lampe

namespace Test

def Hash (t : Type) (n : Nat) := List.Vector t n -> t

/-- The reference recovery implementation. -/
def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : List.Vector Bool depth) (proof : List.Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
    | false => H ⟨[recover', pitem], by tauto⟩
    | true => H ⟨[pitem, recover'], by tauto⟩

/- Extracted Start -/

nr_def «mtree_recover»<>(idx : [bool], p : [Field], item : Field) -> Field {
  #assert(#uEq(#sliceLen(idx) : u32, #sliceLen(p) : u32) : bool) : Unit;
  let mut curr_h = item;
  for i in 0 : u32 .. #sliceLen(idx) : u32 {
    let dir = #sliceIndex(idx, #cast(i) : u32) : bool;
    let sibling_root = #sliceIndex(p, #cast(i) : u32) : Field;
    if dir {
      curr_h = (@mhash<> as λ(Field, Field) → Field)(sibling_root, curr_h);
    } else {
      curr_h = (@mhash<> as λ(Field, Field) → Field)(curr_h, sibling_root);
    };
  };
  curr_h;
}

/- Extracted End -/

/- Define the environment without the extracted `mhash`, since we define a separate axiom for this below. -/
def env := Lampe.Env.mk [(«mtree_recover».name, «mtree_recover».fn)] []

/-- Represents the output (i.e., the value of `curr_h`) at the end of the `i`th iteration of the Noir recovery function. -/
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

theorem recoverAux_eq_cons [Inhabited α] {idx : List Bool} {proof : List α} {hd₁ : d ≤ idx.length} {hd₂ : d ≤ proof.length}  :
    recoverAux h d idx proof item = recoverAux h d (a :: idx) (b :: proof) item := by
  induction d
  . rfl
  . rename_i n ih
    unfold recoverAux
    have h₁ : idx.reverse.get! n = (a :: idx).reverse.get! n := by
      simp only [List.reverse_cons]
      symm
      apply List.get!_append_eq_get!
      simp_all only [List.length_reverse]
      linarith
    have h₂ : proof.reverse.get! n = (b :: proof).reverse.get! n := by
      simp only [List.reverse_cons]
      symm
      apply List.get!_append_eq_get!
      simp_all only [List.length_reverse]
      linarith
    rw [←h₁, ←h₂, ih]
    simp_all
    linarith
    linarith

theorem recoverAux_eq_MerkleTree_recover [Inhabited α] {idx : List.Vector Bool d} {proof : List.Vector α d} {item : α} :
    recoverAux h d idx.toList proof.toList item = recover h idx proof item := by
  induction d
  . rfl
  . rename Nat => n
    rename_i _ ih
    simp [recoverAux, recover]
    have _ : n < idx.toList.length := by simp
    have _ : n < proof.toList.length := by simp
    have h₁ : idx.toList[0] = idx.head := by
      have _ : idx.toList ≠ [] := by
        cases idx; aesop
      have : idx.head = idx.toList.head (by tauto) := by
        cases idx; simp only [List.head, List.Vector.head]; aesop
      rw [this]
      symm
      apply List.head_eq_getElem
    have h₂ : proof.toList[0] = proof.head := by
      have _ : proof.toList ≠ [] := by cases proof; aesop
      have : proof.head = proof.toList.head (by tauto) := by
        cases proof; unfold List.head List.Vector.head; aesop
      rw [this]
      symm
      apply List.head_eq_getElem
    rw [h₁, ←h₂]
    cases idx.head <;> {
      simp only [Bool.false_eq_true, ↓reduceIte]
      congr
      cases h₁ : idx.toList <;> cases h₂ : proof.toList
      all_goals try {
        have _ : idx.length = 0 := by simp_all
        contradiction
      }
      rename_i _ _ _ _ tail₁ _ tail₂
      have _ : idx.toList.length = n + 1 := by apply List.Vector.length_val
      have _ : proof.toList.length = n + 1 := by apply List.Vector.length_val
      rw [←recoverAux_eq_cons (hd₁ := by simp_all) (hd₂ := by simp_all)]
      have h₁ : tail₁ = idx.tail.toList := by
        have : tail₁ = idx.toList.tail := by simp_all
        rw [this]
        symm
        apply List.Vector.tail_toList_eq_toList_tail
      have h₂ : tail₂ = proof.tail.toList := by
        have : tail₂ = proof.toList.tail := by simp_all
        rw [this]
        symm
        apply List.Vector.tail_toList_eq_toList_tail
      rw [h₁, h₂]
      apply ih (idx := idx.tail) (proof := proof.tail)
    }

theorem recoverAux_next_true [Inhabited α] {idx : List Bool} {proof : List α} {item : α} :
    idx.reverse.get! i = true → l = proof.reverse.get! i →
    (recoverAux h (i + 1) idx proof item = h ⟨[l, recoverAux h i idx proof item], by tauto⟩) := by
  intros
  conv => lhs; unfold recoverAux
  simp_all

theorem recoverAux_next_false [Inhabited α] {idx : List Bool} {proof : List α} {item : α} :
    idx.reverse.get! i = false → r = proof.reverse.get! i →
    (recoverAux h (i + 1) idx proof item = h ⟨[recoverAux h i idx proof item, r], by tauto⟩) := by
  intros
  conv => lhs; unfold recoverAux
  simp_all


/- Just for testing purposes... -/
def babyHash' : Hash Nat 2 := fun ⟨[a, b], _⟩ => (a + 2 * b) * 3

example : (recoverAux (α := Nat) babyHash' 0 [true, false, false] [243, 69, 6] 5) = 5 := rfl

example : (recoverAux (α := Nat) babyHash' 1 [true, false, false] [243, 69, 6] 5) = 51 := rfl

example : (recoverAux (α := Nat) babyHash' 2 [true, false, false] [243, 69, 6] 5) = 567 := rfl

example : (recoverAux (α := Nat) babyHash' 3 [true, false, false] [243, 69, 6] 5) = 4131 := rfl

lemma hypothesize {_ : P₁ → STHoare p env P₂ e Q} : STHoare p env (⟦P₁⟧ ⋆ P₂) e Q := by
  simp only [STHoare, THoare] at *
  intros H st h
  have _ : P₁ := by
    simp only [SLP.lift, SLP.star] at h
    tauto
  simp_all

lemma hypothesize' {_ : P₁ → STHoare p env (⟦P₁⟧ ⋆ P₂) e Q} : STHoare p env (⟦P₁⟧ ⋆ P₂) e Q := by
  simp only [STHoare, THoare] at *
  intros H st h
  have _ : P₁ := by
    simp only [SLP.lift, SLP.star] at h
    tauto
  simp_all

lemma extract_lift [LawfulHeap α] {P₁ : Prop} {P₂ : SLP α} :
    (⟦P₁⟧ ⋆ P₂) st → P₁ ∧ P₂ st := by
  simp only [SLP.star, SLP.lift]
  intros h
  obtain ⟨_, _, _, _, _⟩ := h
  simp_all

lemma exists_lift_eq_lift [LawfulHeap α] {hb : Inhabited β} : (∃∃ (_ : β), ⟦P⟧) = (⟦P⟧ : SLP α) := by
  unfold SLP.exists' SLP.lift
  simp_all

/- Assume that `mhash` is a valid hash function for any given `h` -/
axiom mhash_intro {p : Prime} {P : SLP (State p)} (h : Hash (Tp.denote p .field) 2)
    {a b : Tp.denote p .field}
    {fnRef : Tp.denote p $ .fn [.field, .field] .field}
    {_ : P ⊢ ⟦fnRef = FuncRef.decl "mhash" [] h![]⟧ ⋆ ⊤} :
    STHoare p env P (Expr.call [.field, .field] .field fnRef h![a, b]) fun v => ⟦v = h ⟨[a, b], by tauto⟩⟧ ⋆ P

/- Show that the output of `mtree_recover` matches with reference `recover` for every input, assuming that `mhash_intro` holds for `h`. -/
example [Inhabited (Tp.denote p .field)]
  {h : Hash (Tp.denote p .field) 2}
  {d : Nat}
  {idx : List.Vector Bool d}
  {proof : List.Vector (Tp.denote p .field) d}
  {item : Tp.denote p .field} :
    STHoare p env ⟦⟧ (mtree_recover.fn.body _ h![] |>.body h![idx.toList.reverse, proof.toList.reverse, item])
    fun v => v = recover h idx proof item := by
  simp only [mtree_recover]
  steps
  rename Ref => r
  rename_i vt₁ vt₂
  apply hypothesize'
  intro hvt₂
  simp only [List.length_reverse, List.Vector.toList_length, BitVec.natCast_eq_ofNat,
    exists_prop, -Nat.reducePow] at hvt₂
  . loop_inv (fun i _ _ => [r ↦ ⟨.field, recoverAux (α := (Tp.denote p .field)) h i.toNat idx.toList proof.toList item⟩])
    intros i hlo hhi
    . simp only
      generalize hrv : recoverAux (α := (Tp.denote p .field)) _ _ _ _ _ = rv
      apply STHoare.letIn_intro
      . steps
      . intros i'
        simp only [Builtin.CastTp.cast]
        rw [exists_lift_eq_lift (hb := by tauto)]
        apply hypothesize
        intro
        subst i'
        apply STHoare.letIn_intro
        . steps
        . intros dir
          simp [-Nat.reducePow]
          apply hypothesize'
          intro hdir₁
          obtain ⟨_, hdir₁⟩ := hdir₁
          apply STHoare.letIn_intro
          . steps
          . intros i'
            simp only [Builtin.CastTp.cast]
            rw [exists_lift_eq_lift (hb := by tauto)]
            apply hypothesize
            intro
            subst i'
            apply STHoare.letIn_intro
            steps
            intros v₁
            apply hypothesize'
            intro hv₁'
            simp at hv₁'
            obtain ⟨_, hv₁'⟩ := hv₁'
            apply STHoare.letIn_intro
            . apply STHoare.ite_intro (Q := fun _ => [r ↦ ⟨.field, recoverAux h (i.toNat + 1) idx.toList proof.toList item⟩]) <;> intro hdir₂
              <;> {
                apply STHoare.letIn_intro
                . steps
                . intro fnRef
                  apply STHoare.letIn_intro
                  . steps
                  . intro v₂
                    apply STHoare.letIn_intro
                    . apply mhash_intro h
                      sl
                      tauto
                    . intro v₃
                      steps
                      congr
                      simp only [Lens.modify, Option.get_some]
                      subst v₃ v₂
                      symm
                      first
                      | apply recoverAux_next_true <;> { simp_all } /- for the main branch -/
                      | apply recoverAux_next_false <;> { simp_all } /- for the else branch -/
              }
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
    simp_all only [Nat.cast_zero, BitVec.ofNat_eq_ofNat, List.length_reverse,
      List.Vector.toList_length, BitVec.natCast_eq_ofNat, exists_prop, beq_true, and_true,
      true_eq_decide_iff, exists_const, BitVec.toNat_ofNat, BitVec.ofNat_le_ofNat, Nat.zero_mod,
      zero_le, -Nat.reducePow]
    have : d % (2 ^ 32) = d := by simp_all
    rw [this]
    apply recoverAux_eq_MerkleTree_recover
