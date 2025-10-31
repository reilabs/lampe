import Lampe
import Stdlib.Tp

namespace Lampe.Stdlib.List

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/--
Implements the ordering relation used by Noir's `Array` and `Slice` directly over Lean's `List`.
-/
@[simp]
def compareWith {α : Type}
    (f : α → α → Ordering)
    (self other : List α)
  : Ordering := match self, other with
| [], [] => .eq
| [], _ => .lt
| _, [] => .gt
| x::xs, y::ys => f x y |>.then $ compareWith f xs ys

theorem compareWith_take_then_drop {α : Type} {a b : List α}
    (i : ℕ)
    (f : α → α → Ordering)
  : compareWith f a b =
    (compareWith f (a.take i) (b.take i)).then (compareWith f (a.drop i) (b.drop i)) := by
  induction i generalizing a b with
  | zero => simp_all
  | succ n ih =>
    cases a
    all_goals cases b
    any_goals rfl
    · simp [←ih, Ordering.then_assoc]

/--
States that the provided list is pairwise ordered according to the relation `f`.

This is a strictly weaker notion than `List.Pairwise` or `List.Sorted` as it makes no claim as to
the transitivity of the provided relation `f`, while those statements do so.

This definition matches the notion of ordering used in `std::array::sort_via`, which does not (and
cannot) check for global ordering by the relation `f`.
-/
def OrderedBy (f : α → α → Prop) (l : List α) : Prop :=
  ∀i, (h : i < l.length - 1) → f l[i] l[i + 1]

namespace OrderedBy

theorem nil {f : α → α → Prop} : OrderedBy f [] := by simp_all [OrderedBy]

theorem singleton {f : α → α → Prop} : OrderedBy f [x] := by simp_all [OrderedBy]

theorem cons {f : α → α → Prop}
  : f x y → OrderedBy f (y :: xs) → OrderedBy f (x :: y :: xs) := by
  intro hh ht i hi

  induction xs with
  | nil =>
    simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.add_one_sub_one,
      Nat.lt_one_iff] at hi
    simp [hh, hi]
  | cons z zs ih =>
    simp at hi
    cases i
    · simp [hh]
    · conv =>
        congr
        · rw [List.getElem_cons_succ]
        · rw [List.getElem_cons_succ]
      apply ht
      simp_all

theorem tail_cons {f : α → α → Prop} : OrderedBy f (x :: y :: xs) → OrderedBy f (y :: xs) := by
  intro ha i hi
  have := ha (i + 1) (by simp_all)
  simp only [List.getElem_cons_succ] at this
  assumption

theorem cons_iff {f : α → α → Prop}
  : f x y ∧ OrderedBy f (y :: xs) ↔ OrderedBy f (x :: y :: xs) := by
  apply Iff.intro
  · intro a
    apply And.elim List.OrderedBy.cons a
  · intro a
    apply And.intro
    · have := a 0
      simp only [List.length_cons, add_tsub_cancel_right, lt_add_iff_pos_left, add_pos_iff,
        zero_lt_one, or_true, List.getElem_cons_zero, zero_add, List.getElem_cons_succ,
        forall_const] at this
      assumption
    · apply List.OrderedBy.tail_cons a

theorem pair {f : α → α → Prop} : f x y ↔ List.OrderedBy f [x, y] := by
  apply Iff.intro <;>
  · intro hf
    unfold OrderedBy at *
    simp_all

theorem trans_eq_Sorted {xs : List α} {f : α → α → Prop}
  : OrderedBy f xs → Transitive f → List.Sorted f xs := by
  intros ord trans

  induction xs with
  | nil => simp
  | cons z zs ih =>
    simp [List.Sorted.cons]

    apply And.intro
    · cases zs with
      | nil => simp
      | cons y ys =>
        have := List.OrderedBy.cons_iff.mpr ord
        have fzy := this.left
        have tord := this.right
        have rest_sorted := ih tord
        have : IsTrans α f := ⟨trans⟩
        have : List.Sorted f (z :: y :: ys) := List.sorted_cons_cons.mpr ⟨fzy, rest_sorted⟩
        exact List.rel_of_sorted_cons this
    · cases zs with
      | nil => simp
      | cons y ys => exact ih (List.OrderedBy.tail_cons ord)

theorem append {α} {xs : List α} {h} {x} {f : α → α → Prop}
  : (hf : f (xs.getLast h) x)
  → (ord_pfx : OrderedBy f xs)
  → OrderedBy f (xs ++ [x]) := by
  intros hf ord_pfd

  induction xs with
  | nil => exact singleton
  | cons y ys ih =>
    cases ys with
    | nil =>
      simp_all only [ne_eq, not_true_eq_false, List.nil_append, IsEmpty.forall_iff,
        List.getLast_singleton, List.cons_append]
      exact pair.mp hf
    | cons z zs =>
      have hne : z :: zs ≠ [] := by simp_all
      have ho : OrderedBy f (z :: zs) := (cons_iff.mpr ord_pfd).right
      have hf : f ((z :: zs).getLast (by omega)) x := by simp_all
      have ih := @ih (by assumption) (by assumption) (by assumption)
      simp only [List.cons_append] at *
      apply cons ((cons_iff.mpr ord_pfd).left) ih

end OrderedBy

