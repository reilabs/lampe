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

