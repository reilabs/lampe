import «std-1.0.0-beta.12».Extracted
import Lampe
import Stdlib.Tp

namespace Lampe.Stdlib.List

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr false
set_option Lampe.pp.STHoare false

/--
Implements the ordering relation used by Noir's `Array` and `Slice` directly over Lean's `List`.
-/
@[reducible]
def compareWith {α : Type}
    (f : α → α → Ordering)
    (self other : List α)
  : Ordering := match self, other with
| [], [] => .eq
| [], _ => .lt
| _, [] => .gt
| x::xs, y::ys => f x y |>.then $ compareWith f xs ys

@[simp]
theorem compareWith_nil {comparator : α → α → Ordering}
  : compareWith comparator [] [] = .eq := by
  simp [compareWith]

theorem compareWith_take_then_drop {α : Type} {a b : List α}
    (i : ℕ)
    (f : α → α → Ordering)
  : compareWith f a b = (compareWith f (a.take i) (b.take i)).then (compareWith f (a.drop i) (b.drop i)) := by
  sorry

