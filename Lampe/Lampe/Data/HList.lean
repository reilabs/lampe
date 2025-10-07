import Lean

inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v) where
| nil : HList β []
| cons : ∀ {a : α} {as : List α}, β a → HList β as → HList β (a :: as)

namespace HList

syntax "h![" term,* "]" : term
macro_rules
| `(h![]) => `(HList.nil)
| `(h![$x]) => `(HList.cons $x HList.nil)
| `(h![$x, $xs,*]) => `(HList.cons $x h![$xs,*])

@[reducible]
def replicate {rep : α → Type _} (v : rep tp) : (n : Nat) → HList rep (List.replicate n tp)
| .zero => HList.nil
| .succ n' => HList.cons v (HList.replicate v n')

@[reducible]
def snoc (hs : HList f tps) (a : f tp)
  : HList f (tps ++ [tp]) :=
match tps, hs with
| [], h![] => h![a]
| _::_, HList.cons x xs => HList.cons x (HList.snoc xs a)

open Lean PrettyPrinter

@[app_unexpander HList.nil]
def delabNil : Unexpander
| `($(_)) => `(h![])

-- Inspired by the `List.cons` unexpander
@[app_unexpander HList.cons]
def delabCons : Unexpander
| `($(_) $x $tail) =>
  match tail with
  | `(h![])      => `(h![$x])
  | `(h![$xs,*]) => `(h![$x, $xs,*])
  | _          => pure
| _ => pure

end HList
