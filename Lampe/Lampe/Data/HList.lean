inductive HList {α : Type v} (β : α → Type u) : List α → Type (max u v) where
| nil : HList β []
| cons : ∀ {a : α} {as : List α}, β a → HList β as → HList β (a :: as)

syntax "h![" term,* "]" : term
macro_rules
| `(h![]) => `(HList.nil)
| `(h![$x]) => `(HList.cons $x HList.nil)
| `(h![$x, $xs,*]) => `(HList.cons $x h![$xs,*])
