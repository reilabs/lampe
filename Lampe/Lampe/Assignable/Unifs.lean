unif_hint (α : Type u) (l : List α) (n m : Nat) (e : α) where
  List.replicate m e =?= l
  n =?= m + 1
  ⊢ List.replicate n e =?= (e :: l)

unif_hint (α : Type u) (e : α) (n : Nat) where
  n =?= 0
  ⊢ List.replicate n e =?= []
