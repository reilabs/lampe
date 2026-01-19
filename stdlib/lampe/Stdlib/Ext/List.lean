import Mathlib.Tactic

/-!
# List Extensions

Mathlib-style extensions for List operations, primarily for lexicographic comparisons.
-/

theorem List.lt_append_of_lt [DecidableEq α] [LT α] [DecidableLT α]
    (l₁ l₂ l₃ l₄ : List α) :
    l₁.length = l₂.length → l₁ < l₂ → l₁ ++ l₃ < l₂ ++ l₄ := by
  intro hl hlt
  rw [List.lt_iff_exists] at hlt
  simp only [hl, List.take_length, lt_self_iff_false, and_false, exists_idem, false_or] at hlt
  rcases hlt with ⟨i, h, _⟩
  rw [List.lt_iff_exists]
  right
  exists
    i,
    (by simp only [List.length_append]; linarith),
    (by simp only [List.length_append]; linarith)
  apply And.intro
  · intro j hj
    have : j < l₁.length := by linarith
    have : j < l₂.length := by linarith
    simp_all
  · simp_all

theorem List.take_succ_lt_of_take_lt [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α}
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) (hlt : l₁.take i < l₂.take i) :
    l₁.take (i + 1) < l₂.take (i + 1) := by
  rw [List.take_succ_eq_append_getElem hi₁, List.take_succ_eq_append_getElem hi₂]
  apply List.lt_append_of_lt
  · simp [
      Nat.min_eq_left (Nat.le_of_lt hi₁), Nat.min_eq_left (Nat.le_of_lt hi₂)
    ]
  · exact hlt

theorem List.take_succ_lt_of_getElem_lt [DecidableEq α] [LT α] [DecidableLT α]
    {l₁ l₂ : List α}
    (hi₁ : i < l₁.length) (hi₂ : i < l₂.length)
    (heq : l₁.take i = l₂.take i) (hlt : l₁[i] < l₂[i]) :
    l₁.take (i + 1) < l₂.take (i + 1) := by
  rw [
    List.take_succ_eq_append_getElem hi₁,
    List.take_succ_eq_append_getElem hi₂,
    heq
  ]
  exact List.append_left_lt (List.cons_lt_cons_iff.mpr (Or.inl hlt))

theorem List.lt_of_take_lt [DecidableEq α] [LT α] [DecidableLT α] {l₁ l₂ : List α} {n : Nat}
    (hlen₁ : l₁.length = n) (hlen₂ : l₂.length = n)
    (hlt : l₁.take n < l₂.take n) : l₁ < l₂ := by
  rw [←List.take_length (l := l₁), ←List.take_length (l := l₂), hlen₁, hlen₂]
  exact hlt

theorem List.do_pure_eq_map {α β : Type} (l : List α) (f : α → β) :
    (do let a ← l; pure (f a)) = List.map f l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show List.flatMap _ (x :: xs) = _
    simp only [List.flatMap_cons, Pure.pure, List.singleton_append, List.map_cons]
    congr 1
