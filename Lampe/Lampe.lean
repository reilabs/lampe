import Lampe.Basic
open Lampe

nr_def simple_muts<>(x : Field) -> Field {
  let mut y = x;
  let mut z = x;
  z = z;
  y = z;
  y
}

example : STHoare p Γ ⟦⟧ (simple_muts.fn.body _ h![] h![x]) fun v => v = x := by
  simp only [simple_muts]
  steps
  simp_all

nr_def weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

example {P} {x y : Tp.denote P .field} : STHoare P Γ ⟦⟧ (weirdEq.fn.body _ h![.field] h![x, y]) fun _ => x = y := by
  simp only [weirdEq]
  steps
  intros
  simp_all

nr_def sliceAppend<I>(x: [I], y: [I]) -> [I] {
  let mut self = x;
  for i in (0 : u32) .. #slice_len(y):u32 {
    self = #slice_push_back(self, #slice_index(y, i): I): [I]
  };
  self
}

lemma BitVec.add_toNat_of_lt_max {a b : BitVec w} (h: a.toNat + b.toNat < 2^w) : (a + b).toNat = a.toNat + b.toNat := by
  simp only [BitVec.add_def, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  assumption

example {self that : Tp.denote P (.slice tp)} : STHoare P Γ ⟦⟧ (sliceAppend.fn.body _ h![tp] h![self, that]) fun v => v = self ++ that := by
  simp only [sliceAppend]
  steps
  rename Tp.denote _ tp.slice.ref => selfRef
  loop_inv (fun i _ _ => [selfRef ↦ ⟨.slice tp, self ++ that.take i.toNat⟩])
  · intros i _ _
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      apply BitVec.add_toNat_of_lt_max
      casesm* (Tp.denote P (.u 32)), (U _), Fin _
      simp at *
      linarith
    simp only [this, List.take_succ]
    rename some _ = _ => h
    simp_all [←h]
  · simp_all
  · simp_all
  steps
  simp_all [Nat.mod_eq_of_lt]

nr_def simple_if<>(x : Field, y : Field) -> u32 {
  let y = if #eq(x, y) : bool { 4 : u32 } else { 4 : u32 };
  4 : u32
}

example {p Γ x y}: STHoare p Γ ⟦x = y⟧ (simple_if.fn.body (Tp.denote p) h![] h![x, y])
  fun v => v = BitVec.ofNat 32 4 := by
  simp only [simple_if]
  steps
  sorry
