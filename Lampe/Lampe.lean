import Lampe.Basic
open Lampe

nr_def simple_muts<>(x : Field) -> Field {
  let mut y = x;
  let mut z = x;
  z = z;
  y = z;
  y
}

example : STHoare p Γ ⟦⟧ (simple_muts.fn.body _ h![] |>.body h![x]) fun v => v = x := by
  simp only [simple_muts]
  steps
  simp_all

nr_def weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #add(x, y) : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

example {x y : Tp.denote p .field} : STHoare p Γ ⟦⟧ (weirdEq.fn.body _ h![.field] |>.body h![x, y]) fun _ => x = y := by
  simp only [weirdEq]
  steps
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

example {self that : Tp.denote p (.slice tp)} : STHoare p Γ ⟦⟧ (sliceAppend.fn.body _ h![tp] |>.body h![self, that]) fun v => v = self ++ that := by
  simp only [sliceAppend]
  steps
  rename Tp.denote _ tp.slice.ref => selfRef
  loop_inv (fun i _ _ => [selfRef ↦ ⟨.slice tp, self ++ that.take i.toNat⟩])
  · intros i _ _
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      apply BitVec.add_toNat_of_lt_max
      casesm* (Tp.denote p (.u 32)), (U _), Fin _
      simp at *
      linarith
    simp only [this, List.take_succ]
    aesop
  · simp_all
  · simp_all
  steps
  simp_all [Nat.mod_eq_of_lt]

nr_def simple_if<>(x : Field, y : Field) -> Field {
  let mut z = x;
  if #eq(x, x) : bool {
    z = y
   }; -- else ()
  z
}

example {p Γ x y}: STHoare p Γ ⟦⟧ (simple_if.fn.body _ h![] |>.body h![x, y])
  fun v => v = y := by
  simp only [simple_if]
  steps <;> tauto
  . sl
  . sl
    simp_all
  . subst_vars
    rfl


nr_def simple_if_else<>(x : Field, y : Field) -> Field {
  let z = if #eq(x, x) : bool { x } else { y };
  z
}

example {p Γ x y}: STHoare p Γ ⟦⟧ (simple_if_else.fn.body _ h![] |>.body h![x, y])
  fun v => v = x := by
  simp only [simple_if_else]
  steps
  . simp only [decide_True, exists_const]
    sl
    contradiction
  . aesop

nr_def simple_lambda<>(x : Field, y : Field) -> Field {
  let add = |a : Field, b : Field| -> Field { #add(a, b) : Field };
  ^add(x, y) : Field;
}

example {p Γ} {x y : Tp.denote p Tp.field} :
  STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
  fun v => v = (x + y) := by
  simp only [simple_lambda]
  steps
  simp_all
  steps
  simp_all
  rotate_left 2
  simp_all [SLP.entails_self]
  exact (fun v => v = x + y)
  sl
  aesop
  sl
  aesop

nr_trait_impl[bulbulizeField] <> Bulbulize<> for Field {
    fn bulbulize<>(x : Field) -> Field {
      #add(x, x) : Field
    };
}


nr_trait_impl[bulbulizeU32] <> Bulbulize<> for u32 {
  fn bulbulize<>(_x : u32) -> u32 {
      69 : u32
    }
}

def simpleTraitCall (tp : Tp) (arg : tp.denote P): Expr (Tp.denote P) tp :=
  @Expr.call _ [] h![] [tp] tp (.trait ⟨⟨⟨"Bulbulize", [], h![]⟩, tp⟩, "bulbulize"⟩) h![arg]

def simpleTraitEnv : Env := {
  functions := [],
  traits := [bulbulizeField, bulbulizeU32]
}

example : STHoare p simpleTraitEnv ⟦⟧ (simpleTraitCall .field arg) (fun v => v = 2 * arg) := by
  simp only [simpleTraitCall]
  apply STHoare.callTrait_intro
  · constructor
    · apply List.Mem.head
    any_goals rfl
    rotate_left 2
    all_goals simp only
    . exact h![]
    · tauto
    · tauto
  · simp; rfl
  any_goals rfl
  simp
  steps
  rintro rfl
  casesm* ∃_,_
  subst_vars
  ring

example : STHoare p simpleTraitEnv ⟦⟧ (simpleTraitCall (.u 32) arg) (fun v => v = 69) := by
  simp only [simpleTraitCall]
  apply STHoare.callTrait_intro
  · constructor
    · apply List.Mem.tail
      apply List.Mem.head
    any_goals rfl
    rotate_left 2
    all_goals simp only
    . exact h![]
    · tauto
    · tauto
  · simp; rfl
  any_goals rfl
  simp
  steps
  simp_all
