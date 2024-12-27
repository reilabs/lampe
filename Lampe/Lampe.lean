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
  #fAdd(x, y) : I;
  #assert(#fEq(a, x) : bool) : Unit;
  #assert(#fEq(a, y) : bool) : Unit;
}

example {x y : Tp.denote p .field} : STHoare p Γ ⟦⟧ (weirdEq.fn.body _ h![.field] |>.body h![x, y]) fun _ => x = y := by
  simp only [weirdEq]
  steps
  simp_all

nr_def sliceAppend<I>(x: [I], y: [I]) -> [I] {
  let mut self = x;
  for i in (0 : u32) .. #sliceLen(y):u32 {
    self = #slicePushBack(self, #sliceIndex(y, i): I): [I]
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
  if #fEq(x, x) : bool {
    z = y
   };
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
  let z = if #fEq(x, x) : bool { x } else { y };
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
  let add = |a : Field, b : Field| -> Field { #fAdd(a, b) : Field };
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

nr_trait_impl[bulbulizeField] <> Bulbulize<> for Field where {
    fn bulbulize<>(x : Field) -> Field {
      #fAdd(x, x) : Field
    };
}

nr_trait_impl[bulbulizeU32] <> Bulbulize<> for u32 where {
  fn bulbulize<>(_x : u32) -> u32 {
      69 : u32
    }
}

def simpleTraitEnv : Env := {
  functions := [],
  traits := [bulbulizeField, bulbulizeU32]
}

def simple_trait_call (tp : Tp) (arg : tp.denote P): Expr (Tp.denote P) tp :=
  @Expr.call _ [] h![] [tp] tp (.trait ⟨⟨⟨"Bulbulize", [], h![]⟩, tp⟩, "bulbulize"⟩) h![arg]


example : STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call .field arg) (fun v => v = 2 * arg) := by
  simp only [simple_trait_call]
  steps
  apply_impl [] bulbulizeField.2
  tauto
  any_goals rfl
  simp only
  steps
  casesm ∃_, _
  intro
  subst_vars
  ring

example : STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call (.u 32) arg) (fun v => v = 69) := by
  simp only [simple_trait_call]
  steps
  apply_impl [] bulbulizeU32.2
  tauto
  any_goals rfl
  simp only
  steps
  aesop


example : STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call (.u 32) arg) (fun v => v = 69) := by
  simp only [simple_trait_call]
  steps
  try_impls [] [bulbulizeField.2, bulbulizeU32.2]
  tauto
  any_goals rfl
  simp only
  steps
  aesop

example : STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call (.u 32) arg) (fun v => v = 69) := by
  simp only [simple_trait_call]
  steps
  try_impls_all [] simpleTraitEnv
  tauto
  any_goals rfl
  simp only
  steps
  aesop


nr_def simple_trait_call_syntax<I> (x : I) -> I {
  (I as Bulbulize<>)::bulbulize<>(x : I) : I
}

example {p} {arg : Tp.denote p Tp.field} :
  STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call_syntax.fn.body _ h![.field] |>.body h![arg]) (fun v => v = 2 * arg) := by
  simp only [simple_trait_call_syntax]
  steps
  try_impls_all [] simpleTraitEnv
  tauto
  any_goals rfl
  simp only
  steps
  simp_all
  rotate_left 1
  all_goals try exact (fun v => v = 2 * arg)
  all_goals (sl; intro; subst_vars; ring)


nr_trait_impl[me] <I> Me<> for I where {
    fn me<>(x : I) -> I {
      x
    }
}

def genericTraitEnv : Env := {
  functions := [],
  traits := [me]
}

nr_def generic_trait_call<>(x : Field) -> Field {
  (Field as Me<>)::me<>(x : Field) : Field
}

example {p} {x : Tp.denote p Tp.field} :
  STHoare p genericTraitEnv ⟦⟧ (generic_trait_call.fn.body _ h![] |>.body h![x]) (fun v => v = x) := by
  simp only [generic_trait_call]
  steps
  try_impls_all [Tp.field] genericTraitEnv
  tauto
  all_goals try rfl
  simp_all
  steps
  sl
  aesop

nr_struct_def Pair <I> {
  a : I,
  b : I
}

nr_def struct_construct<>(a : Field, b : Field) -> Pair<Field> {
  Pair<Field> { a, b }
}

example {p} {a b : Tp.denote p .field} :
  STHoare p Γ ⟦⟧ (struct_construct.fn.body _ h![] |>.body h![a, b]) (fun v => v.fst = a ∧ v.snd = (b, ())) := by
  simp only [struct_construct]
  steps
  aesop

nr_def struct_project<>(x : Field, y : Field) -> Field {
  let s = Pair<Field> { x, y };
  (s as Pair<Field>).a
}

example {p} {x y : Tp.denote p .field} :
  STHoare p Γ ⟦⟧ (struct_project.fn.body _ h![] |>.body h![x, y]) (fun v => v = x) := by
  simp only [struct_project]
  steps
  aesop

nr_def basic_cast<>(x : u8) -> Field {
  #cast(x) : Field
}

example {p} {x : Tp.denote p $ .u 8} :
  STHoare p Γ ⟦⟧ (basic_cast.fn.body _ h![] |>.body h![x]) (fun (v : Tp.denote _ .field) => v = x.toNat) := by
  simp only [basic_cast]
  steps
  aesop
