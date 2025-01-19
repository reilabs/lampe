import Lampe

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

example {x y : Tp.denote p CTp.field} :
  STHoare p Γ ⟦⟧ (weirdEq.fn.body _ h![.field] |>.body h![x, y]) fun _ => x = y := by
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

lemma BitVec.add_toNat_of_lt_max {a b : BitVec w} (h: a.toNat + b.toNat < 2^w) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [BitVec.add_def, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  assumption

example {self that : Tp.denote p (CTp.slice tp)} :
    STHoare p Γ ⟦⟧ (sliceAppend.fn.body _ h![tp] |>.body h![self, that])
    fun v => v = self ++ that := by
  simp only [sliceAppend]
  steps
  rename Tp.denote _ (.concrete tp.slice.ref) => selfRef
  loop_inv (fun i _ _ => [selfRef ↦ ⟨CTp.slice tp, self ++ that.take i.toNat⟩])
  · intros i _ _
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      apply BitVec.add_toNat_of_lt_max
      casesm* (Tp.denote p (CTp.u 32)), (U _), Fin _
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

example {p Γ x y} : STHoare p Γ ⟦⟧ (simple_if.fn.body _ h![] |>.body h![x, y])
    fun v => v = y := by
  simp only [simple_if]
  steps <;> try tauto
  . sl
  . sl
    simp_all
  . subst_vars
    rfl


nr_def simple_if_else<>(x : Field, y : Field) -> Field {
  let z = if #fEq(x, x) : bool { x } else { y };
  z
}

example {p Γ x y} : STHoare p Γ ⟦⟧ (simple_if_else.fn.body _ h![] |>.body h![x, y])
    fun v => v = x := by
  simp only [simple_if_else]
  steps
  . simp only [decide_true, exists_const]
    sl
    contradiction
  . simp_all [decide_true, exists_const]

nr_def simple_lambda<>(x : Field, y : Field) -> Field {
  let add = |a : Field, b : Field| -> Field { #fAdd(a, b) : Field };
  add(x, y)
}

example {p Γ} {x y : Tp.denote p CTp.field} :
    STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
    fun v => v = x + y := by
  simp only [simple_lambda]
  steps
  all_goals try simp only [Expr.coe, reduceDIte]
  steps
  . unfold SLP.entails
    intros
    simp
    tauto
  . steps
    . rw [←SLP.star_assoc]
      apply STHoare.callLambda_intro
      simp
      steps
      all_goals try exact fun v => v = x + y
      sl
      intros
      simp_all
    . simp [Expr.coe, reduceDIte]
      steps
      all_goals try exact fun v => v = x + y
      unfold SLP.entails
      intros st h
      apply SLP.ent_drop_left at h
      simp [SLP.forall']
      intros
      simp_all [SLP.wand, SLP.star, SLP.top, SLP.lift]
    . sl
      intros
      simp_all

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

nr_def simple_trait_call<I> (x : I) -> I {
  ((I as Bulbulize<>)::bulbulize<> as λ(I) → I)(x)
}

example {p} {arg : Tp.denote p CTp.field} :
    STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call.fn.body _ h![.field] |>.body h![arg])
    fun v => v = 2 * arg := by
  simp only [simple_trait_call]
  steps
  simp only [Expr.coe, reduceDIte]
  . steps
  . steps
    . apply STHoare.callTrait_intro
      sl
      tauto
      try_impls_all [] simpleTraitEnv
      all_goals try tauto
      simp only
      steps
      simp_all only [exists_const, SLP.true_star]
      on_goal 2 => exact fun v => v = 2 * arg
      sl
      intros
      subst_vars
      ring
    simp only [Expr.coe, reduceDIte]
    steps
    all_goals try exact fun v => v = 2 * arg
    repeat sl; simp_all

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
  ((Field as Me<>)::me<> as λ(Field) → Field)(x)
}

example {p} {x : Tp.denote p CTp.field} :
    STHoare p genericTraitEnv ⟦⟧ (generic_trait_call.fn.body _ h![] |>.body h![x])
    fun v => v = x := by
  simp only [generic_trait_call]
  steps
  simp only [Expr.coe, reduceDIte]
  steps
  . steps
    . apply STHoare.callTrait_intro
      sl
      tauto
      try_impls_all [CTp.field] genericTraitEnv
      tauto
      all_goals try rfl
      steps
    simp only [Expr.coe, reduceDIte]
    steps
    all_goals try exact fun v => v = x
    repeat sl; simp_all

nr_struct_def Pair <I> {
  a : I,
  b : I
}

nr_def struct_construct<>(a : Field, b : Field) -> Pair<Field> {
  Pair<Field> { a, b }
}

example {p} {a b : Tp.denote p CTp.field} :
    STHoare p Γ ⟦⟧ (struct_construct.fn.body _ h![] |>.body h![a, b])
    fun v => v.fst = a ∧ v.snd = (b, ()) := by
  simp only [struct_construct]
  steps
  aesop

nr_def struct_project<>(x : Field, y : Field) -> Field {
  let s = Pair<Field> { x, y };
  (s as Pair<Field>).a
}

example {p} {x y : Tp.denote p CTp.field} :
    STHoare p Γ ⟦⟧ (struct_project.fn.body _ h![] |>.body h![x, y])
    fun v => v = x := by
  simp only [struct_project]
  steps
  aesop

nr_def basic_cast<>(x : u8) -> Field {
  #cast(x) : Field
}

example {p} {x : Tp.denote p $ CTp.u 8} :
    STHoare p Γ ⟦⟧ (basic_cast.fn.body _ h![] |>.body h![x])
    fun (v : Tp.denote p CTp.field) => v = x.toNat := by
  simp only [basic_cast]
  steps
  aesop

nr_def add_two_fields<>(a : Field, b : Field) -> Field {
  #fAdd(a, b) : Field
}

nr_def call_decl<>() -> Field {
  (@add_two_fields<> as λ(Field, Field) → Field)(1 : Field, 2 : Field)
}

example : STHoare p ⟨[(add_two_fields.name, add_two_fields.fn)], []⟩ ⟦⟧
    (call_decl.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [call_decl]
  steps
  simp only [Expr.coe, reduceDIte]
  steps
  steps
  . simp only [Expr.coe, reduceDIte]
    steps
  . steps
    . apply STHoare.callDecl_intro
      sl
      tauto
      all_goals try tauto
      simp only [add_two_fields]
      steps
      all_goals try exact fun v => v = 3
      sl
      intros
      simp_all
      ring
    . simp only [Expr.coe, reduceDIte]
      steps
      all_goals try exact fun v => v = 3
      sl
      simp_all
    . sl
      simp_all

nr_def simple_tuple<>() -> Field {
  let t = `(1 : Field, true, 3 : Field);
  t.2
}

example : STHoare p Γ ⟦⟧ (simple_tuple.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [simple_tuple]
  steps
  aesop

nr_def simple_slice<>() -> bool {
  let s = &[true, false];
  s[[1 : u32]]
}

example : STHoare p Γ ⟦⟧ (simple_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.bool) => v = false := by
  simp only [simple_slice, Expr.mkSlice]
  steps
  rfl
  aesop

nr_def simple_array<>() -> Field {
  let arr = [1 : Field, 2 : Field];
  arr[1 : u32]
}

example : STHoare p Γ ⟦⟧ (simple_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 2 := by
  simp only [simple_array, Expr.mkArray]
  steps <;> try tauto
  aesop

nr_def simple_rep_array<>() -> [Field; 4] {
  let arr = [1 : Field ; 4];
  arr
}

example : STHoare p Γ ⟦⟧ (simple_rep_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p $ CTp.array _ _) => v.toList = [1, 1, 1, 1] := by
  simp only [simple_rep_array, Expr.mkArray]
  steps <;> try tauto
  aesop

nr_def simple_rep_slice<>() -> [Field] {
  let arr = &[1 : Field ; 4];
  arr
}

example : STHoare p Γ ⟦⟧ (simple_rep_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p $ CTp.slice _) => v = [1, 1, 1, 1] := by
  simp only [simple_rep_slice, Expr.mkArray]
  steps <;> try tauto
  aesop


nr_def tuple_lens<>() -> Field {
  let mut p = `(`(1 : Field, 2 : Field), 3 : Field);
  p .0 .1 = 3 : Field;
  p .0 .1
}

example : STHoare p Γ ⟦⟧ (tuple_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [tuple_lens]
  steps
  subst_vars
  simp_all only [Access.get, exists_const, Lens.modify, Lens.get, Option.bind_eq_bind,
    Option.some_bind, Option.bind_some, Option.some.injEq]
  subst_vars
  rfl

nr_def struct_lens<>() -> Field {
  let mut p = `(Pair<Field>{ 1 : Field, 2 : Field}, 3 : Field);
  (p .0 as Pair<Field>).b = 3 : Field;
  (p .0 as Pair<Field>).b
}

example : STHoare p Γ ⟦⟧ (struct_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [struct_lens]
  steps
  aesop

nr_def array_lens<>() -> Field {
  let mut p = `([1 : Field, 2 : Field], 3 : Field);
  p.0[1 : u32] = 3 : Field;
  p.0[1 : u32]
}

example : STHoare p Γ ⟦⟧ (array_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [array_lens]
  steps
  rfl
  on_goal 3 => exact (⟨[1, 3], (by rfl)⟩, 3)
  . simp_all
    subst_vars
    simp_all
    rename_i v _ _ _ a₁ a₂ _
    obtain ⟨_, _⟩ := a₁
    obtain ⟨_, _⟩ := a₂
    obtain ⟨_, snd⟩ := v
    obtain ⟨_, _⟩ := snd
    simp_all
    rfl
  . simp_all
    subst_vars
    rfl

nr_def slice_lens<>() -> Field {
  let mut p = `(&[1 : Field, 2 : Field], 3 : Field);
  p .0 [[1 : u32]] = 3 : Field;
  p .0 [[1 : u32]]
}

example : STHoare p Γ ⟦⟧ (slice_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [slice_lens]
  steps
  all_goals try exact ([1, 3], 3)
  all_goals try tauto
  . simp_all
    subst_vars
    simp_all
    rename_i v _ _ _ a₁ a₂ _
    obtain ⟨_, _⟩ := a₁
    obtain ⟨_, _⟩ := a₂
    obtain ⟨_, snd⟩ := v
    simp_all
    rfl
  . simp_all [Builtin.indexTpl]

nr_def deref_lens<>() -> Field {
  let r = #ref(`(5 : Field)) : &`(Field);
  *(r).0 = 3 : Field;
  *(r).0
}

example : STHoare p Γ ⟦⟧ (deref_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 3 := by
  simp only [deref_lens]
  steps
  subst_vars
  simp_all only [exists_const, Lens.modify, Lens.get]
  simp_all [Builtin.indexTpl]

nr_def simple_func<>() -> Field {
  10 : Field
}

nr_def call<>(f : λ() → Field) -> Field {
  f()
}

nr_def simple_hof<>() -> Field {
  let func = @simple_func<> as λ() → Field;
  (@call<> as λ(λ() → Field) → Field)(func)
}

example : STHoare p ⟨[(simple_func.name, simple_func.fn), (call.name, call.fn)], []⟩ ⟦⟧
    (simple_hof.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.field) => v = 10 := by
  simp only [simple_hof]
  steps
  simp only [Expr.coe, reduceDIte]
  steps
  . steps
    . apply STHoare.callDecl_intro
      sl
      tauto
      all_goals try tauto
      simp [simple_func, call]
      steps
      . apply STHoare.callDecl_intro
        sl
        intros
        subst_vars
        all_goals try tauto
        simp [simple_func]
        steps
        all_goals try exact fun v => v = 10
        sl
        simp_all
      simp [Expr.coe]
      steps
      all_goals try exact fun v => v = 10
      repeat sl; simp_all
    . simp [Expr.coe]
      steps
      all_goals try exact fun v => v = 10
      sl
      simp_all
    . sl
      simp_all

nr_def simple_unit<>() -> Unit {
  #unit
}

example : STHoare p Γ ⟦⟧ (simple_unit.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p CTp.unit) => v = () := by
  simp only [simple_unit]
  steps
  tauto
  simp
  unfold SLP.entails SLP.wand
  intros
  simp

nr_def impl_fn<>(x : ?impl) -> ?impl {
  x
}

nr_def trait_as_type<>(x : Field) -> Field {
  let f = @impl_fn<> as λ(?impl) → ?impl;
  f(x)
}

example : STHoare p ⟨[⟨impl_fn.name, impl_fn.fn⟩], []⟩ ⟦⟧
    (trait_as_type.fn.body _ h![] |>.body h![x])
    fun v => v = x := by
  simp only [trait_as_type]
  steps
  simp_all [impl_fn]
  simp [Expr.coe]
  steps
  simp [Expr.coe]
  steps
  apply STHoare.callDecl_intro
  sl
  tauto
  tauto
  all_goals try rfl
  steps
  simp [Expr.coe]
  steps
  all_goals try exact fun v => v = x
  . simp_all [SLP.entails, SLP.forall', SLP.exists']
    intros st h
    simp_all [SLP.exists', SLP.wand]
    intros st' _ _ _ h'
    obtain ⟨_, _⟩ := h'
    simp_all [SLP.star, SLP.wand, SLP.lift]
    obtain ⟨st₁, st₂, ⟨_, _, _, ⟨_, _, _, ⟨_, _, _, _⟩⟩⟩⟩ := h
    exists st₁, st₂
    refine ⟨by tauto, ?_, ?_, by tauto⟩
    aesop
    subst_vars
    simp_all
    rename_i h₁ _ h₂
    obtain ⟨_, _⟩ := h₁
    obtain ⟨_, _⟩ := h₂
    subst_vars
    simp
  . sl
    simp_all
