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

example {x y : Tp.denote p .field} :
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

example {self that : Tp.denote p (.slice tp)} :
    STHoare p Γ ⟦⟧ (sliceAppend.fn.body _ h![tp] |>.body h![self, that])
    fun v => v = self ++ that := by
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

example {p Γ x y} : STHoare p Γ ⟦⟧ (simple_if.fn.body _ h![] |>.body h![x, y])
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

example {p Γ x y} : STHoare p Γ ⟦⟧ (simple_if_else.fn.body _ h![] |>.body h![x, y])
    fun v => v = x := by
  simp only [simple_if_else]
  steps
  . simp only [decide_True, exists_const]
    sl
    contradiction
  . simp_all [decide_True, exists_const]

nr_def simple_lambda<>(x : Field, y : Field) -> Field {
  let add = |a : Field, b : Field| -> Field { #fAdd(a, b) : Field };
  add(x, y);
}

example {p Γ} {x y : Tp.denote p Tp.field} :
    STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
    fun v => v = x + y := by
  simp only [simple_lambda]
  steps
  . apply STHoare.consequence_frame_left STHoare.callLambda_intro
    . rw [SLP.star_assoc, SLP.star_comm, SLP.star_assoc]
      rw [SLP.top_star_top]
      apply SLP.ent_star_top
    . exact fun v => v = x + y
    . simp only
      steps
      simp_all only [exists_const, SLP.true_star]
      unfold SLP.wand SLP.entails SLP.forall'
      intros _ _ _ _ _ _
      simp_all [SLP.star, SLP.lift]
  simp_all
  steps
  simp_all
  intros st₁ h₁ v st₂ _ _
  apply SLP.ent_drop_left at h₁
  unfold SLP.lift SLP.star at *
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

example {p} {arg : Tp.denote p Tp.field} :
    STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call.fn.body _ h![.field] |>.body h![arg])
    fun v => v = 2 * arg := by
  simp only [simple_trait_call]
  steps
  . apply STHoare.callTrait_intro
    sl
    tauto
    try_impls_all [] simpleTraitEnv
    all_goals tauto
    simp only
    steps
    simp_all only [exists_const, SLP.true_star]
    on_goal 2 => exact (fun v => v = 2 * arg)
    sl
    intros
    subst_vars
    ring
  steps
  intros
  subst_vars
  rfl

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

example {p} {x : Tp.denote p Tp.field} :
    STHoare p genericTraitEnv ⟦⟧ (generic_trait_call.fn.body _ h![] |>.body h![x])
    fun v => v = x := by
  simp only [generic_trait_call]
  steps
  . apply STHoare.callTrait_intro
    sl
    tauto
    try_impls_all [Tp.field] genericTraitEnv
    tauto
    all_goals try rfl
    steps
  . steps
    simp_all

nr_struct_def Pair <I> {
  a : I,
  b : I
}

nr_def struct_construct<>(a : Field, b : Field) -> Pair<Field> {
  Pair<Field> { a, b }
}

example {p} {a b : Tp.denote p .field} :
    STHoare p Γ ⟦⟧ (struct_construct.fn.body _ h![] |>.body h![a, b])
    fun v => v.fst = a ∧ v.snd = (b, ()) := by
  simp only [struct_construct]
  steps
  aesop

nr_def struct_project<>(x : Field, y : Field) -> Field {
  let s = Pair<Field> { x, y };
  (s as Pair<Field>).a
}

example {p} {x y : Tp.denote p .field} :
    STHoare p Γ ⟦⟧ (struct_project.fn.body _ h![] |>.body h![x, y])
    fun v => v = x := by
  simp only [struct_project]
  steps
  aesop

nr_def basic_cast<>(x : u8) -> Field {
  #cast(x) : Field
}

example {p} {x : Tp.denote p $ .u 8} :
    STHoare p Γ ⟦⟧ (basic_cast.fn.body _ h![] |>.body h![x])
    fun (v : Tp.denote p .field) => v = x.toNat := by
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
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [call_decl]
  steps
  apply STHoare.callDecl_intro
  . sl
    tauto
  on_goal 3 => exact add_two_fields.fn
  all_goals tauto
  on_goal 3 => exact fun v => v = 3
  . simp only [add_two_fields]
    steps
    simp_all
    intros
    ring
  . steps
    simp_all

nr_def simple_tuple<>() -> Field {
  let t = `(1 : Field, true, 3 : Field);
  t.2
}

example : STHoare p Γ ⟦⟧ (simple_tuple.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [simple_tuple]
  steps
  aesop

nr_def simple_slice<>() -> bool {
  let s = &[true, false];
  s[[1 : u32]]
}

example : STHoare p Γ ⟦⟧ (simple_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .bool) => v = false := by
  simp only [simple_slice, Expr.mkSlice]
  steps
  rfl
  aesop

nr_def simple_array<>() -> Field {
  let arr = [1 : Field, 2 : Field];
  arr[1 : u32]
}

example : STHoare p Γ ⟦⟧ (simple_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 2 := by
  simp only [simple_array, Expr.mkArray]
  steps <;> tauto
  aesop

nr_def tuple_lens<>() -> Field {
  let mut p = `(`(1 : Field, 2 : Field), 3 : Field);
  p .0 .1 = 3 : Field;
  p .0 .1
}

example : STHoare p Γ ⟦⟧ (tuple_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
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
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [struct_lens]
  steps
  aesop

nr_def array_lens<>() -> Field {
  let mut p = `([1 : Field, 2 : Field], 3 : Field);
  p.0[1 : u32] = 3 : Field;
  p.0[1 : u32]
}

example : STHoare p Γ ⟦⟧ (array_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [array_lens]
  steps
  rfl
  on_goal 3 => exact (⟨[1, 3], (by rfl)⟩, 3)
  . simp_all
    rfl
  . simp_all
    aesop

nr_def slice_lens<>() -> Field {
  let mut p = `(&[1 : Field, 2 : Field], 3 : Field);
  p .0 [[1 : u32]] = 3 : Field;
  p .0 [[1 : u32]]
}

example : STHoare p Γ ⟦⟧ (slice_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [slice_lens]
  steps
  all_goals try exact ([1, 3], 3)
  all_goals try tauto
  . simp_all
    rfl
  . simp_all [Builtin.indexTpl]

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
    fun (v : Tp.denote p .field) => v = 10 := by
  simp only [simple_hof]
  steps
  . apply STHoare.callDecl_intro
    sl
    all_goals tauto
    simp only [call]
    steps
    . apply STHoare.callDecl_intro
      sl
      all_goals tauto
      simp only [simple_func]
      steps
      on_goal 2 => exact fun v => v = 10
      sl
      simp_all
    . steps
      on_goal 2 => exact fun v => v = 10
      sl
      simp_all
  steps
  simp_all


nr_struct_def Option2<T> {
    _is_some : bool,
    _value : T
}
nr_def «my_fn»<>() -> u8 {
    #uAdd(1 : u8, 1 : u8) : u8;
}

nr_def «my_func»<>(a : u8) -> u8 {
    #uAdd(a, 1 : u8) : u8;
}

nr_def «my_func3»<>(a : u8) -> u8 {
    (@my_func<> as λ(u8) → u8)(a);
}

nr_trait_impl[impl_270] <T> MyTrait<> for Option2<T> where {
    fn foo<> (self : Option2<T>) -> Option2<T> {
        self;
}
}

#print impl_270

nr_def «get_unchecked»<T>(a : Option2<T>) -> T {
    (a as Option2<T>)._value;
}


nr_def «Option2::some»<T>(_value : T) -> Option2<T> {
    Option2<T> { true, _value };
}

nr_def «Option2::is_some»<T>(self : Option2<T>) -> bool {
    (self as Option2<T>)._is_some;
}

nr_def «Option2::is_none»<T>(self : Option2<T>) -> bool {
    #bNot((@Option2::is_some<T> as λ(Option2<T>) → bool)(self)) : bool;
}

nr_def «my_func2»<>(arr : [u8; 8], b : u8) -> u8 {
    #arrayIndex(arr, #cast(b) : u32) : u8;
}

nr_def «Option2::none»<T>() -> Option2<T> {
    Option2<T> { false, #zeroed() : T };
}

nr_def «cast_test»<>(a : u8) -> u64 {
    if #uEq(a, 0 : u8) : bool {
            0 : u64;
    } else {
            #cast(a) : u64;
    };
}

nr_trait_impl[impl_269] <T> std::default::Default<> for Option2<T> where {
    fn default<> () -> Option2<T> {
        (@Option2::none<T> as λ() → Option2<T>)();
}
}


nr_def «tuple_test»<>(a : u8) -> `(u8, u8) {
    let b = |c : u8| -> u8 #uAdd(#uAdd(c, a) : u8, 10 : u8) : u8;
    `(a, a);
}

nr_def «_main»<>() -> Unit {
    let mut op1 = (@Option2::some<Field> as λ(Field) → Option2<Field>)(5 : Field);
    let op2 = ((Option2<T> as Default<>)::default<Field> as λ() → Option2<Field>)();
    let op3 = ((Option2<T> as MyTrait<>)::foo<Field> as λ(Option2<Field>) → Option2<Field>)(if true {
            op1;
    } else {
            op2;
    });
    (@Option2::is_some<Field> as λ(Option2<Field>) → bool)(op1);
    let mut l = [1 : Field, 2 : Field, 3 : Field];
    #arrayIndex(l, #cast(0 : Field) : u32) : Field;
    let t = `(1 : Field, true, 3 : Field);
    t.2;
    l[#cast(1 : Field) : u32] = 4 : Field;
    (op1 as Option2<Field>)._is_some = false;
    let mut tpl = `(1 : Field, true);
    tpl.0 = 2 : Field;
}
