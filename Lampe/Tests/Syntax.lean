import Lampe

open Lampe

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

noir_def basic_void_fn<>() -> Unit := {
  #_unit
}

noir_def basic_fn<>(x: u64) -> u64 := {
  x
}

noir_def basic_fn_call<>() -> u64 := {
  let y = (basic_fn<> as λ(u64) → u64)(3: u64);
  let z = (basic_fn<> as λ(u64) → u64)(4: u64);
  (#_uAdd returning u64)(y, z)
}

def basicFnEnv : Env := .mk [basic_fn, basic_fn_call] []

theorem basic_fn_lemma : Lampe.STHoare p basicFnEnv ⟦⟧ (basic_fn.call h![] h![x])
    fun v => v = x := by
  enter_decl
  steps
  assumption

example : Lampe.STHoare p basicFnEnv ⟦⟧ (basic_fn_call.fn.body _ h![] |>.body h![])
    fun v => v = (7 : Tp.denote p (Tp.u 64)) := by
  simp only [basic_fn_call]
  steps [basic_fn_lemma]
  simp_all; subst_vars; norm_cast

noir_def basic_muts<>(x: Field) -> Field := {
  let y = (#_ref returning & Field)(x);
  let z = (#_ref returning & Field)(x);
  z = (#_readRef returning Field)(z);
  y = (#_readRef returning Field)(z);
  (#_readRef returning Field)(y)
}

example : Lampe.STHoare p Γ ⟦⟧ (basic_muts.fn.body _ h![] |>.body h![x]) fun v => v = x := by
  simp only [basic_muts]
  steps
  simp_all

noir_def weird_eq<I: Type>(x: I, y: I) -> Unit := {
  let a = (#_fresh returning I)();
  (#_fAdd returning I)(x, y);
  (#_assert returning Unit)((#_fEq returning bool)(a, x));
  (#_assert returning Unit)((#_fEq returning bool)(a, y));
}

example {x y : Tp.denote p .field} :
  STHoare p Γ ⟦⟧ (weird_eq.fn.body _ h![.field] |>.body h![x, y]) fun _ => x = y := by
  simp only [weird_eq]
  steps
  simp_all

noir_def slice_append<I: Type>(x: Vector<I>, y: Vector<I>) → Vector<I> := {
  let self = (#_ref returning & Vector<I>)(x);
  for i in (0 : u32) .. (#_arrayLen returning u32)(y) do {
    self = (#_vectorPushBack returning Vector<I>)((#_readRef returning Vector<I>)(self), (#_vectorIndex returning I)(y, i));
  };
  (#_readRef returning Vector<I>)(self)
}

example {selfV that : Tp.denote p (.vector tp)}
  : STHoare p Γ ⟦⟧ (slice_append.fn.body _ h![tp] |>.body h![selfV, that])
    fun v => v = selfV ++ that := by
  simp only [slice_append]
  steps
  loop_inv nat (fun i _ _ => [self ↦ ⟨.vector tp, selfV ++ that.take i⟩])
  . simp_all
  · simp
  . intros i _ _
    steps
    simp
  . steps
    simp_all [Nat.mod_eq_of_lt]

noir_def simple_if<>(x: Field, y: Field) -> Field := {
  let z = (#_ref returning & Field)(x);
  if (#_fEq returning bool)(x, x) then {
    z = y;
  };
  (#_readRef returning Field)(z)
}

example : STHoare p Γ ⟦⟧ (simple_if.fn.body _ h![] |>.body h![x, y]) fun v => v = y := by
  simp only [simple_if]
  steps

  step_as ([z ↦ ⟨_, x⟩]) (fun _ => [z ↦ ⟨_, y⟩])
  . apply STHoare.ite_intro
    . intro; steps
    . intro h; cases h

  steps
  simp_all

noir_def simple_if_else<>(x: Field, y: Field) -> Field := {
  let z = if (#_fEq returning bool)(x, x) then { x } else { y };
  z
}

example : STHoare p Γ ⟦⟧ (simple_if_else.fn.body _ h![] |>.body h![x, y]) fun v => v = x := by
  simp only [simple_if_else]
  steps

  step_as (⟦⟧) (fun z => z = x)
  . apply STHoare.ite_intro
    . intro; steps; simp_all
    . intro h; cases h

  steps
  simp_all

noir_def simple_lambda<>(x: Field, y: Field) -> Field := {
  let add = fn(a: Field, b: Field): Field := (#_fAdd returning Field)(a, b);
  (add as λ(Field, Field) -> Field)(x, y);
}

example {p Γ} {x y : Tp.denote p Tp.field} :
    STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
    fun v => v = x + y := by
  simp only [simple_lambda]
  steps
  enter_lambda_as (⟦⟧) (fun v => v = x + y)
  . assumption
  steps
  assumption

noir_trait_def Bulbulize<> [] := {
  method bulbulize<>(Self) -> Field;
}

noir_trait_impl[bulbulizeField] <> Bulbulize<> for Field where [] := {
  noir_def bulbulize<>(x: Field) -> Field := {
    (#_fAdd returning Field)(x, x)
  }
}

noir_trait_impl[bulbulizeU32] <> Bulbulize<> for u32 where [] := {
  noir_def bulbulize<>(_x: u32) -> u32 := {
    69: u32
  }
}

def simpleTraitEnv : Env := {
  functions := [],
  traits := [bulbulizeField, bulbulizeU32]
}

noir_def simple_trait_call<I: Type> (x: I) -> I := {
  ((I as Bulbulize<>)::bulbulize<> as λ(I) → I)(x)
}

example {p} {arg: Tp.denote p Tp.field} :
    STHoare p simpleTraitEnv ⟦⟧ (simple_trait_call.fn.body _ h![.field] |>.body h![arg])
    fun v => v = 2 * arg := by
  simp only [simple_trait_call]
  steps
  step_as (⟦⟧) (fun v => v = 2 * arg)
  . assumption
  · resolve_trait
    steps
    subst_vars
    ring

noir_trait_impl[me] <I: Type> Me<> for I where [] := {
  noir_def me<>(x: I) -> I := {
    x
  }
}

def genericTraitEnv : Env := {
  functions := [],
  traits := [me]
}

noir_def generic_trait_call<>(x: Field) -> Field := {
  ((Field as Me<>)::me<> as λ(Field) → Field)(x)
}

example {p} {x : Tp.denote p Tp.field} :
    STHoare p genericTraitEnv ⟦⟧ (generic_trait_call.fn.body _ h![] |>.body h![x])
    fun v => v = x := by
  simp only [generic_trait_call]
  steps
  step_as (⟦⟧) (fun v => v = x)
  . assumption
  · resolve_trait
    steps
    assumption

noir_struct_def FooStruct<I: Type> {
  I,
  I
}

noir_def make_foo_struct<>(x: u32) -> FooStruct<u32> := {
  let y = (#_uMul returning u32)(x, 10: u32);
  (#_makeData returning FooStruct<u32>)(x, y)
}

noir_def make_tuple<>(x: u32) -> Tuple<u32, u32> := {
  (#_makeData returning Tuple<u32, u32>)(x, x)
}

example : STHoare p Γ ⟦⟧ (make_tuple.fn.body _ h![] |>.body h![x])
    fun v => v = (x, x, ()) := by
  simp only [make_tuple]
  steps
  subst_vars; rfl

noir_def get_second_elem<>() -> u32 := {
  let v = (make_foo_struct<> as λ(u32) → FooStruct<u32>)(10: u32);
  v.1
}

def structEnv : Env := .mk [make_foo_struct, get_second_elem] []

theorem helper_lemma :
    STHoare p structEnv ⟦⟧ (make_foo_struct.call h![] h![x])
    fun v => v = (x, (10 * x, ())) := by
  enter_decl
  steps
  subst_vars
  simp_all; simp [HList.toTuple, BitVec.mul_comm]; rfl

example :
    STHoare p structEnv ⟦⟧ (get_second_elem.call h![] h![])
    fun v => v = (100 : Tp.denote p (Tp.u 32)) := by
  enter_decl
  steps [helper_lemma]
  subst_vars
  rfl

noir_def generic_func<I: Type>(a: I) -> I := {
  a
}

noir_def call_generic_func<>(a: Field) -> Field := {
  let x = (generic_func<Field> as λ(Field) -> Field)(a);
  x
}

noir_def basic_cast<>(x: u8) -> Field := {
  (#_cast returning Field)(x)
}

example {p} {x : Tp.denote p $ .u 8} :
    STHoare p Γ ⟦⟧ (basic_cast.fn.body _ h![] |>.body h![x])
    fun (v : Tp.denote p .field) => v = x.toNat := by
  simp only [basic_cast]
  steps
  aesop

noir_def add_two_fields<>(a: Field, b: Field) -> Field := {
  (#_fAdd returning Field)(a, b)
}

noir_def call_decl<>() -> Field := {
  (add_two_fields<> as λ(Field, Field) → Field)(1: Field, 2: Field)
}

example : STHoare p ⟨[add_two_fields], []⟩ ⟦⟧
    (call_decl.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [call_decl]
  steps
  step_as (⟦⟧) (fun (v : Fp p) => v = 3)
  . assumption
  · enter_decl
    simp only [add_two_fields]
    steps
    subst_vars
    ring

noir_def simple_tuple<>() -> Field := {
  let t = (#_makeData returning Tuple<Field, bool, Field>)(1: Field, #_true, 3: Field);
  t.2
}

example : STHoare p Γ ⟦⟧ (simple_tuple.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [simple_tuple]
  steps
  aesop

noir_def simple_slice<>() -> bool := {
  let s = (#_mkVector returning Vector<bool>)(#_true, #_false);
  (#_vectorIndex returning bool)(s, (1: u32))
}

example : STHoare p Γ ⟦⟧ (simple_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .bool) => v = false :=   by
  simp only [simple_slice]
  steps
  simp_all

noir_def simple_array<>() -> Field := {
  let arr = (#_mkArray returning Array<Field, 2: u32>)(1: Field, 2: Field);
  (#_arrayIndex returning Field)(arr, 1: u32)
}

example : STHoare p Γ ⟦⟧ (simple_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 2 := by
  simp only [simple_array]
  steps
  casesm* _ = _
  simp_all; aesop

noir_def use_array<>() -> Field := {
  let a = (#_mkRepeatedArray returning Array<Field, 4: u32>)((1: Field));
  (#_arrayIndex returning Field)(a, ((2: u32)))
}

example : STHoare p Γ ⟦⟧ (use_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p Tp.field) => v = 1 := by
  simp only [use_array]
  steps
  simp_all; subst_vars; rfl

-- Note that repeated slices are not currently supported in the extractor
noir_def repeated_slice<>() -> Field := {
  let a = (#_mkRepeatedVector returning Vector<Field>)((4: u32), (1: Field));
  (#_vectorIndex returning Field)(a, (0: u32))
}

example : STHoare p Γ ⟦⟧ (repeated_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p Tp.field) => v = 1 := by
  simp only [repeated_slice]
  steps
  simp_all

noir_def simple_tuple_access<>() → Field := {
  let t =
    (#_makeData returning Tuple<Field, bool, Field>)(1: Field, #_true, 3: Field);
  t.2
}

example : STHoare p Γ ⟦⟧ (simple_tuple_access.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [simple_tuple_access]
  steps
  aesop

noir_def simple_slice_of_values<>() → bool := {
  let s = (#_mkVector returning Vector<bool>)(#_true, #_false);
  (#_vectorIndex returning bool)(s, 1: u32)
}

example : STHoare p Γ ⟦⟧ (simple_slice_of_values.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .bool) => v = false := by
  simp only [simple_slice_of_values]
  steps
  aesop

noir_def tuple_lens<>() → Field := {
  let p = (#_ref returning & Tuple<Tuple<Field, Field>, Field>)(
    (#_makeData returning Tuple<Tuple<Field, Field>, Field>)(
      (#_makeData returning Tuple<Field, Field>)(1: Field, 2: Field),
      3: Field
    )
  );

  (p.1: Field) = 5: Field;
  ((p.0: Tuple<Field, Field>).1: Field) = 10: Field;

  let p_val = (#_readRef returning Tuple<Tuple<Field, Field>, Field>)(p);
  (p_val.0).1
}

example : STHoare p Γ ⟦⟧ (tuple_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 10 := by
  simp only [tuple_lens]
  steps
  subst_vars
  rfl

noir_struct_def Pair<E: Type> {
  E,
  E
}

noir_def struct_lens<>() → Field := {
  let p = (#_ref returning & Tuple<Pair<Field>, Field>)(
    (#_makeData returning Tuple<Pair<Field>, Field>)(
      (#_makeData returning Pair<Field>)(1: Field, 2: Field),
      3: Field
    )
  );

  ((p.0: Pair<Field>).1: Field) = 20: Field;

  let p_val = (#_readRef returning Tuple<Pair<Field>, Field>)(p);
  (p_val.0).1
}

example : STHoare p Γ ⟦⟧ (struct_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 20 := by
  simp only [struct_lens]
  steps
  subst_vars
  rfl

noir_def array_lens<>() → Field := {
  let a = (#_ref returning & Tuple<Array<Field, 2: u32>, Field>)(
    (#_makeData returning Tuple<Array<Field, 2: u32>, Field>)(
      (#_mkArray returning Array<Field, 2: u32>)(1: Field, 2: Field),
      3: Field
    )
  );

  ((a.0: Array<Field, 2: u32>)[1: u32]: Field) = 30: Field;

  let a_val = (#_readRef returning Tuple<Array<Field, 2: u32>, Field>)(a);
  (#_arrayIndex returning Field)(a_val.0, 1: u32)
}

example : STHoare p Γ ⟦⟧ (array_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 30 := by
  simp only [array_lens]
  steps
  aesop

noir_def slice_lens<>() → Field := {
  let a = (#_ref returning & Tuple<Vector<Field>, Field>)(
    (#_makeData returning Tuple<Vector<Field>, Field>)(
      (#_mkVector returning Vector<Field>)(1: Field, 2: Field),
      3: Field
    )
  );

  ((a.0: Vector<Field>)[[1: u32]]: Field) = 40: Field;

  let a_val = (#_readRef returning Tuple<Vector<Field>, Field>)(a);
  (#_vectorIndex returning Field)(a_val.0, 1: u32)
}

example : STHoare p Γ ⟦⟧ (slice_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 40 := by
  simp only [slice_lens]
  steps
  aesop

noir_def deref_lens<>() → Field := {
  let r = (#_ref returning &Tuple<Field>)((#_makeData returning Tuple<Field>)(5: Field));

  ((*r: Tuple<Field>).0: Field) = 10: Field;

  (#_readRef returning Tuple<Field>)(r).0
}

example : STHoare p Γ ⟦⟧ (deref_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 10 := by
  simp only [deref_lens]
  steps
  subst_vars
  rfl

noir_def return_ten<>() → Field := {
  10: Field
}

noir_def call_free_func<>() → Field := {
  (return_ten<> as λ() → Field)()
}

noir_def call_function<>(f: λ() → Field) → Field := {
  (f as λ() → Field)()
}

noir_def simple_hof<>() → Field := {
  let func = (return_ten<> as λ() → Field);

  (call_function<> as λ(λ() → Field) → Field)(func)
}


example : STHoare p ⟨[return_ten, call_function], []⟩ ⟦⟧ (simple_hof.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 10 := by
  simp only [simple_hof]
  steps
  subst_vars
  step_as (⟦⟧) (fun v : Fp p => v = 10)
  . assumption
  . enter_decl
    simp only [call_function]

    step_as (⟦⟧) (fun (v : Fp p) => v = 10)
    . assumption
    . enter_decl
      steps
      assumption

noir_def create_arr<N: u32>() → Array<Field, N: u32> := {
  (#_mkRepeatedArray returning Array<Field, N: u32>)(1: Field)
}

def createArrEnv : Env := ⟨[create_arr], []⟩

lemma List.Vector.replicate_to_list : (List.Vector.replicate N e).toList = List.replicate N e := by
  simp only [List.Vector.replicate]
  rfl

example : STHoare p createArrEnv ⟦⟧ (create_arr.call h![N] h![])
    fun v => v.toList = List.replicate N.toNat (1 : Tp.denote p .field) := by
  enter_decl
  steps
  subst_vars
  rfl

noir_type_alias Arr<T: Type, N: u32> := Array<T, N: u32>;

noir_def alias_test<>(arr: @Arr<Field, 3: u32>) → Field := {
  (#_arrayIndex returning Field)(arr, 1: u32)
}

def aliasTestEnv : Env := ⟨[alias_test], []⟩

example : STHoare p aliasTestEnv ⟦⟧ (alias_test.call h![] h![⟨[1, 2, 3], by tauto⟩])
    fun (v : Tp.denote p .field) => v = 2 := by
  enter_decl
  steps
  aesop

noir_def const_test<N: u8>(x: Field) → Field := {
  let res = (#_ref returning & Field)(x);

  for _ in (0: u8) .. uConst!(N: u8) do {
    res = (#_fMul returning Field)((#_readRef returning Field)(res), 2: Field);
  };

  (#_readRef returning Field)(res)
}

def constTestEnv : Env := ⟨[const_test], []⟩

example : STHoare p constTestEnv ⟦⟧ (const_test.call h![3] h![2])
    fun (v : Tp.denote p .field) => v = 16 := by
  enter_decl
  steps

  loop_inv nat (fun i _ _ => [res ↦ ⟨.field, 2^i * 2⟩])
  . simp
  . simp_all
  . intros i hlo hhi
    steps
  . steps
    simp_all
    norm_num

noir_def tuple_pattern<>(x: Field) → Field := {
  let (x, y) = (#_makeData returning Tuple<Field, Field>)(x, x);
  let x = (#_ref returning & Field)(x);
  x = y;
  (#_readRef returning Field)(x)
}

def tuplePatternEnv : Env := ⟨[tuple_pattern], []⟩

example : STHoare p tuplePatternEnv ⟦⟧ (tuple_pattern.call h![] h![x])
    fun (v : Tp.denote p .field) => v = x := by
  enter_decl
  steps
  subst_vars
  apply_assumption

noir_def test_lam<>(x: Field) -> Field := {
  let f = fn(x: Field): Field := x;
  (f as λ(Field) → Field)(x)
}

def testLamEnv : Env := ⟨[test_lam], []⟩

example : STHoare p testLamEnv ⟦⟧ (test_lam.call h![] h![x])
    fun (v : Tp.denote p .field) => v = x := by
  enter_decl
  steps
  enter_lambda_as (⟦⟧) (fun v => v = x)
  · assumption
  steps
  simp_all

noir_def has::colons<>(x: Field) -> Field := {
  x
}

noir_def has::colons::two<>(x: Field) -> Field := {
  (has::colons<> as λ(Field) → Field)(x)
}

def hasColonsEnv : Env := .mk [«has::colons», «has::colons::two»] []

example : STHoare p hasColonsEnv ⟦⟧ («has::colons::two».call h![] h![x]) fun v => v = x := by
  enter_decl
  steps
  step_as (⟦⟧) (fun v => v = x)
  . assumption
  · enter_decl
    steps
    assumption

noir_type_alias FField<> := Field;

noir_struct_def «asdf::Other»<> {
  @FField<>,
}

noir_def «asdf::colon_test»<>() -> Field := {
  let a = (5: Field);
  let b = (10: Field);
  (#_fAdd returning Field)(a, b)
}

noir_def «asdf::inner::colon_test_inner»<>() -> @FField<> := {
  let a = (5: Field);
  let b = (10: Field);
  let c = (#_makeData returning «asdf::Other»<>)((#_fAdd returning Field)(a, b));
  c.0
}

noir_def test_blocks<>() -> u32 := {
  let s = (2: Field);
  let x = {
    let y = (9: Field);
    (2: u32)
  };
  (3: u32)
}

noir_def deref_tuple<>(self: & Tuple<Field, Field>) -> Unit := {
  ((*self: Tuple<Field, Field>).0: Field) = 1: Field;
  #_skip
}

noir_def unused_arg<>(_x: Field) -> Unit := {
  #_unit
}

noir_def generic_fconst<N: Field>() -> Vector<Field> := {
  (#_mkRepeatedVector returning Vector<Field>)(0: Field, fConst!(N: Field))
}

noir_def generic_uconst<N: u32>() -> Vector<Field> := {
  (#_mkRepeatedVector returning Vector<Field>)(0: Field, uConst!(N: u32))
}

noir_struct_def has::«from»::name::«meta»<> {
  Field
}

noir_def make::has::«from»::name::«meta»<>(x: Field) -> has::«from»::name::«meta»<> := {
  (#_makeData returning has::«from»::name::«meta»<>)(x)
}

noir_def call::make::has::«from»::name::«meta»<>(x : Field) -> Field := {
  ((make::has::«from»::name::«meta»<> as λ(Field) → has::«from»::name::«meta»<>)(x)).0
}

def badNameEnv : Env := .mk [«make::has::from::name::meta», «call::make::has::from::name::meta»] []

example : STHoare p badNameEnv ⟦⟧ («make::has::from::name::meta».call h![] h![x]) fun v => v = (x,()) := by
  enter_decl
  steps
  assumption

example : STHoare p badNameEnv ⟦⟧ («call::make::has::from::name::meta».call h![] h![x]) fun v => v = x := by
  enter_decl
  steps
  step_as (⟦⟧) (fun v => v = (x, ()))
  · enter_decl
    steps
    assumption
  steps
  subst_vars
  rfl

noir_def returns_string<>() → String<5: u32> := {
  "hello"
}

def returnsStringEnv : Env := ⟨[returns_string], []⟩

theorem returns_string_correct {p}
  : STHoare p returnsStringEnv ⟦⟧
    (returns_string.call h![] h![])
    (fun v => v = NoirStr.of "hello") := by
  enter_decl
  steps
  subst_vars
  rfl

-- Tests for explicit ref/readRef patterns (previously used auto-deref).
noir_def increment_ref<>(r: & Field) -> Unit := {
  (*r: Field) = (#_fAdd returning Field)((#_readRef returning Field)(r), (1: Field));
  #_skip
}

-- Pass acc (already a ref) directly to increment_ref.
noir_def mut_ref_loop<>() -> Field := {
  let acc = (#_ref returning & Field)((0: Field));
  for _ in (0: u32) .. (3: u32) do {
    (increment_ref<> as λ(& Field) -> Unit)(acc);
  };
  (#_readRef returning Field)(acc)
}

-- Same as mut_ref_loop (variants collapsed now that auto-deref is removed).
noir_def mut_ref_loop_parens<>() -> Field := {
  let acc = (#_ref returning & Field)((0: Field));
  for _ in (0: u32) .. (3: u32) do {
    (increment_ref<> as λ(& Field) -> Unit)(acc);
  };
  (#_readRef returning Field)(acc)
}

-- Same as mut_ref_loop.
noir_def mut_ref_loop_block<>() -> Field := {
  let acc = (#_ref returning & Field)((0: Field));
  for _ in (0: u32) .. (3: u32) do {
    (increment_ref<> as λ(& Field) -> Unit)(acc);
  };
  (#_readRef returning Field)(acc)
}

-- Same as mut_ref_loop.
noir_def mut_ref_loop_nested<>() -> Field := {
  let acc = (#_ref returning & Field)((0: Field));
  for _ in (0: u32) .. (3: u32) do {
    (increment_ref<> as λ(& Field) -> Unit)(acc);
  };
  (#_readRef returning Field)(acc)
}

-- Direct pass of ref to increment_ref (chain collapse is no longer relevant).
noir_def mut_ref_chain<>() -> Field := {
  let acc = (#_ref returning & Field)((0: Field));
  (increment_ref<> as λ(& Field) -> Unit)(acc);
  (#_readRef returning Field)(acc)
}

-- Aliasing: r = x (same ref), increment through r modifies x.
noir_def mut_ref_chain_non_autoderef<>() -> Field := {
  let x = (#_ref returning & Field)((0: Field));
  let r = x;
  (increment_ref<> as λ(& Field) -> Unit)(r);
  (#_readRef returning Field)(x)
}

-- Same as above with non-zero initial value (x goes from 7 to 8).
noir_def chain_mutate_copy_smoke<>() -> Field := {
  let x = (#_ref returning & Field)((7: Field));
  let r = x;
  (increment_ref<> as λ(& Field) -> Unit)(r);
  (#_readRef returning Field)(x)
}

-- r2 is a copy of r's value. v is a ref to a copy of r2's value.
-- Returns value at v (= original value at r).
noir_def chain_from_explicit_readref<>(r: & Field) -> Field := {
  let r2 = (#_ref returning & Field)((#_readRef returning Field)(r));
  let v = (#_ref returning & Field)((#_readRef returning Field)(r2));
  (#_readRef returning Field)(v)
}

-- Smoke: x=5, call chain_from_explicit_readref with x (already a ref), result should be 5.
noir_def chain_from_explicit_readref_smoke<>() -> Field := {
  let x = (#_ref returning & Field)((5: Field));
  (chain_from_explicit_readref<> as λ(& Field) -> Field)(x)
}

def mutRefLoopEnv : Env :=
  ⟨[
    increment_ref,
    mut_ref_loop,
    mut_ref_loop_parens,
    mut_ref_loop_block,
    mut_ref_loop_nested,
    mut_ref_chain,
    mut_ref_chain_non_autoderef,
    chain_mutate_copy_smoke,
    chain_from_explicit_readref,
    chain_from_explicit_readref_smoke
  ], []⟩

theorem increment_ref_spec {r : Ref} {v : Fp p} :
    STHoare p mutRefLoopEnv
    [r ↦ ⟨.field, v⟩]
    (increment_ref.call h![] h![r])
    (fun _ => [r ↦ ⟨.field, v + 1⟩]) := by
  enter_decl
  steps

theorem mut_ref_loop_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_loop.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 3) := by
  enter_decl
  steps
  loop_inv nat (fun i _ _ => [acc ↦ ⟨.field, (i : Fp p)⟩])
  · simp
  · intros i _ _
    steps [increment_ref_spec]
    push_cast
    ring_nf
  · steps
    simp_all

theorem mut_ref_loop_parens_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_loop_parens.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 3) := by
  enter_decl
  steps
  loop_inv nat (fun i _ _ => [acc ↦ ⟨.field, (i : Fp p)⟩])
  · simp
  · intros i _ _
    steps [increment_ref_spec]
    push_cast
    ring_nf
  · steps
    simp_all

theorem mut_ref_loop_block_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_loop_block.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 3) := by
  enter_decl
  steps
  loop_inv nat (fun i _ _ => [acc ↦ ⟨.field, (i : Fp p)⟩])
  · simp
  · intros i _ _
    steps [increment_ref_spec]
    push_cast
    ring_nf
  · steps
    simp_all

theorem mut_ref_loop_nested_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_loop_nested.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 3) := by
  enter_decl
  steps
  loop_inv nat (fun i _ _ => [acc ↦ ⟨.field, (i : Fp p)⟩])
  · simp
  · intros i _ _
    steps [increment_ref_spec]
    push_cast
    ring_nf
  · steps
    simp_all

theorem mut_ref_chain_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_chain.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 1) := by
  enter_decl
  steps [increment_ref_spec]
  simp_all

theorem mut_ref_chain_non_autoderef_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (mut_ref_chain_non_autoderef.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 1) := by
  enter_decl
  steps
  subst_vars
  steps [increment_ref_spec]
  simp_all

-- Same propagation with a non-zero initial value (x: 7 → 8).
theorem chain_mutate_copy_smoke_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (chain_mutate_copy_smoke.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 8) := by
  enter_decl
  steps
  subst_vars
  steps [increment_ref_spec]
  simp_all
  ring

-- chain_from_explicit_readref: reading through two ref copies preserves the original value.
lemma chain_from_explicit_readref_spec {r : Tp.denote p Tp.field.ref} {val : Fp p}
  : STHoare p mutRefLoopEnv [r ↦ ⟨.field, val⟩]
    (chain_from_explicit_readref.call h![] h![r])
    (fun result => result = val) := by
  enter_decl
  steps
  simp_all

-- Smoke: x=5 passed as &x, chain_from_explicit_readref reads through the ref chain,
-- result is 5 (x unchanged).
theorem chain_from_explicit_readref_smoke_correct
  : STHoare p mutRefLoopEnv ⟦⟧
    (chain_from_explicit_readref_smoke.call h![] h![])
    (fun (v : Tp.denote p .field) => v = 5) := by
  enter_decl
  steps
  steps [chain_from_explicit_readref_spec]
  simp_all

noir_def integer_shifts<>(a: i32, b: i32) -> i32 := {
  let x = (#_iShl returning i32)(a, b);
  let y = (#_iShr returning i32)(a, b);
  (#_iSub returning i32)(a, b)
}

def integerShiftsEnv : Env := ⟨[integer_shifts], []⟩

theorem integer_shifts_correct {p a b}
  : STHoare p integerShiftsEnv ⟦⟧
    (integer_shifts.call h![] h![a, b])
    (fun r => r = a - b) := by
  enter_decl
  steps
  simp_all

