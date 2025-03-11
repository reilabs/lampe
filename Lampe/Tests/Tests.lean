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

example {x y : Tp.denote p .field} :
  STHoare p Γ ⟦⟧ (weirdEq.fn.body _ h![.field] |>.body h![x, y]) fun _ => x = y := by
  simp only [weirdEq]
  steps
  simp_all

nr_def sliceAppend<I>(x: [I], y: [I]) -> [I] {
  let mut self = x;
  for i in (0 : u32) .. #sliceLen(y) : u32 {
    self = #slicePushBack(self, #sliceIndex(y, i) : I) : [I]
  };
  self
}

lemma BitVec.add_toNat_of_lt_max {a b : BitVec w} (h: a.toNat + b.toNat < 2^w) :
    (a + b).toNat = a.toNat + b.toNat := by
  simp only [BitVec.add_def, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  assumption

lemma BitVec.ofNat_ge_zero {n : Nat} (a : Nat) : 0 ≤ BitVec.ofNat n a := by
  simp only [ofNat_eq_ofNat, ofNat_le_ofNat, Nat.zero_mod, zero_le]

lemma BitVec.toNat_zero {n : Nat} : BitVec.toNat (n := n) (0 : Int) = 0 := by
  change BitVec.toNat 0 = 0
  simp

example {selfV that : Tp.denote p (.slice tp)} :
    STHoare p Γ ⟦⟧ (sliceAppend.fn.body _ h![tp] |>.body h![selfV, that])
    fun v => v = selfV ++ that := by
  simp only [sliceAppend]
  steps
  loop_inv (fun i _ _ => [self ↦ ⟨.slice tp, selfV ++ that.take i.toNat⟩])
  · simp_all ; apply BitVec.ofNat_ge_zero
  · simp_all [BitVec.toNat_zero]
  · intros i _ _
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      apply BitVec.add_toNat_of_lt_max
      casesm* (Tp.denote p (.u 32)), (U _), Fin _
      simp at *
      linarith
    simp only [this, List.take_succ]
    aesop

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

  steps

  enter_block_as ([z ↦ ⟨_, x⟩]) (fun _ => [z ↦ ⟨_, y⟩])
  · apply STHoare.ite_intro
    · intro; steps
    · intro h; cases h

  steps
  simp_all

nr_def simple_if_else<>(x : Field, y : Field) -> Field {
  let z = if #fEq(x, x) : bool { x } else { y };
  z
}

example {p Γ x y} : STHoare p Γ ⟦⟧ (simple_if_else.fn.body _ h![] |>.body h![x, y])
    fun v => v = x := by
  simp only [simple_if_else]
  steps

  enter_block_as (⟦⟧) (fun z => z = x)
  · apply STHoare.ite_intro
    · intro; steps; simp_all
    · intro h; cases h

  steps
  simp_all

nr_def simple_lambda<>(x : Field, y : Field) -> Field {
  let add = |a : Field, b : Field| -> Field { #fAdd(a, b) : Field };
  add(x, y);
}

example {p Γ} {x y : Tp.denote p Tp.field} :
    STHoare p Γ ⟦⟧ (simple_lambda.fn.body _ h![] |>.body h![x, y])
    fun v => v = x + y := by
  simp only [simple_lambda]
  steps

  apply STHoare.letIn_intro (Q := fun v => v = x + y)
  . apply STHoare.ramified_frame_top (H₁ := (∃∃h, [λadd.asLambda h ↦ _]) ⋆ ⟦⟧) (Q₁ := fun v => (∃∃h, [λadd.asLambda h ↦ _]) ⋆ v = x + y)
    apply STHoare.callLambda_intro
    case h_ent =>
      sl_norm
      rw [←SLP.exists_star]
      apply SLP.exists_intro_l
      intro hp
      apply SLP.exists_intro_r
      rw [SLP.star_comm]
      apply SLP.star_mono_l'
      apply SLP.forall_right
      intro
      apply SLP.wand_intro
      sl_norm
      apply SLP.star_mono_l
      apply SLP.entails_top
    steps
    assumption
  · intro
    steps
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

  enter_block_as (⟦⟧) (fun v => v = 2 * arg)
  · enter_trait [] simpleTraitEnv
    steps
    subst_vars
    ring

  steps
  simp_all


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
  enter_block_as (⟦⟧) (fun v => v = x)
  · enter_trait [Tp.field] genericTraitEnv
    steps
    assumption

  steps
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
  simp_all

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

example : STHoare p ⟨[add_two_fields], []⟩ ⟦⟧
    (call_decl.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [call_decl]
  steps
  enter_block_as (⟦⟧) (fun v => v = 3)
  · enter_decl
    simp only [add_two_fields]
    steps
    subst_vars
    ring

  steps
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
  simp only [simple_slice]
  steps
  aesop

nr_def simple_array<>() -> Field {
  let arr = [1 : Field, 2 : Field];
  arr[1 : u32]
}

example : STHoare p Γ ⟦⟧ (simple_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 2 := by
  simp only [simple_array]
  steps
  casesm* _ = _
  rfl

nr_def simple_rep_array<>() -> [Field; 4] {
  let arr = [1 : Field ; 4];
  arr
}

example : STHoare p Γ ⟦⟧ (simple_rep_array.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p $ .array _ _) => v.toList = [1, 1, 1, 1] := by
  simp only [simple_rep_array, Expr.mkArray]
  steps
  aesop

nr_def simple_rep_slice<>() -> [Field] {
  let arr = &[1 : Field ; 4];
  arr
}

example : STHoare p Γ ⟦⟧ (simple_rep_slice.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p $ .slice _) => v = [1, 1, 1, 1] := by
  simp only [simple_rep_slice, Expr.mkArray]
  steps
  subst_vars
  rfl

nr_def tuple_lens<>() -> Field {
  let mut p = `(`(1 : Field, 2 : Field), 3 : Field);
  p .0 .1 = 3 : Field;
  p .0 .1
}

example : STHoare p Γ ⟦⟧ (tuple_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [tuple_lens]
  steps
  casesm* _ = _
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
  aesop

nr_def slice_lens<>() -> Field {
  let mut p = `(&[1 : Field, 2 : Field], 3 : Field);
  p .0 [[1 : u32]] = 3 : Field;
  p .0 [[1 : u32]]
}

@[simp]
lemma BitVec.toNat_one {n : Nat} {h : n > 0} : BitVec.toNat (n := n) (1 : Int) = 1 := by
  change BitVec.toNat 1 = 1
  simp [h]

example : STHoare p Γ ⟦⟧ (slice_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [slice_lens]
  steps
  casesm* _ = _
  rfl

nr_def simple_func<>() -> Field {
  10 : Field
}

nr_def deref_lens<>() -> Field {
  let r = #ref(`(5 : Field)) : &`(Field);
  *(r).0 = 3 : Field;
  *(r).0
}

example : STHoare p Γ ⟦⟧ (deref_lens.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 3 := by
  simp only [deref_lens]
  steps
  simp_all

nr_def call<>(f : λ() → Field) -> Field {
  f()
}

nr_def simple_hof<>() -> Field {
  let func = @simple_func<> as λ() → Field;
  (@call<> as λ(λ() → Field) → Field)(func)
}

example : STHoare p ⟨[simple_func, call], []⟩ ⟦⟧
    (simple_hof.fn.body _ h![] |>.body h![])
    fun (v : Tp.denote p .field) => v = 10 := by
  simp only [simple_hof]
  steps
  apply pluck_final_pure_destructively
  rintro rfl

  enter_block_as (⟦⟧) (fun v => v = 10)
  · enter_decl
    simp only [call]
    enter_block_as (⟦⟧) (fun v => v = 10)
    · enter_decl
      simp only [simple_func]
      steps
      assumption
    steps
    simp_all

  steps
  simp_all

nr_def fmtstr_test<>() -> Field {
  let y = 3 : Field;
  let _x = #format("y: {}", y);
  y
}

nr_def create_arr<@N : 32>() -> [Field; N] {
  [1 : Field ; N]
}

example : STHoare p Γ ⟦⟧ (create_arr.fn.body _ h![3] |>.body h![])
    fun (v : Tp.denote p $ .array .field 3) => v.toList = [1, 1, 1] := by
  simp only [create_arr]
  steps
  aesop

nr_type_alias Array<T, @N : 32> = [T; N]

nr_def alias_test<>(x : @Array<Field, 3 : 32>) -> Field {
  x[1 : u32]
}

example : STHoare p Γ ⟦⟧ (alias_test.fn.body _ h![] |>.body h![⟨[1, 2, 3], by tauto⟩])
    fun (v : Tp.denote p .field) => v = 2 := by
  simp only [alias_test]
  steps
  aesop

nr_def const_test<@N : 8>(x : Field) -> Field {
  let mut res = x;
  for _? in 0 : u8 .. @N {
    res = #fMul(res, 2 : Field) : Field;
  };
  res;
}

example : STHoare p Γ ⟦⟧ (const_test.fn.body _ h![3] |>.body h![1])
    fun (v : Tp.denote p .field) => v = 8 := by
  simp only [const_test]
  steps
  loop_inv (fun i _ _ => [res ↦ ⟨.field, 2^(i.toNat) * 1⟩])
  · simp [Int.cast, IntCast.intCast]
  · congr
    simp_all only [BitVec.ofNat_eq_ofNat, mul_one]
    rfl
  . intros i _ _
    steps
    congr
    simp_all
    have : i.toNat < 3 := by tauto
    have : (i.toNat + 1) % 256 = i.toNat + 1 := by
      apply Nat.mod_eq_of_lt
      linarith
    rw [this]
    rfl
  steps
  subst_vars
  simp
  ring
