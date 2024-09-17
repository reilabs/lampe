-- This module serves as the root of the `Lampe` library.
-- Import modules here that should be built as part of the library.
import «Lampe».Basic
-- import Lampe.Hoare
import Lean.Meta.Tactic.Simp.Main

open Lampe

variable (P : Prime)

nr_def weirdEq<I>(x : I, y : I) -> Unit {
  let a = #fresh() : I;
  #assert(#eq(a, x) : bool) : Unit;
  #assert(#eq(a, y) : bool) : Unit;
}

nr_def recursiveMul<>(n: u64, k: u64) -> u64 {
  if #eq(n, (0:u64)):bool (0:u64)
  else {
    let n = #sub(n, (1:u64)) : u64;
    #add(k, recursiveMul<>(n, k) : u64):u64
  }
}

def testMod : Lampe.Module := ⟨[weirdEq, recursiveMul]⟩

open Lampe

theorem assignable_weirdEq_field_iff:
  Assignable Γ st (weirdEq.fn.body _ h![.field] h![a, b]) Q ↔
  a = b ∧ Q st () := by
  noir_simp [weirdEq]

-- theorem weirdEq_u_hoare { Q : State P → Tp.denote P .unit → Prop}:
    -- Hoare.Call Γ (tps := [.u s, .u s]) (fun st h![a, b] => a == b ∧ Q st .unit) (weirdEq.fn.body _ h![.u s]) Q := by




theorem Fin.castSucc_val : Fin.val (Fin.castSucc a) = a := by
  rfl

theorem Fin.succ_val : Fin.val (Fin.succ a) = a.val + 1 := by
  rfl

theorem assignableRecursiveMul:
    Assignable (P := P) (Lampe.Env.ofModule testMod) st (recursiveMul.fn.body _ h![] h![a, b]) Q ↔
    (a.val * b.val < 2 ^ 64) ∧ Q st (a * b) := by
  induction a using Fin.induction generalizing Q with
  | zero => noir_simp [recursiveMul]
  | succ a ih =>
      simp only [recursiveMul]
      have : a.succ - Nat.cast 1 = a.castSucc := by
        cases a
        conv => lhs; whnf
        conv => rhs; whnf
        simp_arith
        linarith
      noir_simp only [this, ih, Fin.mul_def, Fin.add_def, Fin.castSucc_val, Fin.succ_val]
      simp_arith [Nat.add_mul, Nat.add_comm]
      apply Iff.intro
      · intro_cases
        apply And.intro <;> try assumption
        rename _ + _ * _ % _ ≤ _ => h
        rw [Nat.mod_eq_of_lt] at h <;> linarith
      · intro_cases
        apply And.intro (by linarith)
        apply And.intro
        · rw [Nat.mod_eq_of_lt] <;> linarith
        · assumption


@[reducible]
def «std::Option» : Struct :=
{
  name := "std::Option"
  tyArgKinds := [.type]
  fieldTypes := fun h![T] => [.bool, T]
}

nr_def std::Option::some<T>(x : T) -> std::Option <T> {
  std::Option <T> { true, x }
}

nr_def std::Option::unwrap<T>(opt : std::Option <T>) -> T {
  #assert(opt.0) : Unit;
  opt.1
}

#print «std::Option::some»

@[reducible]
def mod := Env.ofModule ⟨[«std::Option::some», «std::Option::unwrap»]⟩

theorem unwrap_some {st : State P} {T e Q}:
    Assignable mod st expr![
      std::Option::unwrap<T>(std::Option::some<T>(${e}) : std::Option<T>) : T
    ] Q
    ↔ Assignable mod st e Q := by
  noir_simp [«std::Option::unwrap», «std::Option::some»]

def «std::U128» : Struct :=
{
  name := "std::U128"
  tyArgKinds := []
  fieldTypes := fun _ => [.field, .field]
}

variable (pLarge : P.natVal > 2 ^ 128)

def fromU128 (x : U 128) : («std::U128».tp h![]).denote P :=
  (⟨x.val % 2 ^ 64, by apply Nat.lt_trans; apply Nat.mod_lt; decide; apply Nat.lt_trans ?_ pLarge; decide⟩,
  (⟨x.val / 2 ^ 64, by apply Nat.div_lt_of_lt_mul; simp only [Prime.natVal] at pLarge; linarith [x.prop]⟩,
  ()))

nr_def std::U128::from_u64s_le<>(lo: u64, hi: u64) -> std::U128<> {
  #assert(#lt((128 : u32), #cast(#modulus_num_bits():u64):u32):bool):Unit;
  std::U128<> { #cast(lo):Field, #cast(hi):Field }
}

nr_def std::U128::add<>(self : std::U128<>, b : std::U128<>) -> std::U128<> {
  let low = #add(self.0, b.0):Field;
  let lo = #cast(#cast(low):u64):Field;
  let carry = #div(#sub(low, lo):Field, 18446744073709551616:Field):Field;
  let high = #add(#add(self.1, b.1):Field, carry):Field;
  let hi = #cast(#cast(high):u64):Field;
  std::U128<> { lo, hi }
}

theorem «std::U128::add».correct :
    Assignable (P:=P) Γ st («std::U128::add».fn.body _ h![] h![fromU128 P pLarge a, fromU128 P pLarge b]) Q ↔
    Q st (fromU128 P pLarge $ a + b) := by
  rcases a with ⟨a, pa⟩; rcases b with ⟨b, pb⟩;
  noir_simp [«std::U128::add», getProj, fromU128]
  apply Iff.of_eq
  sorry

nr_def lt_fallback<>(x: Field, y: Field) -> bool {
  let num_bytes = #div(#add(#cast(#modulus_num_bits():u64):u32, 7:u32):u32, 8:u32):u32;
  let x_bytes = #to_le_bytes(x, num_bytes):[u8];
  let y_bytes = #to_le_bytes(y, num_bytes):[u8];
  let mut x_is_lt = false;
  let mut done = false;
  for i in 0:u32 .. num_bytes {
    if #not(done):bool {
      let x_byte = #index(x_bytes, #sub(#sub(num_bytes, 1:u32):u32, i):u32):u8;
      let y_byte = #index(y_bytes, #sub(#sub(num_bytes, 1:u32):u32, i):u32):u8;
      let bytes_match = #eq(x_byte, y_byte):bool;
      if #not(bytes_match):bool {
        x_is_lt = #lt(x_byte, y_byte):bool;
        done = true;
      }
    }
  };
  x_is_lt
}

def lt_mod : Lampe.Module := ⟨[lt_fallback]⟩

abbrev seventeen : Lampe.Prime := ⟨16, by decide⟩

lemma Lampe.State.allocs_nextRef {st : State P} : (st.allocs P as).nextRef = st.nextRef.forward as.length := by
  simp [allocs, Ref.forward, nextRef]

-- set_option trace.Meta.Tactic.simp.discharge true

lemma State.get_set_of_ne (h : r' ≠ r) (hn : State.get? P st r' = some res) :
    (State.set P st r tp v).get? P r' = some res := by
  cases r; cases r'
  simp_all [State.get?, State.set, State.get]

lemma State.get_set_of_eq (h : r.val < st.size):
    (State.set P st r tp v).get? P r = some ⟨tp, v⟩ := by
  simp [State.get?, State.get, State.set, h]

example : Assignable (P := seventeen) (Env.ofModule lt_mod) st expr![
    #assert(lt_fallback<>(1:Field, 2:Field):bool):Unit
  ] fun _ _ => True := by
  have : numBits seventeen.natVal = 5 := by rfl
  noir_simp only [lt_fallback, this]
  exists [1]
  noir_simp only
  exists [2]
  noir_simp only
  rw [Assignable.readRef_iff ?mem]
  case mem =>
    simp only [
      State.allocs_nextRef,
      List.length_cons,
      List.length_nil,
      State.allocs_get?_forward,
      Ref.forward_zero,
      State.allocs_get?_nextRef
    ]
    rfl
  noir_simp only
  rw [Assignable.readRef_iff ?mem]
  case mem =>
    simp only [
      State.allocs_nextRef,
      List.length_cons,
      List.length_nil,
      Nat.add_one,
    ]
    apply State.get_set_of_ne
    · simp [Ref.forward, State.nextRef] -- todo direct strat
    · apply State.get_set_of_eq
      simp -- todo direct
  tauto

#print lt_fallback
