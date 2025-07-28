import Lampe

open Lampe

-- TODO: I'm using this file for testing, delete before I merging

nr_def fib<@N : u32>() -> Field {
    let mut a = 0 : Field;
    let mut b = 1 : Field;
    for _? in 0 : u32 .. u@N {
            let temp = a;
        a = b;
        b = #fAdd(temp, b) : Field;
        skip;
    };
    a;
}

def env := Lampe.Env.mk [fib] []

open Lampe

variable {p : Prime}

def Ref.fib : Nat → Nat
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

def Spec.fib (p) (N : U 32) : Fp p :=
  Ref.fib N.toNat

@[simp]
lemma fib_induction (i : U 32) (hhi : i < (2 ^ 32 : Nat) - 2)
    : Spec.fib p (i + 2) = Spec.fib _ (i + 1) + Spec.fib _ i := by
  simp only [Spec.fib, fib]
  repeat rw [BitVec.toNat_add]
  simp
  have h2 : i.toNat + 2 < 4294967296 := by
    have : i.toNat < 2 ^32 - 2 := by change i < (2 ^ 32 : Nat) - 2; assumption
    omega
  have h1 : i.toNat + 1 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1]
  simp [Ref.fib]

open Spec in
theorem fib_spec {N : U 32} (h : N < (2 ^ 32 : Nat) - 2) :
    STHoare p env ⟦⟧ (fib.call h![N] h![])
      fun output => output = fib p N := by
  enter_decl
  steps
  loop_inv fun i _ _ => ([a ↦ ⟨Tp.field, fib p i⟩] ⋆ [b ↦ ⟨Tp.field, fib p (i + 1)⟩])
  · change 0 ≤ N; bv_decide
  · intros i _ _
    steps
    · intros
      congr
      simp_all
    · congr
      simp_all
      rw [add_comm]
      calc fib p (i + 1) + fib p i = fib p (i + 2) := by rw [fib_induction (p := p) i (by bv_decide)]
        _ = fib p (i + (1 + 1)) := by rfl
        _ = fib p (i + 1 + 1) := by rw [BitVec.add_assoc]
  · steps
    subst_vars
    rfl

-- TODO: Make this error way better

nr_def hello<>() -> str<5> {
  "hello"
}

theorem t1 {lp}: STHoare lp env (⟦⟧)
    (hello.call h![] h![])
      fun output => (String.mk output.toList) = hello2 := by
      -- fun output => output = (hello2, by rfl) := by
  enter_decl

