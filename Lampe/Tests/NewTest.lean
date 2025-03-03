import Lampe

open Lampe

nr_def aaa<>(x : u8, n : u8) -> u8 {
    let mut a = x;
    for _? in (0 : u8) .. n {
        a = #uAdd(a, 1 : u8) : u8
    };
    a
}

def addOne (u : U 8) : U 8 := u + 1

def asdf (n : Nat) := Nat.repeat addOne n

def thm : Nat.repeat addOne n u = u + n := by sorry

example (h : x < 100) (hn : n < 100)
    : STHoare p Γ ⟦⟧ (aaa.fn.body _ h![] |>.body h![x, n]) fun v => v = x + n := by
  simp only [aaa]
  steps
  rename_i a b
  loop_inv fun u _ _ => [a ↦ ⟨Tp.u 8, Nat.repeat addOne u.toNat x⟩]
  · intros i hl hu
    steps
    congr
    rename_i a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
    subst_vars
    rw [thm] at a8
    simp at a8
    let ⟨qoweiur, asrrrrf⟩ := a8
    rw [asrrrrf]
    simp [thm]
    have : (BitVec.toNat i + 1) % 256 = (i + 1).toNat := by
      simp
    rw [this]
    rw [BitVec.ofNat_toNat]
    simp
    change x + i + 1#8 = x + (i + 1#8)
    bv_decide
  · rename_i hh
    change b = 0 at hh
    bv_decide
  · rename_i t tt
    change b = 0 at tt
    congr
    simp [tt, Nat.repeat]
  · steps
    simp_all
    rw [thm]
    simp_all
