import Lampe

open Lampe

noir_def std::slice::append<T: Type>(mut self: Slice<T>, other: Slice<T>) -> Slice<T> := {
  {
    let ζi0 = other;
    for ζi1 in (0: u32) .. (#_arrayLen returning u32)(ζi0) do {
      let elem = (#_sliceIndex returning T)(ζi0, (#_cast returning u32)(ζi1));
      {
        self = (#_slicePushBack returning Slice<T>)(self, elem);
        #_skip
      }
    };
    #_skip
  };
  self
}

noir_def simple_array<T: Type, N: u32>(x: Array<T, N: u32>) -> u32 := {
  (#_arrayLen returning u32)(x)
}

def thmEnv : Env := .mk [«std::slice::append», simple_array] []

example  : STHoare p thmEnv ⟦⟧ («std::slice::append».call h![T] h![s₁, s₂])
    fun v => v = s₁ ++ s₂ := by
  enter_decl
  steps
  step_as ([self ↦ ⟨Tp.slice T, s₁⟩]) (fun (v : Tp.denote p Tp.unit) => ⟦v = ()⟧ ⋆ [self ↦ ⟨Tp.slice T, s₁ ++ s₂⟩])
  · steps
    loop_inv nat (fun i _ _ => [self ↦ ⟨Tp.slice T, s₁ ++ (s₂.take i)⟩])
    · simp
    · simp
    · intros i hlo hhi
      steps
      simp_all
    steps
    simp_all
  steps
  assumption

example: STHoare p thmEnv ⟦⟧ (simple_array.call h![T, N] h![arr])
    fun v => v = BitVec.ofNat 32 arr.length := by
  enter_decl
  steps
  subst_vars
  rfl
