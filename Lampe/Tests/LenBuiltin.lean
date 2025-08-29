import Lampe

open Lampe

noir_def std::slice::append<T: Type>(mut self: Slice<T>, other: Slice<T>) -> Slice<T> := {
  {
    let (ζi0: Slice<T>) = other;
    for ζi1 in (0: u32) .. (#_arrayLen returning u32)(ζi0) do {
      let (elem: T) = (#_sliceIndex returning T)(ζi0, (#_cast returning u32)(ζi1));
      {
        self = (#_slicePushBack returning Slice<T>)(self, elem);
        #_skip
      }
    };
    #_skip
  };
  self
}

noir_def std::array::concat<T: Type, N: u32, M: u32>(self: Array<T, N: u32>, array2: Array<T, M: u32>) -> Array<T, (N + M): u32> := {
  let mut (result: Array<T, (N + M): u32>) = (#_mkRepeatedArray returning Array<T, (N + M): u32>)((#_zeroed returning T)());
  for i in (0: u32) .. uConst!(N: u32) do {
    (result[i]: T) = (#_arrayIndex returning T)(self, (#_cast returning u32)(i));
    #_skip
  };
  for i in (0: u32) .. uConst!(M: u32) do {
    let (i_3606: Unit) = (#_uAdd returning u32)(i, uConst!(N: u32));
    (result[i_3606]: T) = (#_arrayIndex returning T)(array2, (#_cast returning u32)(i));
    #_skip
  };
  result
}

def thmEnv : Env := .mk [«std::slice::append», «std::array::concat»] []

example (hLen : s₂.length < 2 ^ 32) : STHoare p thmEnv ⟦⟧ («std::slice::append».call h![T] h![s₁, s₂])
    fun v => v = s₁ ++ s₂ := by
  enter_decl
  steps
  step_as ([self ↦ ⟨Tp.slice T, s₁⟩]) (fun (v : Tp.denote p Tp.unit) => ⟦v = ()⟧ ⋆ [self ↦ ⟨Tp.slice T, s₁ ++ s₂⟩])
  · steps
    subst_vars; assumption
    loop_inv nat (fun i _ _ => [self ↦ ⟨Tp.slice T, s₁ ++ (s₂.take i)⟩])
    · simp
    · congr; simp
    · intros i hlo hhi
      steps
      simp_all
      subst_vars
      congr
      rename_i ha _
      let ⟨_, h⟩ := ha
      have : i % 4294967296 = i := by omega
      simp [this] at h
      simp [h]
    steps
    subst_vars
    congr
    simp
    rw [Nat.mod_eq_of_lt]
    assumption
  steps
  assumption

lemma innercast (hSize : N.toNat + M.toNat < 4294967296): (Tp.denote p (Tp.array T (N + M))) = List.Vector (Tp.denote p T) (N.toNat + M.toNat) := by
  conv_lhs => unfold Tp.denote
  congr
  simp [hSize]

lemma outercast : («std::array::concat».fn.body (Tp.denote p) h![T, N, M]).outTp = (Tp.array T (N + M)) := by
  unfold «std::array::concat»
  simp

-- set_option Lampe.pp.Expr true
-- set_option Lampe.pp.STHoare true
set_option trace.Lampe.STHoare.Helpers true

example (hSize : N.toNat + M.toNat < 4294967296) : STHoare p thmEnv ⟦⟧ («std::array::concat».call h![T, N, M] h![arr₁, arr₂])
    fun v => v = outercast ▸ (innercast (by exact hSize)) ▸ (arr₁ ++ arr₂) := by
  enter_decl
  steps
  let x := List.Vector.replicate (N + M).toNat (Tp.zero p T) -- not right, but testing for now
  loop_inv nat (fun i hlo hhi => [result ↦ ⟨Tp.array T (N + M), x⟩])
  · sorry
  -- apply STHoare.letIn_trivial_intro
  -- let h := @STHoare.loop_inv_intro 32 0 (N + M).toNat p Tp.unit thmEnv
  --   fun i _ _ => [result ↦ ⟨Tp.array T (N + M), x⟩]
  -- apply STHoare.loop_inv_intro (fun i _ _ => [result ↦ ⟨Tp.array T (N + M), x⟩])
