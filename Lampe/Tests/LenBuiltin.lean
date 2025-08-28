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

def appendEnv : Env := .mk [«std::slice::append»] []

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

example : STHoare p appendEnv ⟦⟧ («std::slice::append».call h![T] h![s₁, s₂])
    fun v => v = s₁ ++ s₂ := by
  enter_decl
  steps
  step_as ([self ↦ ⟨Tp.slice T, s₁⟩]) (fun v => v = ())
  · steps
