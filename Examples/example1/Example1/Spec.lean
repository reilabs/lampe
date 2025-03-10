import Lampe
import Example1.Extracted
import Example1.Ref

open Lampe Test

example : STHoare p Γ ⟦⟧ (main.fn.body _ h![] |>.body h![x, y]) fun v => v = x + y := by
    simp only [main]
    steps
    assumption
