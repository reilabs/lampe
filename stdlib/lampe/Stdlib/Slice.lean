import «std-1.0.0-beta.11».Extracted
import Lampe

open Lampe

open «std-1.0.0-beta.11».Extracted

set_option maxRecDepth 10000

-- TODO: array len needs fixing for this!
axiom slice_arrayLen {tp: Tp} {p slice} :
    STHoare p env ⟦⟧ (Expr.callBuiltin [tp.slice] (.u 32) Builtin.arrayLen h![slice]) (fun v => v.toNat = slice.length)

set_option trace.Lampe.STHoare.Helpers true
set_option trace.Lampe.SL true

lemma for_each_inv {T Env p f fb l}
    (Inv: List (Tp.denote p T) → SLP (State p))
    (h_inv: ∀(lp: List (Tp.denote p T)) (e: T.denote p), ((lp ++ [e]) <+: l) → STHoare p env (Inv lp) (fb h![e]) (fun _ => Inv (lp ++ [e]))):
    STHoare p env (Inv [] ⋆ [λf ↦ fb]) ((«std::slice::for_each».call h![T, Env] h![l, f])) (fun _ => Inv l ⋆ [λf ↦ fb]) := by
  enter_decl
  steps []
  loop_inv nat fun i _ _ => Inv (l.take i) ⋆ [λf ↦ fb]
  · intro i ihl ihg
    steps
    casesm ∃_,_
    subst_vars

  -- apply STHoare.letIn_intro (Q := fun _ => Inv l ⋆ [λf ↦ fb])
  -- · apply STHoare.ramified_frame_top
  --     (STHoare.loop_inv_intro' (Inv := fun i _ _ => Inv (l.take i) ⋆ [λf ↦ fb]) ?_)
  --   · simp_all
  --     simp [Nat.mod_eq_of_lt (by assumption)]
  --     sl
  --     simp
  --   · intro i ihl ihg
  --     steps
  --     simp_all
  --     casesm ∃_,_
  --     have : i % 4294967296 = i := by
  --       apply Nat.mod_eq_of_lt
  --       apply lt_trans ihg
  --       apply Nat.mod_lt
  --       simp
  --     apply STHoare.letIn_intro
  --     · apply STHoare.callLambda_intro
  --       apply h_inv (lp := l.take i)
  --       simp_all [List.take_prefix]
  --     · intro
  --       steps allow_sl
  --       simp_all
  --       sl
  -- intro
  -- steps

lemma slice_map_inv {T U Env p f fb l}
    (Inv: List (Tp.denote p T) → List (Tp.denote p U) → SLP (State p))
    (h_inv: ∀(ip: List (Tp.denote p T)) (rp: List (Tp.denote p U)) (e: T.denote p), ((ip ++ [e]) <+: l) → STHoare p env (Inv ip rp) (fb h![e]) (fun r => Inv (ip ++ [e]) (rp ++ [r]))):
    STHoare p env (Inv [] [] ⋆ [λf ↦ fb]) ((«std::slice::map».call h![T, U, Env] h![l, f])) (fun v => Inv l v ⋆ [λf ↦ fb]) := by sorry

lemma slice_pure_map {T U Env p f fb func l}
    (h_pure : ∀x, STHoare p env ⟦⟧ (fb h![x]) (fun r => r = func x)):
    STHoare p env [λf ↦ fb] ((«std::slice::map».call h![T, U, Env] h![l, f])) (fun v => v = l.map func) := by
  steps [slice_map_inv (Inv := fun i o => o = i.map func)]
  · assumption
  · rfl
  · intros; steps [h_pure]; simp_all
