import «std-1.0.0-beta.12».Extracted
import Lampe
import Stdlib.List
import Stdlib.TraitMethods

namespace Lampe.Stdlib.Slice
open «std-1.0.0-beta.12»

set_option maxRecDepth 1000

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem append_spec {p T a b}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::slice::append».call h![T] h![a, b])
    (fun r => r = a ++ b) := by
  enter_decl
  steps
  step_as ([self ↦ ⟨T.slice, a⟩]) (fun _ => [self ↦ ⟨T.slice, a ++ b⟩])
  · steps

    loop_inv nat fun i hlo hhi => [self ↦ ⟨T.slice, a ++ (b.take i)⟩]
    · simp
    · simp
    · intro cond hlo hhi
      steps
      simp_all
    · steps
      simp_all
  · steps
    simp_all

theorem as_array_spec {p T N input}
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::slice::as_array».call h![T, N] h![input])
    (fun r => r.toList = input) := by
  enter_decl
  steps
  loop_inv nat fun i hlo hhi => ∃∃v, [array ↦ ⟨T.array N, v⟩] ⋆ (v.toList.take i = input.take i)
  · sl; simp
  · simp
  · intro i _ _
    steps
    simp_all only [beq_true, decide_eq_true_eq, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, Lens.modify, Lens.get, Access.modify,
      BitVec.toNat_ofNatLT, ↓reduceDIte, Builtin.instCastTpU, BitVec.natCast_eq_ofNat,
      BitVec.ofNat_toNat, BitVec.setWidth_eq, List.get_eq_getElem, Option.bind_eq_bind,
      Option.bind_some, Option.bind_fun_some, Option.get_some, List.Vector.toList_set]
    rename_i take_of_vec_eq_input
    rw [List.take_succ]
    rw [List.take_set]
    rw [take_of_vec_eq_input]
    simp_all only [Lens.modify, Lens.get, Access.modify, BitVec.toNat_ofNatLT, ↓reduceDIte,
      Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      List.get_eq_getElem, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.isSome_some, List.length_set, List.Vector.toList_length, getElem?_pos,
      List.getElem_set_self, Option.toList_some]

    have : i < input.length := by simp_all
    have h : (List.take i input).set i input[i] = List.take i input := by
      rw [List.set_eq_of_length_le (by simp_all)]
    rw [h, List.take_append_getElem]

  steps
  rename_i a v _
  subst_vars
  have h1 : input.length = BitVec.toNat N := by aesop
  have h2 : v.toList.length = BitVec.toNat N := by simp_all
  conv at a =>
    congr
    · arg 1; rw [←h2]
    · rw [←h1]

  rw [List.take_length] at a
  simp_all

theorem map_spec {T U Env p f fb l}
    (Inv : List (Tp.denote p T) → List (Tp.denote p U) → SLP (State p))
    (h_inv : ∀(ip : List (Tp.denote p T)) (rp : List (Tp.denote p U)) (e : T.denote p),
      ((ip ++ [e]) <+: l) → STHoare p env (Inv ip rp) (fb h![e])
        (fun r => Inv (ip ++ [e]) (rp ++ [r])))
  : STHoare p env
    (Inv [] [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::map».call h![T, U, Env] h![l, f])
    (fun v => Inv l v ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨U.slice, []⟩] ⋆ [λf ↦ fb] ⋆ Inv [] [])
    (fun _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [λf ↦ fb] ⋆ Inv l v)
  · steps
    loop_inv nat fun i _ _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [λf ↦ fb] ⋆ Inv (l.take i) v
    · sl
    · simp
    · intro i ihl ihg
      steps
      simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
        zero_le, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem]
      generalize_proofs
      rename U.slice.denote p => v
      have := h_inv (l.take i) v l[i] (by simp [List.take_prefix])
      steps [STHoare.callLambda_intro (hlam := this)]
      simp_all only [List.take_append_getElem, Lens.modify, Option.get_some]
      sl
    · steps
      simp [*]
      sl
  steps
  simp_all
  sl

theorem map_pure_spec {T U Env p f fb func l}
    (h_pure : ∀x, STHoare p env ⟦⟧ (fb h![x]) (fun r => r = func x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::map».call h![T, U, Env] h![l, f])
    (fun v => v = l.map func) := by
  steps [map_spec (Inv := fun i o => o = i.map func)]
  · rfl
  · assumption
  · intros; steps [h_pure]; simp_all

theorem mapi_spec {T U Env p f fb l}
    (inv : List (T.denote p) → List (U.denote p) → SLP (State p))
    (inv_sem : ∀(ip : List (T.denote p)) (op : List (U.denote p)) (e : T.denote p),
      ((ip ++ [e]) <+: l) → STHoare p env (inv ip op) (fb h![ip.length, e])
        (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env
    (inv [] [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::mapi».call h![T, U, Env] h![l, f])
    (fun v => inv l v ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨U.slice, []⟩] ⋆ [index ↦ ⟨.u 32, 0⟩] ⋆ [λf ↦ fb] ⋆ inv [] [])
    (fun _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [index ↦ ⟨.u 32, l.length⟩] ⋆ [λf ↦ fb] ⋆ inv l v)
  · steps
    loop_inv nat fun i _ _ =>
      ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [index ↦ ⟨.u 32, i⟩] ⋆ [λf ↦ fb] ⋆ (inv (l.take i) v)
    · sl
    · simp
    · intro i hlo hhi
      steps
      simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
        EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, Builtin.instCastTpU,
        BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem]
      generalize_proofs
      rename Tp.denote p U.slice => v
      have := inv_sem (l.take i) v l[i] (by simp [List.take_prefix])
      have i_eq_len : (l.take i).length = i := by simp only [List.length_take, inf_eq_left]; omega
      rw [i_eq_len] at this
      steps [STHoare.callLambda_intro (hlam := this)]
      · simp only [List.take_append_getElem, Lens.modify, Option.get_some]; sl

      congr 1
      simp_all only [List.take_append_getElem, List.length_take, inf_eq_left, Lens.modify,
        Option.isSome_some, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_intCast, Int.reducePow,
        Int.reduceMod, Int.toNat_one, Option.get_some]
      rw [BitVec.ofNat_add]
      rfl

    · steps
      · simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
        EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.toNat_ofNatLT, zero_le, List.take_length]
        sl

      simp_all

  steps
  simp_all only [BitVec.natCast_eq_ofNat]; sl

theorem mapi_pure_spec {T U Env p f fb fEmb l}
    (inv_pure : ∀i x, (h : i < l.length) → STHoare p env ⟦⟧ (fb h![i, x]) (fun r => r = fEmb i x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::mapi».call h![T, U, Env] h![l, f])
    (fun v => v = l.mapIdx fEmb) := by
  steps [mapi_spec (inv := fun i o => o = i.mapIdx fEmb)]
  · rfl
  · assumption
  · intros
    rename List (T.denote p) => ip
    rename T.denote p => e
    steps [inv_pure ip.length e ?lt]
    case lt =>
      rename_i a
      simp_all only [BitVec.natCast_eq_ofNat, List.length_cons, List.length_nil, zero_add, gt_iff_lt]
      have h1 : (ip ++ [e]).length ≤ l.length := List.IsPrefix.length_le a
      rw [List.length_append] at h1
      exact h1

    simp_all

theorem for_each_spec {T Env p f fb l}
    (Inv : List (Tp.denote p T) → SLP (State p))
    (h_inv : ∀(lp : List (Tp.denote p T)) (e : T.denote p),
      ((lp ++ [e]) <+: l) → STHoare p env (Inv lp) (fb h![e]) (fun _ => Inv (lp ++ [e])))
  : STHoare p env
    (Inv [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::for_each».call h![T, Env] h![l, f])
    (fun _ => Inv l ⋆ [λf ↦ fb]) := by
  enter_decl
  steps []
  loop_inv nat fun i _ _ => Inv (l.take i) ⋆ [λf ↦ fb]
  · simp
  · intro i ihl ihg
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.get_eq_getElem]
    generalize_proofs
    have := h_inv (l.take i) l[i] $ by
      simp [List.take_prefix]
    steps [STHoare.callLambda_intro (hlam := this)]
    simp only [List.take_append_getElem]
    sl
  steps
  simp_all
  sl

theorem for_eachi_spec {T Env p f fb l}
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (e : T.denote p),
      ((ip ++ [e]) <+: l) → STHoare p env (inv ip) (fb h![ip.length, e]) (fun _ => inv (ip ++ [e])))
  : STHoare p env
    (inv [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::for_eachi».call h![T, Env] h![l, f])
    (fun _ => inv l ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => [index ↦ ⟨.u 32, i⟩] ⋆ [λf ↦ fb] ⋆ inv (l.take i)
  · sl; simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, Builtin.instCastTpU,
      BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem]
    generalize_proofs
    have := inv_spec (l.take i) l[i] (by simp [List.take_prefix])
    have i_eq_len : (l.take i).length = i := by simp only [List.length_take, inf_eq_left]; omega
    rw [i_eq_len] at this

    steps [STHoare.callLambda_intro (hlam := this)]
    · simp only [List.take_append_getElem]; sl

    congr 1
    simp_all only [List.take_append_getElem, List.length_take, inf_eq_left, Lens.modify,
      Option.isSome_some, BitVec.toNat_ofNat, Nat.reducePow, BitVec.toNat_intCast, Int.reducePow,
      Int.reduceMod, Int.toNat_one, Option.get_some]
    rw [BitVec.ofNat_add]
    rfl

  steps
  simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
    EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.toNat_ofNatLT, zero_le, List.take_length]
  sl

theorem fold_spec {p T U Env l a f fb}
    (inv : List (T.denote p) → U.denote p → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (accum : U.denote p) (e : T.denote p),
      ((ip ++ [e] <+: l) → STHoare p env (inv ip accum)
        (fb h![accum, e])
        (fun r => inv (ip ++ [e]) r)))
  : STHoare p env
    (inv [] a ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::fold».call h![T, U, Env] h![l, a, f])
    (fun r => (inv l r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([accumulator ↦ ⟨U, a⟩] ⋆ [λf ↦ fb] ⋆ inv [] a)
    (fun _ => ∃∃v, [accumulator ↦ ⟨U, v⟩] ⋆ [λf ↦ fb] ⋆ inv l v)
  · steps
    loop_inv nat fun i _ _ => ∃∃v, [accumulator ↦ ⟨U, v⟩] ⋆ [λf ↦ fb] ⋆ inv (l.take i) v
    · sl
    · simp
    · intro i hlo hhi
      steps
      simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
        zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
        BitVec.toNat_ofNatLT, List.get_eq_getElem]
      generalize_proofs
      rename U.denote p => v
      have := inv_spec (l.take i) v l[i] (by simp [List.take_prefix])
      steps [STHoare.callLambda_intro (hlam := this)]
      simp only [List.take_append_getElem]; sl

    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      BitVec.toNat_ofNatLT, zero_le, List.take_length]
    sl

  steps
  subst_vars
  sl

theorem fold_pure_spec {p T U Env l a f fb fEmb}
    (inv_pure : ∀a x, STHoare p env ⟦⟧ (fb h![a, x]) (fun r => r = fEmb a x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::fold».call h![T, U, Env] h![l, a, f])
    (fun r => r = l.foldl fEmb a ⋆ [λf ↦ fb]) := by
  steps [fold_spec (inv := fun xs v => v = xs.foldl fEmb a)]
  · rfl
  · assumption
  · intros; steps [inv_pure]; simp_all

theorem reduce_spec {p T Env l f fb}
    (l_len_gt : l.length > 0)
    (inv : List (T.denote p) → T.denote p → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (acc : T.denote p) (e : T.denote p),
      ((ip ++ [e] <+: l.tail) → STHoare p env (inv ip acc) (fb h![acc, e])
        (fun r => inv (ip ++ [e]) r)))
  : STHoare p env
    ((inv [] l[0]) ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::reduce».call h![T, Env] h![l, f])
    (fun r => (inv l.tail r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  cases l with
  | nil => contradiction
  | cons init l =>
    simp only [List.tail_cons, List.length_cons, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, Fin.zero_eta, List.get_eq_getElem,
      Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero] at *
    loop_inv nat fun i _ _ => ∃∃v, [accumulator ↦ ⟨T, v⟩] ⋆ [λf ↦ fb] ⋆ inv (l.take (i-1)) v
    · sl
    · simp only [BitVec.toNat_intCast, BitVec.toNat_ofNatLT]; omega
    · intro i hlo hhi
      cases i with
      | zero => contradiction
      | succ i =>
        steps
        simp_all only [gt_iff_lt, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
          Int.toNat_zero, Int.reduceMod, Int.toNat_one, Builtin.instCastTpU,
          BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT, List.get_eq_getElem]
        generalize_proofs
        rename T.denote p => v
        have := inv_spec (l.take i) v (l[i]'(by simp_all)) (by simp [List.take_prefix])
        simp only [List.take_append_getElem] at this

        steps [STHoare.callLambda_intro (hlam := this)]

    steps
    simp_all only [List.length_cons, gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
      or_true, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      Int.reduceMod, Int.toNat_one, BitVec.toNat_ofNatLT, le_add_iff_nonneg_left, zero_le,
      add_tsub_cancel_right, List.take_length]
    sl

theorem reduce_pure_spec {p T Env l f fb fEmb}
    (l_len_gt : l.length > 0)
    (inv_pure : ∀a x, STHoare p env ⟦⟧ (fb h![a, x]) (fun r => r = fEmb a x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::reduce».call h![T, Env] h![l, f])
    (fun r => r = l.tail.foldl fEmb l[0] ⋆ [λf ↦ fb]) := by
  steps [reduce_spec (inv := fun xs v => v = xs.foldl fEmb l[0])]
  · rfl
  · assumption
  · intros
    steps [inv_pure]
    simp_all

theorem filter_spec {p T Env l f fb}
    (inv : List (T.denote p) → List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : List (T.denote p)) (e : T.denote p),
      ((ip ++ [e] <+: l) → STHoare p env (inv ip op) (fb h![e])
        (fun r => inv (ip ++ [e]) (if r then (op ++ [e]) else op))))
  : STHoare p env
    (inv [] [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::filter».call h![T, Env] h![l, f])
    (fun r => (inv l r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨T.slice, []⟩] ⋆ [λf ↦ fb] ⋆ (inv [] []))
    (fun _ => ∃∃v, [ret ↦ ⟨T.slice, v⟩] ⋆ [λf ↦ fb] ⋆ (inv l v))
  · steps
    loop_inv nat fun i _ _ => ∃∃v, [ret ↦ ⟨T.slice, v⟩] ⋆ [λf ↦ fb] ⋆ (inv (l.take i) v)
    · sl
    · simp
    · intro i hlo hhi
      steps
      simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
        zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
        BitVec.toNat_ofNatLT, List.get_eq_getElem]
      generalize_proofs
      rename Tp.denote p (T.slice) => v

      have := inv_spec (l.take i) v l[i] (by simp [List.take_prefix])
      steps [STHoare.callLambda_intro (hlam := this)]

      apply STHoare.ite_intro
      · intros
        steps
        simp_all
        sl
      · intros
        steps
        simp_all
        sl

    steps
    simp_all
    sl

  steps
  simp_all
  sl

theorem filter_pure_spec {p T Env l f fb fEmb}
    (inv_pure : ∀x, STHoare p env ⟦⟧ (fb h![x]) (fun r => r = fEmb x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::filter».call h![T, Env] h![l, f])
    (fun r => (r = l.filter fEmb)) := by
  steps [filter_spec (inv := fun xs v => v = xs.filter fEmb)]
  · rfl
  · assumption
  · intros
    steps [inv_pure]
    subst_vars
    split
    all_goals simp_all

theorem join_spec {p T a s}
    {t_append : Append.hasImpl env T}
    {t_empty_emb : T.denote p}
    {t_app_emb : T.denote p → T.denote p → T.denote p}
    (t_empty_sem : STHoare p env ⟦⟧ (Append.empty h![] T h![] h![] h![]) (fun r => r = t_empty_emb))
    (t_app_sem : ∀a b, STHoare p env ⟦⟧ (Append.append h![] T h![] h![] h![a, b])
      (fun r => r = t_app_emb a b))
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::slice::join».call h![T] h![a, s])
    (fun r => r = if h : a.length > 0 then
      a.tail.foldl (fun l r => t_app_emb (t_app_emb l s) r) a[0]
    else t_empty_emb) := by
  enter_decl
  steps [t_empty_sem]

  let foldFnEmb := fun l r => t_app_emb (t_app_emb l s) r

  step_as ([ret ↦ ⟨T, t_empty_emb⟩])
    (fun _ => [ret ↦ ⟨T, if h : a.length > 0 then a.tail.foldl foldFnEmb a[0] else t_empty_emb⟩])

  apply STHoare.ite_intro
  · intro cond
    steps
    simp_all only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
      Lens.modify, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      List.get_eq_getElem, Option.get_some, gt_iff_lt]

    loop_inv nat fun i _ _ => [ret ↦ ⟨T, (a.tail.take (i - 1)).foldl foldFnEmb a[0]⟩]
    · simp_all only [Lens.modify, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
      Int.toNat_zero, List.get_eq_getElem, Option.isSome_some, Int.reduceMod, Int.toNat_one,
      BitVec.toNat_ofNatLT]
      omega
    · intro i hlo hhi
      steps [t_app_sem]
      congr
      simp_all only [Lens.modify, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
        Int.toNat_zero, List.get_eq_getElem, Option.isSome_some, Int.reduceMod, Int.toNat_one,
        Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT,
        Option.get_some]

      have : i + 1 - 1 = i - 1 + 1 := by omega
      rw [this, List.take_succ_eq_append_getElem ?i_lt]

      case i_lt =>
        rw [List.length_tail]
        have : i < a.length := by simp [BitVec.toNat_ofNatLT (by omega)] at hhi; assumption
        omega

      simp [List.getElem_tail, Nat.sub_add_cancel hlo, foldFnEmb]

    steps
    congr
    have : 0 < a.length := by omega
    simp_all only [Lens.modify, BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
      Int.toNat_zero, List.get_eq_getElem, Option.isSome_some, Int.reduceMod, Int.toNat_one,
      BitVec.toNat_ofNatLT, ↓reduceDIte]

    congr
    rw [←List.length_tail, List.take_length]

  · intro cond
    simp_all only [ne_eq, decide_not, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq,
      gt_iff_lt]
    steps
    congr
    have : a.length = 0 := by
      apply_fun BitVec.toNat at cond
      rw [BitVec.toNat_ofNatLT (a.length) (by omega)] at cond
      norm_cast
    rw [List.length_eq_zero_iff.mp this]
    simp

  steps
  simp_all [foldFnEmb]

theorem all_spec {p T Env l f fb}
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : Bool) (e : T.denote p),
      (ip ++ [e] <+: l) → STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ∧ r)))
  : STHoare p env
    ((inv [] true) ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::all».call h![T, Env] h![l, f])
    (fun r => (inv l r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps

  step_as ([ret ↦ ⟨.bool, true⟩] ⋆ (inv [] true) ⋆ [λf ↦ fb])
    (fun r => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv l b) ⋆ [λf ↦ fb])

  steps
  loop_inv nat fun i _ _ => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv (l.take i) b) ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.get_eq_getElem]

    generalize_proofs
    rename Tp.denote p .bool => b
    have := inv_spec (l.take i) b l[i] (by simp [List.take_prefix])

    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Bool.decide_and, Bool.decide_eq_true, Bool.forall_bool, Bool.false_and,
      Bool.true_and, List.take_append_getElem, Lens.modify, Option.get_some]
    sl
    exact ()
  · simp_all only [Bool.decide_and, Bool.decide_eq_true, Bool.forall_bool, Bool.false_and,
    Bool.true_and, BitVec.toNat_ofNatLT, List.take_length, SLP.star_true]
    steps

  steps
  subst_vars
  sl

theorem all_pure_spec {p T Env l f fb fEmb}
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::all».call h![T, Env] h![l, f])
    (fun r => r = l.all fEmb) := by
  steps [all_spec (inv := fun x r => r = x.all fEmb)]
  · simp
  · assumption
  · intro ip op e pfx
    steps [inv_pure]
    simp_all only [List.all_eq_true, Bool.decide_and, Bool.decide_eq_true, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true]
    rw [←List.all_eq]

theorem any_spec {p T Env l f fb}
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : Bool) (e : T.denote p),
      (ip ++ [e] <+: l) → STHoare p env (inv ip op) (fb h![e]) (fun r => inv (ip ++ [e]) (op ∨ r)))
  : STHoare p env
    ((inv [] false) ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::slice::any».call h![T, Env] h![l, f])
    (fun r => (inv l r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps

  step_as ([ret ↦ ⟨.bool, false⟩] ⋆ (inv [] false) ⋆ [λf ↦ fb])
    (fun r => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv l b) ⋆ [λf ↦ fb])

  steps
  loop_inv nat fun i _ _ => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv (l.take i) b) ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.get_eq_getElem]

    generalize_proofs
    rename Tp.denote p .bool => b
    have := inv_spec (l.take i) b l[i] (by simp [List.take_prefix])

    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.forall_bool, Bool.false_or,
      Bool.true_or, List.take_append_getElem, Lens.modify, Option.get_some]
    sl
    exact ()
  · simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.forall_bool, Bool.false_or, Bool.true_or,
    BitVec.toNat_ofNatLT, List.take_length, SLP.star_true]
    steps

  steps
  subst_vars
  sl

theorem any_pure_spec {p T Env l f fb fEmb}
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::slice::any».call h![T, Env] h![l, f])
    (fun r => r = l.any fEmb) := by
  steps [any_spec (inv := fun x r => r = x.any fEmb)]
  · simp
  · assumption
  · intro ip op e pfx
    steps [inv_pure]
    simp_all only [List.any_eq_true, Bool.decide_or, Bool.decide_eq_true, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]
    rw [←List.any_eq]
