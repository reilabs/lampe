import «std-1.0.0-beta.12».Extracted
import Stdlib.Array.CheckShuffle
import Stdlib.Convert
import Stdlib.Tp

import Batteries.Classes.Order
import Lampe

namespace Lampe.Stdlib.Array
namespace Lampe.Stdlib.List

open «std-1.0.0-beta.12»

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

theorem map_spec {p T N U Env l f fb}
    (inv : List (T.denote p) → List (U.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : List (U.denote p)) (e : T.denote p),
      (ip ++ [e] <+: l.toList) → STHoare p env (inv ip op) (fb h![e])
        (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env
    ((inv [] []) ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::map».call h![T, N, U, Env] h![l, f])
    (fun r => inv l.toList r.toList ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => ∃∃v,
    [ret ↦ ⟨U.array N, v⟩] ⋆ (inv (l.take i).toList (v.take i).toList) ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, List.Vector.toList_take, Builtin.instCastTpU, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
    generalize_proofs
    rename_i i_lt_pow

    rename Tp.denote p (U.array N) => v
    have := inv_spec (l.take i).toList (v.take i).toList (l.toList[i]'(by simp_all))
      (by simp [List.take_prefix])
    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.Vector.toList_take, List.take_append_getElem, Lens.modify,
      Lens.get, Access.modify, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some,
      Option.bind_fun_some, Option.get_some, List.Vector.toList_set]

    have : i < (v.toList.set i «#v_5»).length := by simp_all
    conv => rhs; enter [1, 2]; rw [List.take_succ_eq_append_getElem this]
    simp only [List.getElem_set this, if_true]
    conv =>
      rhs
      enter [1, 2, 1]
      apply List.take_set_of_le (by rfl)

    sl

  steps
  simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
    List.Vector.toList_take]

  rename Tp.denote p (U.array N) => v
  rename_i a
  have l1 : BitVec.toNat N = l.toList.length := by simp
  have l2 : BitVec.toNat N = v.toList.length := by simp

  conv =>
    lhs
    rhs
    congr
    · arg 1; apply l1
    · arg 1; apply l2

  simp only [a, List.take_length]
  sl

theorem map_pure_spec {p T N U Env l f fb fEmb}
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::map».call h![T, N, U, Env] h![l, f])
    (fun r => r.toList = l.toList.map fEmb) := by
  steps [map_spec (inv := fun i o => o = i.map fEmb)]
  · simp
  · assumption
  · intros; steps [inv_pure]; simp_all

theorem mapi_spec {p T N U Env l f fb}
    (inv : List (T.denote p) → List (U.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : List (U.denote p)) (e : T.denote p),
      ((ip ++ [e]) <+: l.toList) → STHoare p env (inv ip op) (fb h![ip.length, e])
        (fun r => inv (ip ++ [e]) (op ++ [r])))
  : STHoare p env
    (inv [] [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::mapi».call h![T, N, U, Env] h![l, f])
    (fun r => inv l.toList r.toList ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ =>
    ∃∃v, [ret ↦ ⟨U.array N, v⟩] ⋆ inv (l.take i).toList (v.take i).toList ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, List.Vector.toList_take,
      Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
    generalize_proofs
    rename_i i_lt_pow i_lt_n

    rename Tp.denote p (U.array N) => v
    have := inv_spec (l.take i).toList (v.take i).toList (l.toList[i]'(by simp_all))
      (by simp [List.take_prefix])
    have i_eq_len_take : BitVec.ofNatLT i i_lt_pow = BitVec.ofNat 32 (l.take i).toList.length := by
      simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
        BitVec.toNat_ofNatLT, Nat.reducePow, List.Vector.toList_take, List.length_take,
        List.Vector.toList_length, List.take_append_getElem, BitVec.natCast_eq_ofNat]
      congr
      omega
    simp only [i_eq_len_take]

    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      List.Vector.toList_take, List.length_take, List.Vector.toList_length, BitVec.toNat_ofNat,
      Nat.reducePow, List.take_append_getElem, Lens.modify, Lens.get, Access.modify, ↓reduceDIte,
      Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some, Option.get_some,
      List.Vector.toList_set]

    have : (min i N.toNat) % 4294967296 = i := by omega
    rw [this]
    have : i < (v.toList.set i «#v_5»).length := by simp_all
    conv => rhs; enter [1, 2]; rw [List.take_succ_eq_append_getElem this]
    simp only [List.getElem_set this, if_true]
    conv => rhs; enter [1, 2, 1]; apply List.take_set_of_le (by rfl)
    sl

  steps
  simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
    EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
    List.Vector.toList_take]

  rename Tp.denote p (U.array N) => v
  rename_i a
  have l1 : BitVec.toNat N = l.toList.length := by simp
  have l2 : BitVec.toNat N = v.toList.length := by simp
  conv =>
    lhs
    rhs
    congr
    · arg 1; apply l1
    · arg 1; apply l2

  simp only [a, List.take_length]
  sl

theorem mapi_pure_spec {p T N U Env l f fb fEmb}
    (inv_pure : ∀i x, (h : i < l.length) → STHoare p env ⟦⟧ (fb h![i, x]) (fun r => r = fEmb i x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::mapi».call h![T, N, U, Env] h![l, f])
    (fun r => r.toList = l.toList.mapIdx fEmb) := by
  steps [mapi_spec (inv := fun i o => o = i.mapIdx fEmb)]
  · simp
  · assumption
  · intros;
    rename List (T.denote p) => ip
    rename T.denote p => e
    steps [inv_pure ip.length e ?lt]
    case lt =>
      rename_i a
      simp_all only [BitVec.natCast_eq_ofNat]
      have h1 : (ip ++ [e]).length ≤ l.toList.length := List.IsPrefix.length_le a
      have h2 : l.toList.length = l.length := by simp
      rw [h2, List.length_append] at h1
      exact h1

    simp_all

theorem for_each_spec {p T N Env l f fb}
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (e : T.denote p),
      ((ip ++ [e]) <+: l.toList) → STHoare p env (inv ip) (fb h![e]) (fun _ => inv (ip ++ [e])))
  : STHoare p env
    (inv [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::for_each».call h![T, N, Env] h![l, f])
    (fun _ => inv l.toList ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => inv (l.take i).toList ⋆ [λf ↦ fb]
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, List.Vector.toList_take, Builtin.instCastTpU, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
    generalize_proofs

    have := inv_spec (l.take i).toList (l.toList[i]'(by simp_all)) (by simp [List.take_prefix])
    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.Vector.toList_take, List.take_append_getElem]
    sl

  steps
  simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
    List.Vector.toList_take]
  have l1 : BitVec.toNat N = l.toList.length := by simp
  conv => lhs; enter [1, 1]; rw [l1]
  simp only [List.take_length]
  sl

theorem for_eachi_spec {p T N Env l f fb}
    (inv : List (T.denote p) → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (e : T.denote p),
      ((ip ++ [e] <+: l.toList) → STHoare p env (inv ip) (fb h![ip.length, e]) (fun _ => inv (ip ++ [e]))))
  : STHoare p env
    (inv [] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::for_eachi».call h![T, N, Env] h![l, f])
    (fun _ => inv l.toList ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  loop_inv nat fun i _ _ => inv (l.take i).toList ⋆ [λf ↦ fb]
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, List.Vector.toList_take,
      Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
    generalize_proofs
    rename_i i_lt_pow i_lt_n

    have := inv_spec (l.take i).toList (l.toList[i]'(by simp_all)) (by simp [List.take_prefix])
    have i_eq_len_take : BitVec.ofNatLT i i_lt_pow = BitVec.ofNat 32 (l.take i).toList.length := by
      simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
        BitVec.toNat_ofNatLT, Nat.reducePow, List.Vector.toList_take, List.length_take,
        List.Vector.toList_length, List.take_append_getElem, BitVec.natCast_eq_ofNat]
      congr
      omega
    simp only [i_eq_len_take]
    steps [STHoare.callLambda_intro (hlam := this)]

    simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      List.Vector.toList_take, List.length_take, List.Vector.toList_length, BitVec.toNat_ofNat,
      Nat.reducePow, List.take_append_getElem]
    sl

  steps
  simp_all only [BitVec.natCast_eq_ofNat, BitVec.toNat_intCast, Int.reducePow,
    EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
    List.Vector.toList_take]
  have l1 : BitVec.toNat N = l.toList.length := by simp
  conv => lhs; enter [1, 1]; rw [l1]
  simp only [List.take_length]
  sl

theorem fold_spec {p T N U Env l a f fb}
    (inv : List (T.denote p) → U.denote p → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (accum : U.denote p) (e : T.denote p),
      ((ip ++ [e] <+: l.toList) → STHoare p env (inv ip accum) (fb h![accum, e])
        (fun r => inv (ip ++ [e]) r)))
  : STHoare p env
    (inv [] a ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::fold».call h![T, N, U, Env] h![l, a, f])
    (fun r => (inv l.toList r) ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([accumulator ↦ ⟨U, a⟩] ⋆ [λf ↦ fb] ⋆ inv [] a)
    (fun _ => ∃∃v, [accumulator ↦ ⟨U, v⟩] ⋆ [λf ↦ fb] ⋆ inv l.toList v)
  steps
  loop_inv nat fun i _ _ => ∃∃v, [accumulator ↦ ⟨U, v⟩] ⋆ [λf ↦ fb] ⋆ inv (l.take i).toList v
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, List.Vector.toList_take]
    generalize_proofs
    rename U.denote p => v

    have := inv_spec (l.take i).toList v (l.toList[i]'(by simp_all)) (by simp [List.take_prefix])
    steps [STHoare.callLambda_intro (hlam := this)]

    simp_all only [List.Vector.toList_take, List.take_append_getElem, Lens.modify, Option.get_some]
    sl

  steps
  simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
    BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, zero_le,
    List.Vector.toList_take]

  have l1 : BitVec.toNat N = l.toList.length := by simp
  simp only [l1, List.take_length]
  sl

  steps
  subst_vars
  sl

theorem fold_pure_spec {p T N U Env l a f fb fEmb}
    (inv_pure : ∀a x, STHoare p env ⟦⟧ (fb h![a, x]) (fun r => r = fEmb a x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::fold».call h![T, N, U, Env] h![l, a, f])
    (fun r => r = l.toList.foldl fEmb a ⋆ [λf ↦ fb]) := by
  steps [fold_spec (inv := fun xs v => v = xs.foldl fEmb a)]
  · rfl
  · assumption
  · intros; steps [inv_pure]; simp_all

theorem reduce_spec {p T N Env l f fb}
    (l_len_gt : l.length > 0)
    (inv : List (T.denote p) → T.denote p → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (acc : T.denote p) (e : T.denote p),
      ((ip ++ [e] <+: l.toList.tail) → STHoare p env (inv ip acc) (fb h![acc, e])
        (fun r => inv (ip ++ [e]) r)))
  : STHoare p env
    (inv [] l[0] ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::reduce».call h![T, N, Env] h![l, f])
    (fun r => inv l.toList.tail r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  rcases l_def : l with ⟨ts, l_prf⟩
  have ts_len_gt_0 : ts.length > 0 := by omega
  cases ts with
  | nil => contradiction
  | cons init r =>
    have r_len_succ_eq_n : r.length + 1 = N.toNat := l_prf
    simp only [List.Vector.toList_mk, List.tail_cons, List.length_cons, gt_iff_lt,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] at *
    loop_inv nat fun i _ _ => ∃∃v, [accumulator ↦ ⟨T, v⟩] ⋆ [λf ↦ fb] ⋆ inv (r.take (i - 1)) v
    · sl
    · simp only [BitVec.toNat_intCast, Int.reducePow, Int.reduceMod, Int.toNat_one]; omega
    · intro i hlo hhi
      cases i with
      | zero => contradiction
      | succ i =>
        steps
        simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod,
          Int.toNat_zero, gt_iff_lt, Int.reduceMod, Int.toNat_one, le_add_iff_nonneg_left, zero_le,
          add_tsub_cancel_right, Builtin.instCastTpU, BitVec.truncate_eq_setWidth,
          BitVec.setWidth_eq, BitVec.toNat_ofNatLT]
        generalize_proofs
        rename T.denote p => v

        have i_lt_r_length : i < r.length := by
          have : (init :: r).length = N.toNat := by simp_all
          have : i + 1 < N.toNat := by linarith
          omega

        have := inv_spec (r.take i) v r[i] (by simp [List.take_prefix])
        have get_eq_getElem : List.Vector.get ⟨init :: r, l_prf⟩ ⟨i + 1, hhi⟩ = r[i] := by rfl
        rw [get_eq_getElem]

        steps [STHoare.callLambda_intro (hlam := this)]
        simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
          BitVec.toNat_ofNatLT, List.Vector.toList_mk, List.tail_cons, List.take_append_getElem,
          Lens.modify, Option.get_some]
        sl

    steps
    simp_all only [gt_iff_lt, List.Vector.toList_mk, List.tail_cons, BitVec.toNat_intCast,
      Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero, Int.reduceMod, Int.toNat_one]
    have : r.length = N.toNat - 1 := by omega
    rw [←this, List.take_length]
    subst_vars
    sl

theorem reduce_pure_spec {p T N Env l f fb fEmb}
    (l_len_gt : l.length > 0)
    (inv_pure : ∀a x, STHoare p env ⟦⟧ (fb h![a, x]) (fun r => r = fEmb a x))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::reduce».call h![T, N, Env] h![l, f])
    (fun r => r = l.toList.tail.foldl fEmb l[0] ⋆ [λf ↦ fb]) := by
  steps [reduce_spec (inv := fun xs v => v = xs.foldl fEmb l[0])]
  · rfl
  · assumption
  · intros; steps [inv_pure]; simp_all

theorem all_spec {p T N Env l f fb}
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : Bool) (e : T.denote p),
      ((ip ++ [e] <+: l.toList) → STHoare p env (inv ip op) (fb h![e])
        (fun r => inv (ip ++ [e]) (op ∧ r))))
  : STHoare p env
    (inv [] true ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::all».call h![T, N, Env] h![l, f])
    (fun r => inv l.toList r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨.bool, true⟩] ⋆ (inv [] true) ⋆ [λf ↦ fb])
    (fun r => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv l.toList b) ⋆ [λf ↦ fb])

  steps
  loop_inv nat fun i _ _ => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv (l.toList.take i) b) ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT]
    generalize_proofs
    rename Tp.denote p .bool => b

    have := inv_spec (l.toList.take i) b (l.toList[i]'(by simp_all)) (by simp [List.take_prefix])
    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Bool.decide_and, Bool.decide_eq_true, Bool.forall_bool, Bool.false_and,
      Bool.true_and, List.take_append_getElem, Lens.modify, Option.get_some]
    sl
    exact ()
  · simp_all only [Bool.decide_and, Bool.decide_eq_true, Bool.forall_bool, Bool.false_and,
    Bool.true_and, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, SLP.star_true]
    steps

    have : l.toList.length = N.toNat := by simp
    simp only [←this, List.take_length]
    sl

  steps
  subst_vars
  sl

theorem all_pure_spec {p T N Env l f fb fEmb}
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::all».call h![T, N, Env] h![l, f])
    (fun r => r = l.toList.all fEmb) := by
  steps [all_spec (inv := fun x r => r = x.all fEmb)]
  · simp
  · assumption
  · intro ip op e pfx
    steps [inv_pure]
    simp_all only [List.all_eq_true, Bool.decide_and, Bool.decide_eq_true, List.all_append,
      List.all_cons, List.all_nil, Bool.and_true]
    rw [←List.all_eq]

theorem any_spec {p T N Env l f fb}
    (inv : List (T.denote p) → Bool → SLP (State p))
    (inv_spec : ∀(ip : List (T.denote p)) (op : Bool) (e : T.denote p),
      ((ip ++ [e] <+: l.toList) → STHoare p env (inv ip op) (fb h![e])
        (fun r => inv (ip ++ [e]) (op ∨ r))))
  : STHoare p env
    (inv [] false ⋆ [λf ↦ fb])
    («std-1.0.0-beta.12::array::any».call h![T, N, Env] h![l, f])
    (fun r => inv l.toList r ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨.bool, false⟩] ⋆ (inv [] false) ⋆ [λf ↦ fb])
    (fun r => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv l.toList b) ⋆ [λf ↦ fb])

  steps
  loop_inv nat fun i _ _ => ∃∃b, [ret ↦ ⟨.bool, b⟩] ⋆ (inv (l.toList.take i) b) ⋆ [λf ↦ fb]
  · sl
  · simp
  · intro i hlo hhi
    steps
    simp_all only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_le, Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT]
    generalize_proofs
    rename Tp.denote p .bool => b

    have := inv_spec (l.toList.take i) b (l.toList[i]'(by simp_all)) (by simp [List.take_prefix])
    steps [STHoare.callLambda_intro (hlam := this)]
    simp_all only [Bool.decide_or, Bool.decide_eq_true, Bool.forall_bool, Bool.false_or,
      Bool.true_or, List.take_append_getElem, Lens.modify, Option.get_some]
    sl
    exact ()
  · simp_all only [Bool.decide_and, Bool.decide_eq_true, Bool.forall_bool, Bool.false_and,
    Bool.true_and, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, SLP.star_true]
    steps

    have : l.toList.length = N.toNat := by simp
    simp only [←this, List.take_length]
    sl

  steps
  subst_vars
  sl

theorem any_pure_spec {p T N Env l f fb fEmb}
    (inv_pure : ∀a, STHoare p env ⟦⟧ (fb h![a]) (fun r => r = fEmb a))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::any».call h![T, N, Env] h![l, f])
    (fun r => r = l.toList.any fEmb) := by
  steps [any_spec (inv := fun x r => r = x.any fEmb)]
  · simp
  · assumption
  · intro ip op e pfx
    steps [inv_pure]
    simp_all only [List.any_eq_true, Bool.decide_or, Bool.decide_eq_true, List.any_append,
      List.any_cons, List.any_nil, Bool.or_false]
    rw [←List.any_eq]

theorem concat_spec: STHoare p env ⟦⟧
    («std-1.0.0-beta.12::array::concat».call h![T, M, N] h![a₁, a₂])
    (fun r => r.toList = a₁.toList ++ a₂.toList) := by
  enter_decl
  steps

  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨T.array (M + N), v⟩] ⋆ (v.toList.take i = a₁.toList.take i)
  · sl
    simp
  · simp
  · intro i hil hiu
    steps
    rename Option.isSome _ = true => hp
    simp at hp
    rw [List.take_succ_eq_append_getElem ?lt1, List.take_succ_eq_append_getElem ?lt2]
    case lt1 => simp_all
    case lt2 => simp_all
    simp only [BitVec.toNat_add, Nat.reducePow, BitVec.add_eq, Lens.modify, Lens.get, Access.modify,
      BitVec.toNat_ofNatLT, Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.get_dite, List.Vector.toList_set, le_refl, List.take_set_of_le, List.getElem_set_self]
    congr

  steps

  loop_inv nat fun i _ _ => ∃∃v, [result ↦ ⟨T.array (M + N), v⟩] ⋆ (v.toList.take (M.toNat + i) = a₁.toList ++ a₂.toList.take i)
  · sl
    simp_all
  · simp
  · intro i hil hiu
    steps
    rw [←add_assoc, List.take_succ, List.take_succ, ←List.append_assoc]
    have : i_3710.toNat = M.toNat + i := by
      subst i_3710
      simp only [BitVec.toNat_add]
      rw [Nat.mod_eq_of_lt (by assumption), add_comm]
      rfl
    congr 1
    · simp [this]
      rw [List.take_set_of_le (by simp)]
      assumption
    simp only [BitVec.toNat_add, Nat.reducePow, BitVec.add_eq, Lens.modify, Lens.get, Access.modify,
      Builtin.instCastTpU, BitVec.natCast_eq_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, Option.bind_eq_bind, Option.bind_some, Option.bind_fun_some,
      Option.get_dite, List.Vector.toList_set]

    rw [List.getElem?_set, this]
    rename Option.isSome _ = true => hp
    simp [this] at hp
    simp [*]
    rfl
  steps
  rename List.take _ _ = _ ++ _ => hp
  rw [List.take_of_length_le ?le1, List.take_of_length_le ?le2] at hp
  case le1 => simp [Nat.mod_le]
  case le2 => simp
  simp_all

/--
This theorem asserts that `std::array::sort_via` implements a valid sort (namely that the output is
a sorted permutation of the input) but does not make any requirements on _how_ the sort is done.

It makes no guarantees as to the computational complexity or stability of the sort, but does ensure
that the result is ordered by the provided relation and that its elements represent a valid
permutation of the input.

Do note that the function as written can only assume that the elements are pairwise ordered by the
provided comparator function. In other words, it does **not** guarantee that they are sorted unless
the comparator function is transitive. For a more strict version of this theorem, see
`sort_via_trans_spec`, which uses a proof of transitivity for the comparator to assure that the
output is sorted.

Note that we have intentionally omitted an impure theorem for `sort_via` as we can envision no sane
use-case for impure comparator functions.
-/
theorem sort_via_spec {p T N Env l f fb}
    {t_eq : Cmp.Eq.hasImpl env T}
    (t_eq_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Eq.eq h![] T h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧))
    {fEmb : T.denote p → T.denote p → Bool}
    (f_spec : ∀a b, STHoare p env ⟦⟧ (fb h![a, b]) (fun r => r = fEmb a b))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::sort_via».call h![T, N, Env] h![l, f])
    (fun r => List.OrderedBy (fEmb · · = true) r.toList ∧ List.Perm l.toList r.toList) := by
  enter_decl

  let r_def := fun a b => fEmb a b = true

  -- The call to `std::array::quicksort::quicksort` is just an unconstrained function, so returns
  -- a fresh value. We can say nothing else about it.
  step_as ([λf ↦ fb]) (fun _ => [λf ↦ fb])
  · steps
    enter_decl
    steps

  steps
  any_goals exact ()

  step_as ([λf ↦ fb]) (fun _ => [λf ↦ fb] ⋆
    List.OrderedBy r_def sorted.toList ∧ List.Perm l.toList sorted.toList)

  apply STHoare.ite_intro
  any_goals intros; contradiction

  intro cond
  steps

  rename_i one_lt_n
  have zero_lt_n : 0 < N.toNat := by
    simp_all only [Bool.not_false, BitVec.ofNat_eq_ofNat]
    exact one_lt_n
  have n_eq_len : sorted.toList.length = N.toNat := by simp_all

  loop_inv nat fun i _ _ => [λf ↦ fb] ⋆ List.OrderedBy r_def (sorted.toList.take (i + 1))
  · simp only [BitVec.toNat_intCast, Int.reducePow, EuclideanDomain.zero_mod, Int.toNat_zero,
      zero_add]

    rw [List.take_add_one, List.take_zero, List.getElem?_eq_getElem (by omega)]
    apply List.OrderedBy.singleton
  · simp
  · intro i hlo hhi
    steps
    rename List.OrderedBy _ _ => pfx_ordered

    simp_all only [Bool.not_false, List.Vector.toList_length, BitVec.toNat_intCast, Int.reducePow,
      EuclideanDomain.zero_mod, Int.toNat_zero, zero_le, BitVec.toNat_ofNatLT, Int.reduceMod,
      Int.toNat_one, Nat.reducePow, Builtin.instCastTpU, BitVec.truncate_eq_setWidth,
      BitVec.setWidth_eq, BitVec.toNat_add]

    rename_i i_succ_lt_2pow
    conv => enter [4, 1, 4, 2, 1, 2, 1]; rw [Nat.mod_eq_of_lt i_succ_lt_2pow]

    generalize_proofs
    rename_i i_lt_n i_succ_lt_n
    generalize ith_def : sorted.get ⟨i, i_lt_n⟩ = ith at *
    generalize isth_def : sorted.get ⟨i + 1, i_succ_lt_n⟩ = isth at *

    have := f_spec ith isth
    steps [STHoare.callLambda_intro (hlam := this)]
    rw [List.take_succ_eq_append_getElem (by simp_all)]

    have : sorted.toList ≠ [] := by
      have : N.toNat ≠ 0 := by omega
      have : N.toNat = sorted.toList.length := by simp_all
      apply List.length_pos_iff_ne_nil.mp (by omega)

    have : List.take (i + 1) (List.Vector.toList sorted) ≠ [] := by
      rw [List.take_succ_eq_append_getElem (by simp_all)]
      apply List.append_ne_nil_of_right_ne_nil
      simp

    apply List.OrderedBy.append (h := this) (ord_pfx := pfx_ordered)

    generalize_proofs pf₁ pf₂
    have : (sorted.toList.take (i + 1)).getLast this = sorted[i] := by
      simp only [List.getLast_take, add_tsub_cancel_right]
      rw [List.getElem?_eq_getElem (by simp_all), Option.getD_some]
      apply List.Vector.toList_getElem
    rw [this, List.Vector.toList_getElem]
    unfold r_def
    simp_all only [Builtin.instCastTpU, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      BitVec.toNat_ofNatLT, BitVec.toNat_add, BitVec.toNat_intCast, Int.reducePow, Int.reduceMod,
      Int.toNat_one, Nat.reducePow, beq_true]
    rename_i v _
    rw [←ith_def, ←isth_def] at v
    assumption

  · steps [CheckShuffle.check_shuffle_spec t_eq t_eq_spec]
    rename_i ord perm _
    rw [BitVec.toNat_sub_of_le (by assumption)] at ord
    simp only [←n_eq_len, BitVec.toNat_intCast, Int.reducePow, Int.reduceMod, Int.toNat_one] at ord
    rw [Nat.sub_add_cancel (by omega)] at ord
    rw [List.take_length] at ord
    exact ⟨ord, perm⟩

  steps
  subst_vars
  assumption

/--
If it can be proven that the embedding of the comparator function is transitive, this theorem
provides a stronger bound in that it states that the output is _strictly sorted_, and not only
ordered by the provided relation.

See `sort_via_spec` for a similar theorem that does not impose this restriction.
-/
theorem sort_via_trans_spec {p T N Env l f fb}
    {t_eq : Cmp.Eq.hasImpl env T}
    (t_eq_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Eq.eq h![] T h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧))
    {fEmb : T.denote p → T.denote p → Bool}
    (fEmb_trans : Transitive (fEmb · · = true))
    (f_spec : ∀a b, STHoare p env ⟦⟧ (fb h![a, b]) (fun r => r = fEmb a b))
  : STHoare p env [λf ↦ fb]
    («std-1.0.0-beta.12::array::sort_via».call h![T, N, Env] h![l, f])
    (fun r => List.Sorted (fEmb · · = true) r.toList ∧ List.Perm l.toList r.toList) := by
  steps [sort_via_spec (t_eq := t_eq) t_eq_spec f_spec]
  constructor
  rename_i a
  rcases a with ⟨ord_by, perm⟩
  exact List.OrderedBy.trans_eq_Sorted ord_by fEmb_trans
  simp_all

/--
This theorem asserts that `std::array::sort` implements a valid sort (namely that the output is
a sorted permutation of the input) but does not make any requirements on _how_ the sort is done.

It makes no guarantees as to the computational complexity or stability of the sort, but does ensure
that the result is sorted by the provided relation and that its elements represent a valid
permutation of the input.

Do note that the function as written can only assume that the elements are pairwise ordered by the
provided comparator function. In other words, it does **not** guarantee that they are sorted unless
the comparator function is transitive. For a more strict version of this theorem, see
`sort_trans_spec`, which uses a proof of transitivity for the `Ord` implementation to assure that
the output is sorted.

This theorem is pure, as we argue that there is no sensible use-case for impure `Ord` and `Eq`
implementations for `T`.
-/
theorem sort_spec {p T N l}
    {t_eq : Cmp.Eq.hasImpl env T}
    (t_eq_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Eq.eq h![] T h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧))
    {t_ord : Cmp.Ord.hasImpl env T}
    (t_ord_emb : Tp.comparator p T)
    (t_ord_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Ord.cmp h![] T h![] h![] h![a, b])
      (fun r => r = Cmp.Ord.fromOrdering (t_ord_emb a b)))
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::array::sort».call h![T, N] h![l])
    (fun r => List.OrderedBy (Cmp.Ord.le_emb t_ord_emb · ·) r.toList
      ∧ List.Perm l.toList r.toList) := by
  enter_decl
  steps

  apply STHoare.consequence_frame
  with_unfolding_all apply sort_via_spec
  case h_ent => sl
  case q_ent => intros; sl; assumption
  any_goals assumption

  intro a b
  steps [t_ord_spec, Cmp.Ord.less_spec, Cmp.Ord.equal_spec, Cmp.Eq.ordering_eq_spec]
  any_goals exact ()

  subst_vars
  rw [Cmp.Ord.fromOrdering_inj.eq_iff] at *
  with_unfolding_all generalize toe_def : t_ord_emb a b = toe at *
  congr <;> cases toe <;> simp_all

/--
If it can be proven that the embedding of the `Ord` implementation is transitive, this theorem
provides a stronger bound in that it states that the output is _strictly sorted_, and not only
ordered by the provided relation.

See `sort_spec` for a similar theorem that does not impose this restriction.
-/
theorem sort_trans_spec {p T N l}
    {t_eq : Cmp.Eq.hasImpl env T}
    (t_eq_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Eq.eq h![] T h![] h![] h![a, b])
      (fun r : Bool => ⟦r ↔ a = b⟧))
    {t_ord : Cmp.Ord.hasImpl env T}
    (t_ord_emb : Tp.comparator p T)
    (t_ord_trans : Std.TransCmp t_ord_emb)
    (t_ord_spec : ∀a b, STHoare p env ⟦⟧ (Cmp.Ord.cmp h![] T h![] h![] h![a, b])
      (fun r => r = Cmp.Ord.fromOrdering (t_ord_emb a b)))
  : STHoare p env ⟦⟧
    («std-1.0.0-beta.12::array::sort».call h![T, N] h![l])
    (fun r => List.Sorted (Cmp.Ord.le_emb t_ord_emb · ·) r.toList
      ∧ List.Perm l.toList r.toList) := by
  steps [sort_spec (t_eq := t_eq) t_eq_spec (t_ord := t_ord) t_ord_emb t_ord_spec]
  constructor
  rename_i a
  rcases a with ⟨ord_by, perm⟩
  apply List.OrderedBy.trans_eq_Sorted ord_by (Cmp.Ord.le_emb_trans t_ord_emb t_ord_trans)
  simp_all

theorem convert_from_str_spec {p N s}
  : STHoare p env ⟦⟧
    (Convert.«from» h![.str N] (.str N) h![] h![] h![s])
    (fun r => r = s.bytes) := by
  resolve_trait
  steps
  simp_all
