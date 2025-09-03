import «std-1.0.0-beta.11».Extracted.Slice
import «std-1.0.0-beta.11».Extracted.«std-1.0.0-beta.11»
import Lampe

namespace Lampe
namespace Stdlib

export «std-1.0.0-beta.11».Extracted (
  «std::slice::append»
  «std::slice::as_array»
  «std::slice::map»
  «std::slice::mapi»
  «std::slice::for_each»
  «std::slice::for_eachi»
  «std::slice::fold»
  «std::slice::reduce»
  «std::slice::filter»
  «std::slice::join»
  «std::slice::all»
  «std::slice::any»
  Slice.env
)

open «std-1.0.0-beta.11».Extracted

set_option maxRecDepth 10000

namespace Slice

lemma for_each_inv {T Env p f fb l}
    (Inv: List (Tp.denote p T) → SLP (State p))
    (h_inv: ∀(lp: List (Tp.denote p T)) (e: T.denote p), ((lp ++ [e]) <+: l) → STHoare p env (Inv lp) (fb h![e]) (fun _ => Inv (lp ++ [e]))):
    STHoare p env (Inv [] ⋆ [λf ↦ fb]) ((«std::slice::for_each».call h![T, Env] h![l, f])) (fun _ => Inv l ⋆ [λf ↦ fb]) := by
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

lemma slice_map_inv {T U Env p f fb l}
    (Inv: List (Tp.denote p T) → List (Tp.denote p U) → SLP (State p))
    (h_inv: ∀(ip: List (Tp.denote p T)) (rp: List (Tp.denote p U)) (e: T.denote p), ((ip ++ [e]) <+: l) → STHoare p env (Inv ip rp) (fb h![e]) (fun r => Inv (ip ++ [e]) (rp ++ [r]))):
    STHoare p env (Inv [] [] ⋆ [λf ↦ fb]) ((«std::slice::map».call h![T, U, Env] h![l, f])) (fun v => Inv l v ⋆ [λf ↦ fb]) := by
  enter_decl
  steps
  step_as ([ret ↦ ⟨U.slice, []⟩] ⋆ [λf ↦ fb] ⋆ Inv [] []) (fun _ => ∃∃v, [ret ↦ ⟨U.slice, v⟩] ⋆ [λf ↦ fb] ⋆ Inv l v)
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

lemma slice_pure_map {T U Env p f fb func l}
    (h_pure : ∀x, STHoare p env ⟦⟧ (fb h![x]) (fun r => r = func x)):
    STHoare p env [λf ↦ fb] ((«std::slice::map».call h![T, U, Env] h![l, f])) (fun v => v = l.map func) := by
  steps [slice_map_inv (Inv := fun i o => o = i.map func)]
  · rfl
  · assumption
  · intros; steps [h_pure]; simp_all
