import Lampe.Hoare.SepTotal

namespace Lampe.STHoare

theorem ref_intro:
    STHoare p Γ
      ⟦⟧
      (.call h![] [tp] (Tp.ref tp) (.builtin .ref) h![v])
      (fun r => [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.ref_intro (fun _ => SLP.entails_self)
  simp only [SLP.true_star]
  intro st hH r hr
  exists (Finmap.singleton r ⟨tp, v⟩ ∪ st), ∅
  apply And.intro (by simp)
  apply And.intro (by simp [Finmap.insert_eq_singleton_union])
  apply And.intro ?_ (by simp)
  exists (Finmap.singleton r ⟨tp, v⟩), st
  simp_all [SLP.singleton]

theorem readRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref] tp (.builtin .readRef) h![r])
    (fun v' => ⟦v' = v⟧ ⋆ [r ↦ ⟨tp, v⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.readRef_intro (fun _ => SLP.entails_self)
  rotate_left
  intro st
  rintro ⟨_, _, _, _, hs, _⟩
  subst_vars
  apply And.intro (by simp; rfl)
  simp only [SLP.true_star, SLP.star_assoc]
  exists (Finmap.singleton r ⟨tp, v⟩), ?_
  apply And.intro (by assumption)
  apply And.intro rfl
  apply And.intro (by simp [SLP.singleton])
  apply SLP.ent_star_top
  assumption

theorem writeRef_intro:
    STHoare p Γ
    [r ↦ ⟨tp, v⟩]
    (.call h![] [tp.ref, tp] .unit (.builtin .writeRef) h![r, v'])
    (fun _ => [r ↦ ⟨tp, v'⟩]) := by
  unfold STHoare
  intro H
  apply THoare.consequence ?_ THoare.writeRef_intro (fun _ => SLP.entails_self)
  intro st
  rintro ⟨_, _, _, _, hs, _⟩
  simp only [SLP.singleton] at hs
  subst_vars
  apply And.intro (by simp)
  simp only
  simp only [Finmap.insert_eq_singleton_union, ←Finmap.union_assoc, Finmap.union_singleton, SLP.star_assoc]
  use Finmap.singleton r ⟨tp, v'⟩, ?_
  apply And.intro (by assumption)
  apply And.intro rfl
  apply And.intro (by simp [SLP.singleton])
  apply SLP.ent_star_top
  assumption

end Lampe.STHoare
