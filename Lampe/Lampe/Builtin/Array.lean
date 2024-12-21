import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
Defines the builtin array constructor.
-/
def mkArray (n : U 32) := newGenericPureBuiltin
  (fun (argTps, tp) => ⟨argTps, (.array tp n)⟩)
  (fun (argTps, tp) args => ⟨argTps = List.replicate n.toNat tp,
    fun h => HList.toVec args h⟩)

/--
Defines the indexing of a array `l : Array tp n` with `i : U 32`
We make the following assumptions:
- If `i < n`, then the builtin returns `l[i] : Tp.denote tp`
- Else (out of bounds access), an exception is thrown.

In Noir, this builtin corresponds to `T[i]` for `T: [T; n]` and `i: uint32`.
-/
def arrayIndex := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n, .u 32], tp⟩)
  (fun (_, n) h![l, i] => ⟨i.toNat < n.toNat,
    fun h => l.get (Fin.mk i.toNat h)⟩)

/--
Defines the function that evaluates to an array's length `n`.
This builtin evaluates to an `U 32`. Hence, we assume that `n < 2^32`.

In Noir, this corresponds to `fn len(self) -> u32` implemented for `[_; n]`.
-/
def arrayLen := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .u 32⟩)
  (fun (_, _) h![a] => ⟨a.length < 2^32,
    fun _ => a.length⟩)

/--
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def arrayAsSlice := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .slice tp⟩)
  (fun (_, _) h![a] => ⟨True,
    fun _ => a.toList⟩)

lemma _root_.Finmap.insert_mem_disjoint [DecidableEq α] {m₁ m₂ : Finmap fun _ : α => β} {hd : m₁.Disjoint m₂} {he : ref ∈ m₁} :
  (m₁.insert ref v).Disjoint m₂ := by
  rw [Finmap.insert_eq_singleton_union]
  have _ : ref ∉ m₂ := by aesop
  simp only [Finmap.disjoint_union_left]
  aesop


lemma vector_eq_tp_denote_array (h : n.toNat > 0) : Mathlib.Vector (Tp.denote p tp) (BitVec.toNat n - 1 + 1) = Tp.denote p (.array tp n) := by
  have _ : n.toNat ≠ 0 := by aesop
  have _ : n.toNat - 1 + 1 = n.toNat := by
    generalize (n.toNat) = n' at *
    cases n'
    contradiction
    aesop
  tauto

def replaceArr (h : n.toNat > 0) (arr : Tp.denote p (.array tp n)) (idx : Fin n.toNat) (v : Tp.denote p tp) : Tp.denote p (.array tp n) :=
  (vector_eq_tp_denote_array h) ▸ ((arr.eraseIdx idx).insertNth v idx)

example {p} : (replaceArr (p := p) (n := ⟨3, by aesop⟩) (tp := .bool) (by tauto) ⟨[false, false, false], (by rfl)⟩ ⟨1, (by tauto)⟩ true).get ⟨1, by tauto⟩ = true := by rfl

inductive arrayWriteIndexOmni : Omni where
| ok {p st tp n} {arr : Tp.denote p $ .array tp n} {v : Tp.denote p tp} {Q} :
  (_ : st.lookup ref = some ⟨.array tp n, arr⟩ ∧ n.toNat > 0 ∧ idx.toNat < n.toNat) →
  Q (some (st.insert ref ⟨.array tp n, replaceArr (by tauto) arr ⟨idx.toNat, (by tauto)⟩ v⟩, ())) →
  arrayWriteIndexOmni p st [.ref $ (.array tp n), .u 32, tp] .unit h![ref, idx, v] Q
| err {p st tp n} {arr : Tp.denote p $ .array tp n} {v : Tp.denote p tp} {Q} :
  (st.lookup ref = some ⟨.array tp n, arr⟩ ∧ idx.toNat ≥ n.toNat) →
  Q none →
  arrayWriteIndexOmni p st [.ref $ (.array tp n), .u 32, tp] .unit h![ref, idx, v] Q

def arrayWriteIndex : Builtin := {
  omni := arrayWriteIndexOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type arrayWriteIndexOmni
    . apply arrayWriteIndexOmni.ok <;> aesop
    . apply arrayWriteIndexOmni.err <;> tauto
  frame := by
      unfold omni_frame
      intros
      rename_i p st₁ st₂ hd outTp args Q _ hd
      cases_type arrayWriteIndexOmni
      rename_i ref idx tp n arr v Q h' hQ
      generalize h₃ : (Finmap.insert ref _ _) = st₃ at *
      . apply arrayWriteIndexOmni.ok
        . exists st₃, st₂
          apply And.intro
          . simp only [LawfulHeap.disjoint]
            rw [←h₃]
            apply Finmap.insert_mem_disjoint <;> tauto
            apply Finmap.mem_of_lookup_eq_some <;> tauto
          apply And.intro <;> try simp_all
          . rw [Finmap.insert_union]
            rw [h₃]
            apply And.intro
            rw [Finmap.lookup_union_left]
            tauto
            apply Finmap.mem_of_lookup_eq_some
            tauto
            tauto
      . apply arrayWriteIndexOmni.err
        rw [Finmap.lookup_union_left]
        tauto
        rename_i h
        apply Finmap.mem_of_lookup_eq_some h.left
        tauto
}

end Lampe.Builtin
