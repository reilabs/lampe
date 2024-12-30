import Lampe.Builtin.Basic
namespace Lampe.Builtin

lemma _root_.Finmap.insert_mem_disjoint [DecidableEq α] {m₁ m₂ : Finmap fun _ : α => β} {hd : m₁.Disjoint m₂} {he : ref ∈ m₁} :
  (m₁.insert ref v).Disjoint m₂ := by
  rw [Finmap.insert_eq_singleton_union]
  have _ : ref ∉ m₂ := by aesop
  simp only [Finmap.disjoint_union_left]
  aesop

lemma Nat.dec_add_eq_self {n : Nat} {h : n ≠ 0} : n - 1 + 1 = n := by
  cases n
  contradiction
  simp

lemma Fin.n_is_non_zero {h : Fin n} : n > 0 := by
  cases_type Fin
  cases n
  contradiction
  simp

lemma Mathlib.Vector.get_after_erase {idx : Nat} {vec : Mathlib.Vector α n} {h₁ h₂ h₃} :
  (Mathlib.Vector.eraseIdx ⟨idx, h₁⟩ vec).get ⟨idx, h₂⟩ = Mathlib.Vector.get vec ⟨idx + 1, h₃⟩ := by
  unfold Mathlib.Vector.get Mathlib.Vector.eraseIdx
  cases vec
  simp_all only [Fin.cast_mk, List.get_eq_getElem]
  rename List _ => l
  rename_i P
  subst_vars
  revert idx
  induction l
  . intros
    rename Nat => idx
    unfold List.length at *
    contradiction
  . rename_i head₁ tail₁ ih
    intros idx h₁ h₂ h₃
    cases idx
    . simp_all
    . simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ]
      apply ih
      . aesop
      . simp_all only [List.length_cons, add_lt_add_iff_right, add_tsub_cancel_right]
        rw [←add_lt_add_iff_right (a := 1)]
        have _ : tail₁.length ≠ 0 := by aesop
        have ht : tail₁.length - 1 + 1 = tail₁.length := by simp_all [Nat.dec_add_eq_self]
        simp_all
      . aesop

lemma Mathlib.Vector.get_after_insert {idx : Nat} {vec : Mathlib.Vector α n} {h} :
  (Mathlib.Vector.insertNth v ⟨idx, h⟩ vec).get ⟨idx, h⟩ = v := by
  unfold Mathlib.Vector.insertNth Mathlib.Vector.get
  cases vec
  simp_all only [List.get_eq_getElem, Fin.coe_cast]
  apply List.get_insertNth_self
  subst_vars
  linarith

@[reducible]
def replaceArray' (arr : Tp.denote p (.array tp n)) (idx : Fin n.toNat) (v : Tp.denote p tp) : Tp.denote p (.array tp n) :=
  let arr' := (arr.insertNth v ⟨idx.val + 1, by aesop⟩)
  arr'.eraseIdx ⟨idx.val, by cases idx; tauto⟩

example {p} : (replaceArray' (p := p) (n := ⟨3, by aesop⟩) (tp := .bool) ⟨[false, false, false], (by rfl)⟩ ⟨1, by tauto⟩ true).get ⟨1, by tauto⟩ = true := by rfl

@[simp]
theorem index_replaced_arr {n : U 32} {idx : Fin n.toNat} {arr} :
  (replaceArray' arr idx v').get idx = v' := by
  unfold replaceArray'
  cases em (n.toNat > 0)
  . simp_all only [gt_iff_lt, eq_mp_eq_cast]
    generalize h₁ : (Mathlib.Vector.insertNth _ _ _) = arr₁
    cases idx
    rw [Mathlib.Vector.get_after_erase, ←h₁]
    apply Mathlib.Vector.get_after_insert
  . simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, dite_false]
    rename_i h
    rw [h] at idx
    apply Fin.n_is_non_zero at idx
    contradiction

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

def replaceArray := newGenericPureBuiltin
  (fun (tp, n) => ⟨[.array tp n, .u 32, tp], (.array tp n)⟩)
  (fun (_, n) h![arr, idx, v] => ⟨idx.toNat < n.toNat,
    fun h => replaceArray' arr ⟨idx.toNat, h⟩ v⟩)

end Lampe.Builtin
