import Lampe.Builtin.Basic

@[simp]
lemma Nat.dec_add_eq_self {n : Nat} {h : n ≠ 0} : n - 1 + 1 = n := by
  cases n
  contradiction
  simp

lemma Fin.n_is_non_zero {h : Fin n} : n ≠ 0 := by
  cases_type Fin
  cases n
  contradiction
  simp

lemma List.Vector.get_after_erase {idx : Nat} {vec : List.Vector α n} {h₁ h₂ h₃} :
  (List.Vector.eraseIdx ⟨idx, h₁⟩ vec).get ⟨idx, h₂⟩ = List.Vector.get vec ⟨idx + 1, h₃⟩ := by
  unfold List.Vector.get List.Vector.eraseIdx
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
        have _ : tail₁.length - 1 + 1 = tail₁.length := by simp_all [Nat.dec_add_eq_self]
        simp_all
      . aesop

@[simp]
lemma List.Vector.get_after_insert {idx : Nat} {vec : List.Vector α n} {h} :
  (List.Vector.insertIdx v ⟨idx, h⟩ vec).get ⟨idx, h⟩ = v := by
  unfold List.Vector.insertIdx List.Vector.get
  cases vec
  simp_all only [List.get_eq_getElem, Fin.coe_cast]
  apply List.get_insertIdx_self
  subst_vars
  linarith

namespace Lampe.Builtin

@[reducible]
def replaceArray' (arr : Tp.denote p (.array tp n)) (idx : Fin n.toNat) (v : Tp.denote p tp) : Tp.denote p (.array tp n) :=
  let arr' := (arr.insertIdx v ⟨idx.val + 1, by aesop⟩)
  arr'.eraseIdx ⟨idx.val, by cases idx; tauto⟩

example {p} : (replaceArray' (p := p) (n := ⟨3, by aesop⟩) (tp := .bool) ⟨[false, false, false], (by rfl)⟩ ⟨1, by tauto⟩ true).get ⟨1, by tauto⟩ = true := by rfl

@[simp]
theorem index_replaced_arr {n : U 32} {idx : Fin n.toNat} {arr} :
  (replaceArray' arr idx v').get idx = v' := by
  unfold replaceArray'
  cases em (n.toNat > 0)
  . simp_all only [gt_iff_lt, eq_mp_eq_cast]
    generalize h₁ : (List.Vector.insertIdx _ _ _) = arr₁
    cases idx
    rw [List.Vector.get_after_erase, ←h₁]
    apply List.Vector.get_after_insert
  . simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, lt_self_iff_false, dite_false]
    rename_i h
    rw [h] at idx
    apply Fin.n_is_non_zero at idx
    contradiction

/--
Defines the builtin array constructor.
-/
def mkArray := newGenericTotalPureBuiltin
  (fun (a : U 32 × Tp) => ⟨List.replicate a.1.toNat a.2, (.array a.2 a.1)⟩)
  (fun _ args => HList.toVec args (by rfl))

/--
Defines the builtin array constructor for repeated arrays
-/
def mkRepeatedArray := newGenericTotalPureBuiltin
  (fun (len, tp) => ⟨[tp], (.array tp len)⟩)
  (fun (num, _) h![val] => List.Vector.replicate num.toNat val)

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
Defines the function that converts an array to a slice.

In Noir, this corresponds to `fn as_slice(self) -> [T]` implemented for `[T; n]`.
-/
def asSlice := newGenericTotalPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .slice tp⟩)
  (fun (_, _) h![a] => a.toList)


end Lampe.Builtin
