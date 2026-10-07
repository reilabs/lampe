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
  simp_all only [List.get_eq_getElem, Fin.val_cast]
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
  . simp_all only [gt_iff_lt]
    obtain ⟨val, isLt⟩ := idx
    show (((arr.insertIdx v' ⟨val + 1, by aesop⟩).eraseIdx ⟨val, by tauto⟩).get ⟨val, isLt⟩ : _) = v'
    generalize h₁ : (List.Vector.insertIdx v' ⟨val + 1, by aesop⟩ arr) = arr₁
    rw [List.Vector.get_after_erase, ← h₁]
    · apply List.Vector.get_after_insert
    · omega
  . simp_all only [gt_iff_lt, not_lt, nonpos_iff_eq_zero]
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
Interprets a list of element values as an array of length `n`, truncating or zero-padding as
needed. An array denotes as a `List.Vector`, i.e. a list *paired with a proof* that its length
is `n`; both components are built below so that they are independent of the concrete elements.
-/
def valArray {p : Prime} (tp : Tp) (n : U 32) (vals : List (Tp.denote p tp)) :
    Tp.denote p (.array tp n) :=
  ⟨-- Reshape the input to exactly `n` elements: keep the first `n`, pad with the type's zero
   -- value if `vals` is too short. The elaborator always supplies a list of exactly the right
   -- length, so this is the identity in practice; it exists so the result is length-correct
   -- *by construction* for any input.
   vals.takeD n.toNat (Tp.zero p tp),
   -- The generic lemma `(l.takeD n d).length = n`. Because `takeD` guarantees the length for
   -- *any* list, this discharges the vector's length side-condition without ever inspecting
   -- the elements — checking a 10'000-element literal costs the same as a 1-element one,
   -- unlike proving `[a, b, c, …].length = n` by `rfl`/`decide`, which walks the whole list.
   List.takeD_length _ _ _⟩

/--
Defines the builtin constructor for arrays whose elements are all compile-time constants.

The element values are carried by the builtin itself as a (prime-generic) denoted list, rather
than as per-element expressions. The Lampe elaborator emits this builtin — with `vals` referencing
a hoisted auxiliary definition — for array literals all of whose elements are numeric literals.
This keeps both the extracted term and every proof goal mentioning the array shallow (a single
constant), in contrast to the general `mkArray` path which `letIn`-binds each element and so
produces terms whose depth grows with the array length.
-/
def mkValArray
    (arrTp : Tp)
    -- `vals` is a *function of the prime* rather than a plain list, because element values live
    -- in `Tp.denote p _`, which depends on `p` — e.g. `Field` elements are integers modulo `p`.
    -- The builtin must work at every prime, so the hoisted definition abstracts over it.
    (vals : (p : Prime) → List (Tp.denote p arrTp.arrayElem)) :=
  newGenericTotalPureBuiltin
    -- The generic-argument type is `Unit` (unlike `mkArray`, which is indexed by element count
    -- and type): the builtin is fully determined by its parameters `arrTp`/`vals`, so proof
    -- automation always instantiates it with `a := ()`. The signature takes *no runtime
    -- arguments* (`[]`) — the elements are data inside the builtin — so stepping over a call
    -- produces no per-element subgoals. The output type is recovered from the whole array type
    -- via the projections `arrayElem`/`arraySize` rather than taking element type and length
    -- as separate parameters: the elaborator can pass the one type annotation it already has,
    -- and because the projections are `@[reducible]`, `(.array tp n).arrayElem`/`.arraySize`
    -- unify with `tp`/`n` when the closing lemma from `Tactic/Steps.lean` — stated at the
    -- projected type — is matched against a goal stated at the original array type.
    (fun (_ : Unit) => ⟨[], .array arrTp.arrayElem arrTp.arraySize⟩)
    -- Evaluation: `h![]` matches the empty `HList` of runtime arguments, and the result is
    -- `valArray … (vals p)` (the prime is implicit from context), whose length side-condition
    -- is discharged generically (see `valArray`) — no proof obligation about the concrete
    -- elements ever arises.
    (fun _ h![] => valArray arrTp.arrayElem arrTp.arraySize (vals _))

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
Defines the function that converts an array to a vector.

In Noir (≥ beta.14), this corresponds to `fn as_vector(self) -> [T]` implemented for `[T; n]`.
-/
def asVector := newGenericTotalPureBuiltin
  (fun (tp, n) => ⟨[.array tp n], .vector tp⟩)
  (fun (_, _) h![a] => a.toList)

-- Deprecated alias for backward compatibility
@[deprecated asVector (since := "2025-03-19")] abbrev asSlice := @asVector

end Lampe.Builtin
