import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.Collections.Map

open «std-1.0.0-beta.14»

/-!
Core semantic interface for Noir `collections::map::HashMap` and `collections::map::Slot`.

We define:
- concrete representation projections for `Slot` and `HashMap`
- a semantic view (`validEntries`) that extracts the logical key-value content
- well-formedness predicates

This file intentionally contains no Hoare triples.
-/

/-! ### Slot -/

section Slot

abbrev slotTp (K V : Tp) : Tp :=
  «std-1.0.0-beta.14::collections::map::Slot».tp h![K, V]

abbrev SlotRepr (p : Prime) (K V : Tp) : Type :=
  Tp.denote p (slotTp K V)

/-- Project the key field of a `Slot`. -/
def Slot.key {p K V} (s : SlotRepr p K V) : K.denote p :=
  Builtin.indexTpl s Builtin.Member.head

/-- Project the value field of a `Slot`. -/
def Slot.value {p K V} (s : SlotRepr p K V) : V.denote p :=
  Builtin.indexTpl s Builtin.Member.head.tail

/-- Project the `_is_present` flag of a `Slot`. -/
def Slot.isPresent {p K V} (s : SlotRepr p K V) : Bool :=
  Builtin.indexTpl s Builtin.Member.head.tail.tail

/-- Project the `_is_deleted` flag of a `Slot`. -/
def Slot.isDeleted {p K V} (s : SlotRepr p K V) : Bool :=
  Builtin.indexTpl s Builtin.Member.head.tail.tail.tail

/--
A slot is *valid* when it is present and not deleted.
This matches Noir's `Slot::is_valid`: `!self._is_deleted & self._is_present`.
-/
def Slot.isValid {p K V} (s : SlotRepr p K V) : Bool :=
  !Slot.isDeleted s && Slot.isPresent s

/--
A slot is *available* when it is deleted or not present.
This matches Noir's `Slot::is_available`: `self._is_deleted | !self._is_present`.
-/
def Slot.isAvailable {p K V} (s : SlotRepr p K V) : Bool :=
  Slot.isDeleted s || !Slot.isPresent s

lemma Slot.isAvailable_eq_not_isValid {p K V} (s : SlotRepr p K V) :
    Slot.isAvailable s = !Slot.isValid s := by
  unfold Slot.isAvailable Slot.isValid
  cases Slot.isDeleted s <;> cases Slot.isPresent s <;> rfl

lemma Slot.isValid_eq_not_isAvailable {p K V} (s : SlotRepr p K V) :
    Slot.isValid s = !Slot.isAvailable s := by
  rw [Slot.isAvailable_eq_not_isValid, Bool.not_not]

/-- The key-value pair of a slot, if valid. -/
def Slot.entry {p K V} (s : SlotRepr p K V) : Option (K.denote p × V.denote p) :=
  if Slot.isValid s then some (Slot.key s, Slot.value s) else none

lemma Slot.entry_of_valid {p K V} {s : SlotRepr p K V} (h : Slot.isValid s = true) :
    Slot.entry s = some (Slot.key s, Slot.value s) := by
  unfold Slot.entry; rw [if_pos h]

lemma Slot.entry_of_not_valid {p K V} {s : SlotRepr p K V} (h : Slot.isValid s = false) :
    Slot.entry s = none := by
  unfold Slot.entry; rw [if_neg (by simp [h])]

end Slot

/-! ### HashMap -/

section HashMap

abbrev hmTp (K V : Tp) (N : U 32) (B : Tp) : Tp :=
  «std-1.0.0-beta.14::collections::map::HashMap».tp h![K, V, N, B]

abbrev HMRepr (p : Prime) (K V : Tp) (N : U 32) (B : Tp) : Type :=
  Tp.denote p (hmTp K V N B)

/-- Project the slot table of a `HashMap`. -/
def table {p K V N B} (m : HMRepr p K V N B) : List.Vector (SlotRepr p K V) N.toNat :=
  Builtin.indexTpl m Builtin.Member.head

/-- Project the `_len` field of a `HashMap`. -/
def len {p K V N B} (m : HMRepr p K V N B) : U 32 :=
  Builtin.indexTpl m Builtin.Member.head.tail

/-- Project the `_build_hasher` field of a `HashMap`. -/
def buildHasher {p K V N B} (m : HMRepr p K V N B) : B.denote p :=
  Builtin.indexTpl m Builtin.Member.head.tail.tail

/--
The list of valid entries in table order.

This is the primary semantic view of a `HashMap`: it filters the table for valid slots
and returns their key-value pairs.
-/
def validEntries {p K V N B} (m : HMRepr p K V N B) : List (K.denote p × V.denote p) :=
  (table m).toList.filterMap Slot.entry

/-- Count of valid slots in the table. -/
def validCount {p K V N B} (m : HMRepr p K V N B) : Nat :=
  (table m).toList.countP (Slot.isValid · = true)

/--
Well-formedness: the `_len` field accurately reflects the number of valid slots.
-/
def wellFormed {p K V N B} (m : HMRepr p K V N B) : Prop :=
  (len m).toNat = validCount m

/--
The load factor is not exceeded: `_len * 4 < N * 3`.
This matches the negation of the assertion condition in `assert_load_factor`.
-/
def loadFactorOk {p K V N B} (m : HMRepr p K V N B) : Prop :=
  (len m).toNat * 4 < N.toNat * 3

/-! ### Basic lemmas -/

lemma validEntries_length_eq_validCount {p K V N B} (m : HMRepr p K V N B) :
    (validEntries m).length = validCount m := by
  unfold validEntries validCount
  induction (table m).toList with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filterMap_cons, List.countP_cons]
    cases hs : Slot.isValid s
    · rw [Slot.entry_of_not_valid hs]; simp [hs, ih]
    · rw [Slot.entry_of_valid hs]; simp [hs, ih]

lemma wellFormed_iff_len_eq_entries_length {p K V N B} (m : HMRepr p K V N B) :
    wellFormed m ↔ (len m).toNat = (validEntries m).length := by
  unfold wellFormed
  rw [validEntries_length_eq_validCount]

end HashMap

end Lampe.Stdlib.Collections.Map
