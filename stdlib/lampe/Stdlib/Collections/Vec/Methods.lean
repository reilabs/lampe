import Stdlib.Collections.Vec.Core

namespace Lampe.Stdlib.Collections.Vec

open «std-1.0.0-beta.14»

/-!
`collections::vec`

Hoare-logic specs for `Vec` methods. All proofs are `sorry`'d.
Each spec is stated in terms of `embed` and standard Lean `List` operations.
-/

theorem new_spec {p T} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::new».call h![T] h![])
      (fun r => embed r = []) := by
  sorry

theorem from_vector_spec {p T s} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::from_vector».call h![T] h![s])
      (fun r => embed r = s) := by
  sorry

theorem len_spec {p T self} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::len».call h![T] h![self])
      (fun r => r.toNat = (embed self).length) := by
  sorry

theorem get_spec {p T self index}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::collections::vec::Vec::get».call h![T] h![self, index])
      (fun r => r = (embed self)[index.toNat]'hindex) := by
  sorry

theorem set_spec {p T selfRef self index value}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::set».call h![T] h![selfRef, index, value])
      (fun _ => V selfRef ((embed self).set index.toNat value)) := by
  sorry

theorem push_spec {p T selfRef self elem} :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::push».call h![T] h![selfRef, elem])
      (fun _ => V selfRef (embed self ++ [elem])) := by
  sorry

theorem pop_spec {p T selfRef self}
    (hnonempty : embed self ≠ []) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::pop».call h![T] h![selfRef])
      (fun r =>
        V selfRef ((embed self).dropLast) ⋆
          ⟦r = (embed self).getLast hnonempty⟧) := by
  sorry

theorem insert_spec {p T selfRef self index elem}
    (hindex : index.toNat ≤ (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::insert».call h![T] h![selfRef, index, elem])
      (fun _ => V selfRef ((embed self).insertIdx index.toNat elem)) := by
  sorry

theorem remove_spec {p T selfRef self index}
    (hindex : index.toNat < (embed self).length) :
    STHoare p env
      [selfRef ↦ ⟨vecTp T, self⟩]
      («std-1.0.0-beta.14::collections::vec::Vec::remove».call h![T] h![selfRef, index])
      (fun r =>
        V selfRef ((embed self).eraseIdx index.toNat) ⋆
          ⟦r = (embed self)[index.toNat]'hindex⟧) := by
  sorry

end Lampe.Stdlib.Collections.Vec
