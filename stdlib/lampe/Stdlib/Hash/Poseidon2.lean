import «std-1.0.0-beta.14».Extracted
import Lampe

namespace Lampe.Stdlib.Hash.Poseidon2

open «std-1.0.0-beta.14»

set_option Lampe.pp.Expr true
set_option Lampe.pp.STHoare true

/-- The sponge rate (number of absorbed elements per permutation call). -/
abbrev RATE := «std-1.0.0-beta.14::hash::poseidon2::RATE»

theorem rate_spec {p} :
    STHoare p env ⟦⟧
      (RATE.call h![] h![])
      (fun r => r = 3#32) := by
  enter_decl
  steps
  rename_i hrate
  simpa using hrate

namespace Sponge

/-- A useful shorthand for the type of the Poseidon2 sponge. -/
@[reducible]
def type := «std-1.0.0-beta.14::hash::poseidon2::Poseidon2».tp h![]

/-- A useful shorthand for declaring the type of values of the Poseidon2 sponge. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

/-- Build a sponge value from its component fields. -/
@[reducible]
def mk {p}
    (cache : List.Vector (Fp p) 3)
    (state : List.Vector (Fp p) 4)
    (cacheSize : U 32)
    (squeezeMode : Bool) : Sponge.denote p :=
  (cache, state, cacheSize, squeezeMode, ())

def cache {p} (self : Sponge.denote p) : List.Vector (Fp p) 3 := self.1
def state {p} (self : Sponge.denote p) : List.Vector (Fp p) 4 := self.2.1
def cacheSize {p} (self : Sponge.denote p) : U 32 := self.2.2.1
def squeezeMode {p} (self : Sponge.denote p) : Bool := self.2.2.2.1

end Sponge

namespace Hasher

/-- A useful shorthand for the type of the Poseidon2 hasher. -/
@[reducible]
def type := «std-1.0.0-beta.14::hash::poseidon2::Poseidon2Hasher».tp h![]

/-- A useful shorthand for declaring the type of values of the Poseidon2 hasher. -/
@[reducible]
def denote (p : Prime) := Tp.denote p type

/-- Build a hasher value from its underlying state. -/
@[reducible]
def mk {p} (state : List (Fp p)) : Hasher.denote p := (state, ())

def state {p} (self : Hasher.denote p) : List (Fp p) := self.1

end Hasher

/-- `Poseidon2::new` returns a sponge with zeroed cache, state with `state[RATE] = iv` and
zeroes elsewhere, zero `cache_size`, and `squeeze_mode = false`. -/
theorem new_spec {p} (iv : Fp p) :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::hash::poseidon2::Poseidon2::new».call h![] h![iv])
      (fun r => r = Sponge.mk
        (0 ::ᵥ 0 ::ᵥ 0 ::ᵥ List.Vector.replicate 0 0)
        (0 ::ᵥ 0 ::ᵥ 0 ::ᵥ iv ::ᵥ List.Vector.replicate 0 0)
        0#32
        false) := by
  enter_decl
  steps [rate_spec]
  simp_all only [Sponge.mk, Lens.modify, Lens.get, Access.modify, Access.get,
    Builtin.indexTpl, Builtin.replaceTuple', HList.toTuple, Option.bind_eq_bind,
    Option.bind_some, Option.bind_fun_some, Option.get_some, ↓reduceDIte,
    BitVec.toNat_ofNat]
  rfl

/-- `Default::default` for `Poseidon2Hasher` produces a hasher with empty state. -/
theorem hasher_default_spec {p} :
    STHoare p env ⟦⟧
      («std-1.0.0-beta.14::default::Default».default h![] Hasher.type h![] h![] h![])
      (fun r => r = Hasher.mk []) := by
  resolve_trait
  steps
  simp_all

end Lampe.Stdlib.Hash.Poseidon2
