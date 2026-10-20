import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
The (source, target) type pairs that the cast builtin supports.

Each pair has exactly one cast function, `CastTp.cast` below. A pair is supported if one of
these constructors applies; `refl` covers casting a type to itself.
-/
inductive CastPair : Tp → Tp → Prop
| refl : CastPair tp tp
| ui : CastPair (.u s₁) (.i s₂)
| iu : CastPair (.i s₁) (.u s₂)
| uu : CastPair (.u s₁) (.u s₂)
| ii : CastPair (.i s₁) (.i s₂)
| uf : CastPair (.u s) .field
| if_ : CastPair (.i s) .field
| fu : CastPair .field (.u s)
| fi : CastPair .field (.i s)
| bu : CastPair .bool (.u s)
| ub : CastPair (.u s) .bool
| ib : CastPair (.i s) .bool
| fb : CastPair .field .bool
| bi : CastPair .bool (.i s)
| bf : CastPair .bool .field

/--
Represents the Noir types that can be casted to each other.

This is a proposition. Every instance of it is equal to every other, so the value of a cast
depends only on the source type, the target type and the input. (Before this change the class
carried the cast function as data, and a derivation of the cast builtin could supply any
function through a hand-made instance.)
-/
class CastTp (tp tp' : Tp) : Prop where
  supported : CastPair tp tp'

/--
The one cast function for each supported (source, target) pair. The branches keep the functions
of the former instances. For a pair that two former instances covered (for example `u32` to
`u32`), the branch keeps the instance that type class resolution selected, the later one.
-/
def CastTp.cast {tp tp' : Tp} [CastTp tp tp'] {p : Prime} (a : Tp.denote p tp) : Tp.denote p tp' :=
  match tp, tp', a with
  | .u _, .i s₂, a => a.zeroExtend s₂
  | .i _, .u s₂, a => a.zeroExtend s₂
  | .u _, .u s₂, a => a.zeroExtend s₂
  | .i _, .i s₂, a => a.signExtend s₂
  | .u _, .field, a => a.toNat
  | .i _, .field, a => a.toNat
  | .field, .u _, a => a.val
  | .field, .i _, a => a.val
  | .bool, .u _, a => if a then 1 else 0
  | .u _, .bool, a => a ≠ 0
  | .i _, .bool, a => a ≠ 0
  | .field, .bool, a => a ≠ 0
  | .bool, .i _, a => if a then 1 else 0
  | .bool, .field, a => if a then 1 else 0
  | .field, .field, a => a
  | .bool, .bool, a => a
  | tp, tp', a => if h : tp = tp' then h ▸ a else Tp.zero p tp'

attribute [simp] CastTp.cast

/--
A self-cast is the identity for every type. Before `CastTp` became a proposition this held by
`rfl` through the `tp → tp` instance; now the integer branches need `setWidth_eq` and
`signExtend_eq`, and every other type reaches the default branch with `tp = tp'`.
-/
@[simp]
theorem CastTp.cast_self {tp : Tp} [CastTp tp tp] {p : Prime} (a : Tp.denote p tp) :
    CastTp.cast a = a := by
  cases tp <;> simp [CastTp.cast]

instance : CastTp tp tp := ⟨.refl⟩
instance : CastTp (.u s₁) (.i s₂) := ⟨.ui⟩
instance : CastTp (.i s₁) (.u s₂) := ⟨.iu⟩
instance : CastTp (.u s₁) (.u s₂) := ⟨.uu⟩
instance : CastTp (.i s₁) (.i s₂) := ⟨.ii⟩
instance : CastTp (.u s) (.field) := ⟨.uf⟩
instance : CastTp (.i s) (.field) := ⟨.if_⟩
instance : CastTp (.field) (.u s) := ⟨.fu⟩
instance : CastTp (.field) (.i s) := ⟨.fi⟩
instance : CastTp (.bool) (.u s) := ⟨.bu⟩
instance : CastTp (.u s) (.bool) := ⟨.ub⟩
instance : CastTp (.i s) (.bool) := ⟨.ib⟩
instance : CastTp (.field) (.bool) := ⟨.fb⟩
instance : CastTp (.bool) (.i s) := ⟨.bi⟩
instance : CastTp (.bool) (.field) := ⟨.bf⟩

inductive castOmni : Omni where
| ok {P st tp tp' v Q} [CastTp tp tp'] :
  Q (some (st, CastTp.cast v)) → castOmni P st [tp] tp' h![v] Q

def cast : Builtin := {
  omni := castOmni
  conseq := by
    unfold omni_conseq
    intros
    cases_type castOmni
    . apply castOmni.ok;
      simp_all
  frame := by
    unfold omni_frame
    intros
    cases_type castOmni
    . apply castOmni.ok
      . constructor <;> tauto
}

/-- The cast builtin is deterministic: every derivation returns `CastTp.cast v` in the input
state. -/
theorem castOmni_inv {P st tp tp' v Q} (h : castOmni P st [tp] tp' h![v] Q) :
    ∃ _ : CastTp tp tp', Q (some (st, CastTp.cast v)) := by
  cases h with
  | ok hq => exact ⟨_, hq⟩

end Lampe.Builtin
