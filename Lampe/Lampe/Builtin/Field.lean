import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
For a prime `p`, a field element `a : Fp p`, and a bit size `w : U 32`,
this builtin evaluates to `()` if and only if `a < 2^w`, i.e., it can be represented by `w` bits.
Otherwise, an exception is thrown.

In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented for `Field`.
-/
def fApplyRangeConstraint := newPureBuiltin
  ⟨[.field, (.u 32)], .unit⟩
  (fun h![a, w] => ⟨a.val < 2^w.toNat,
    fun _ => ()⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the number of bits of `p`.
We asdecomposeWithRadix `log p + 1 < 2^64`, i.e., `p`'s size can be represented by a uint of bit-size `64`.
Otherwise, this builtin throws an exception.

In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits := newPureBuiltin
  ⟨[.field], (.u 64)⟩
  (@fun p h![_] => ⟨numBits p.val < 2^64,
    fun _ => numBits p.val⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 1))⟩
  (@fun p h![_] => decomposeToRadix 2 p.val (by tauto))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 1))⟩
  (@fun p h![_] => .reverse (decomposeToRadix 2 p.val (by tauto)))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the byte representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 8))⟩
  (@fun p h![_] => decomposeToRadix 256 p.val (by linarith))

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 8))⟩
  (@fun p h![_] => .reverse (decomposeToRadix 256 p.val (by linarith)))

/--
Represents the builtin that converts a field element to an unsigned integer.

Assume a B-bit integer. Noir's semantics for this conversion take the field element and truncate it
to its least-significant B bits. This value is then interpreted as the unsigned integer element. In
Noir, this builtin corresponds to `fn from_field(a: Field) -> T` implemented for uints of bit size
`s`.
 -/
def uFromField := newGenericTotalPureBuiltin
  (fun s => ⟨[.field], (.u s)⟩)
  (fun s h![f] => BitVec.ofNat s f.val)

/--
Represents the builtin that converts a field element to an integer.

Assume a B-bit integer. Noir's semantics for this conversion take the field element and truncate it
to its least-significant B bits. This value is then interpreted as the signed integer element. In
Noir, this builtin corresponds to `fn from_field(a: Field) -> T` implemented for ints of bit size
`s`.
-/
def iFromField := newGenericTotalPureBuiltin
  (fun s => ⟨[.field], (.i s)⟩)
  (fun s h![f] => BitVec.ofNat s f.val)

/--
Represents the builtin that converts an unsigned integer into a field element.

Noir's semantics for this conversion take the unsigned integer and zero-extend it up to the size of
the field. We do this by taking our unsigned int as an arbitrary `i ∈ ℤ` and then convert this to a
field element by zero extending. In Noir, this builtin corresponds to `fn as_field(self) -> Field`
implemented for uints of bit size `s`.

Integers are also internally represented as field elements with an additional restriction that all
integer widths `X` are defined such that `iX::MAX < p`, the field prime. This means that we can
unconditionally perform this conversion without care for larger values. To ensure totality, we wrap
when converting, as that case should never be encountered.
-/
def uAsField := newGenericTotalPureBuiltin
  (fun s => ⟨[.u s], (.field)⟩)
  -- Here we rely on the fact that casting our BitVec to a Nat 'implicitly' performs sign extension.
  -- It is not truly sign-extending as that has no semantic meaning in ℕ, but we get the correct
  -- semantics for our operation by doing so. We then rely on a coercion from ℕ to our field, the
  -- source of which can be viewed with `set_option trace.Meta.synthInstance`.
  (fun _ h![a] => a.toNat)

/--
Represents the builtin that converts a signed integer into a field element.

Noir's semantics for this conversion take the signed integer and zero-extend it up to the size of
the field. We do this by taking our signed int as an arbitrary `i ∈ ℤ` and then convert this to a
field element by zero extending. In Noir, this builtin corresponds to `fn as_field(self) -> Field`
implemented for uints of bit size `s`.

Integers are also internally represented as field elements with an additional restriction that all
integer widths `X` are defined such that `iX::MAX < p`, the field prime. This means that we can
unconditionally perform this conversion without care for larger values. To ensure totality, we wrap
when converting, as that case should never be encountered.
-/
def iAsField := newGenericTotalPureBuiltin
  (fun s => ⟨[.i s], (.field)⟩)
  -- Here we rely on the fact that casting our BitVec to a Nat 'implicitly' performs sign extension.
  -- It is not truly sign-extending as that has no semantic meaning in ℕ, but we get the correct
  -- semantics for our operation by doing so. We then rely on a coercion from ℕ to our field, the
  -- source of which can be viewed with `set_option trace.Meta.synthInstance`.
  (fun _ h![a] => a.toNat)

/--
Represents the builtin that returns the bit representation of the modulus of a field in
little-endian format.
-/
def modulusLeBits : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 1))⟩
  (fun {p} h![] => decomposeToRadix 2 p.val (by tauto))

/--
Represents the builtin that returns the bit representation of the modulus of a field in
big-endian format.
-/
def modulusBeBits : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 1))⟩
  (fun {p} h![] => .reverse (decomposeToRadix 2 p.val (by tauto)))

/--
Represents the builtin that returns the byte representation of the modulus of a field in
little-endian format.
-/
def modulusLeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 8))⟩
  (fun {p} h![] => decomposeToRadix 256 p.val (by linarith))

/--
Represents the builtin that returns the byte representation of the modulus of a field in
big-endian format.
-/
def modulusBeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 8))⟩
  (fun {p} h![] => .reverse (decomposeToRadix 256 p.val (by linarith)))

/--
Represents the builtin that returns the number of bits in the modulus of a field.
-/
def modulusNumBits : Builtin := newTotalPureBuiltin
  ⟨[], (.u 64)⟩
  -- Note: We could use the `log2` definition but this is easier to reason about.
  (fun {p} h![] => decomposeToRadix 2 p.val (by tauto) |>.length)

/--
Represents the builtin that converts a field element to its bit representation in little-endian
format.
-/
def toLeBits : Builtin := newGenericTotalPureBuiltin
  (fun s => ([.field], .array (.u 1) s))
  (fun s h![f] => ⟨
    decomposeToRadix 2 f.val (by linarith) |>.takeD s.toNat 0,
    by simp only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
      BitVec.ofNat_eq_ofNat, List.takeD_length]
    ⟩)

/--
Represents the builtin that converts a field element to its bit representation in big-endian format.
-/
def toBeBits : Builtin := newGenericTotalPureBuiltin
  (fun s => ([.field], .array (.u 1) s))
  (fun s h![f] => ⟨
    .reverse $ decomposeToRadix 2 f.val (by linarith) |>.takeD s.toNat 0,
    by simp only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
      BitVec.ofNat_eq_ofNat, List.length_reverse, List.takeD_length]
    ⟩)

/--
Represents the builtin that converts a field element to its radix representation in little-endian
format.
-/
def toLeRadix : Builtin := newGenericPureBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  (fun s h![f, r] => ⟨1 < r,
    fun h => ⟨
      decomposeToRadix r.toNat f.val (by
        simp only [BitVec.lt_def] at h
        exact h
      ) |>.takeD s.toNat 0,
      by
        simp only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
          BitVec.ofNat_eq_ofNat, List.takeD_length]
    ⟩⟩)

/--
Represents the builtin that converts a field element to its radix representation in big-endian
format.
-/
def toBeRadix : Builtin := newGenericPureBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  (fun s h![f, r] => ⟨1 < r,
    fun h => ⟨
      .reverse $ decomposeToRadix r.toNat f.val (by
        simp only [BitVec.lt_def] at h
        exact h
      ) |>.takeD s.toNat 0,
      by
        simp only [BitVec.natCast_eq_ofNat, List.pure_def, List.bind_eq_flatMap,
          BitVec.ofNat_eq_ofNat, List.length_reverse, List.takeD_length]
    ⟩⟩)

end Lampe.Builtin
