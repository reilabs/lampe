import Lampe.Builtin.Basic
namespace Lampe.Builtin

/--
For a prime `p`, a field element `a : Fp p`, and a bit size `w : U 32`,
this builtin evaluates to `()` if and only if `a < 2^w`, i.e., it can be represented by `w` bits.
Otherwise, an exception is thrown.

In Noir, this builtin corresponds to `fn __assert_max_bit_size(self, bit_size: u32)` implemented
for `Field`.
-/
def applyRangeConstraint := newPureBuiltin
  ⟨[.field, (.u 32)], .unit⟩
  (fun h![a, w] => ⟨a.val < 2^w.toNat,
    fun _ => ()⟩)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the number of bits of `p`.
We assume `log p + 1 < 2^64`, i.e., `p`'s size can be represented by a uint of bit-size `64`.
Otherwise, this builtin throws an exception.

In Noir, this builtin corresponds to `fn modulus_num_bits() -> u64` implemented for `Field`.
-/
def fModNumBits := newPureBuiltin
  ⟨[.field], (.u 64)⟩
  (@fun p h![_] => ⟨numBits p.natVal < 2^64,
    fun _ => numBits p.natVal⟩)

def modulus_bits_be (p : Prime) : List (U 1) :=
  (RadixVec.toDigitsBE' 2 p.natVal).map fun d =>
    BitVec.ofNatLT d.val d.prop

def modulus_bits_le (p : Prime) : List (U 1) :=
  (RadixVec.toDigitsLE' 2 p.natVal).map fun d =>
    BitVec.ofNatLT d.val d.prop

def modulus_bytes_be (p : Prime) : List (U 8) :=
  (RadixVec.toDigitsBE' R256 p.natVal).map fun d =>
    BitVec.ofNatLT d.val d.prop

def modulus_bytes_le (p : Prime) : List (U 8) :=
  (RadixVec.toDigitsLE' R256 p.natVal).map fun d =>
    BitVec.ofNatLT d.val d.prop

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bits() -> [u1]` implemented for `Field`.
-/
def fModLeBits := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 1))⟩
  (@fun p h![_] => modulus_bits_le p)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bits() -> [u1]` implemented for `Field`.
-/
def fModBeBits := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 1))⟩
  (@fun p h![_] => modulus_bits_be p)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the byte representation of `p` in little-endian format.

In Noir, this builtin corresponds to `fn modulus_le_bytes() -> [u8]` implemented for `Field`.
-/
def fModLeBytes := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 8))⟩
  (@fun p h![_] => modulus_bytes_le p)

/--
For a prime `p`, a field element `a : Fp p`, this builtin evaluates to the bit representation of `p` in big-endian format.

In Noir, this builtin corresponds to `fn modulus_be_bytes() -> [u8]` implemented for `Field`.
-/
def fModBeBytes := newTotalPureBuiltin
  ⟨[.field], (.slice (.u 8))⟩
  (@fun p h![_] => modulus_bytes_be p)

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
  (fun {p} h![] => modulus_bits_le p)

/--
Represents the builtin that returns the bit representation of the modulus of a field in
big-endian format.
-/
def modulusBeBits : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 1))⟩
  (fun {p} h![] => modulus_bits_be p)

/--
Represents the builtin that returns the byte representation of the modulus of a field in
little-endian format.
-/
def modulusLeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 8))⟩
  (fun {p} h![] => modulus_bytes_le p)

/--
Represents the builtin that returns the byte representation of the modulus of a field in
big-endian format.
-/
def modulusBeBytes : Builtin := newTotalPureBuiltin
  ⟨[], (.slice (.u 8))⟩
  (fun {p} h![] => modulus_bytes_be p)

/--
Represents the builtin that returns the number of bits in the modulus of a field.
-/
def modulusNumBits : Builtin := newTotalPureBuiltin
  ⟨[], (.u 64)⟩
  -- Note: We could use the `log2` definition but this is easier to reason about.
  (fun {p} h![] => numBits p.natVal)

/--
Represents the builtin that converts a field element to its bit representation in little-endian format.

Fails if `f ≥ 2^s`.
-/
def toLeBits : Builtin := newGenericBuiltin
  (fun s => ([.field], .array (.u 1) s))
  fun _ h![f] output =>
    f = RadixVec.ofDigitsLE (r := 2) (output.map BitVec.toFin)

/--
Represents the builtin that converts a field element to its bit representation in big-endian format.

Fails if `f ≥ 2^s`.
-/
def toBeBits : Builtin := newGenericBuiltin
  (fun s => ([.field], .array (.u 1) s))
  fun _ h![f] output =>
    f = RadixVec.ofDigitsBE (r := 2) (output.map BitVec.toFin)

/--
Represents the builtin that converts a field element to its radix representation in little-endian
format.

Fails if `r ≤ 1` or `f ≥ 2^s`.
-/
def toLeRadix : Builtin := newGenericBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  fun _ h![f, r] output =>
    f = RadixVec.ofLimbsLE r.toNat (output.map BitVec.toNat)

/--
Represents the builtin that converts a field element to its radix representation in big-endian
format.

Fails if `r ≤ 1` or `f ≥ 2^s`.
-/
def toBeRadix : Builtin := newGenericBuiltin
  (fun s => ([.field, .u 32], .array (.u 8) s))
  fun _ h![f, r] output =>
    f = RadixVec.ofLimbsBE r.toNat (output.map BitVec.toNat)

end Lampe.Builtin
