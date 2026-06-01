import «std-1.0.0-beta.14».Extracted
import Lampe
import Lampe.Crypto.Pedersen
import Lampe.Crypto.Bn254.Prime
import Stdlib.Field.Bn254
import Stdlib.EmbeddedCurveOps

/-!
# Pedersen reference vectors

Verifies our concrete `pedersenGenerator` and the
Pedersen commitment/hash composition against Aztec's published test
vectors (from `assert_pedersen` in the Noir stdlib at
`std-1.0.0-beta.14/Extracted/Hash/Mod.lean`).

Inputs are `[1, 2, ..., N]` as Fields, separator = N. Outputs are
the published Aztec curve points (for commitment) and field elements
(for hash).

The two domain-separator byte sequences (`defaultDomainBytes` and
`pedersenHashLengthBytes`) are duplicated locally to avoid depending on
the in-progress `Stdlib.Hash.Pedersen` module; the byte literals match
the ASCII encoding of `"DEFAULT_DOMAIN_SEPARATOR"` (24 bytes) and
`"pedersen_hash_length"` (20 bytes) respectively, used by Barretenberg
under the hood.
-/

namespace Tests.Pedersen

open Lampe (Fp Prime)
open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen

/-! ### Domain-separator byte vectors (local copies) -/

/-- ASCII byte vector for the literal `"DEFAULT_DOMAIN_SEPARATOR"`
(24 bytes). Used by `pedersen_commitment_with_separator` and
`pedersen_hash_with_separator`. -/
def defaultDomainBytes : List Nat :=
  [68, 69, 70, 65, 85, 76, 84, 95,    -- "DEFAULT_"
   68, 79, 77, 65, 73, 78, 95,         -- "DOMAIN_"
   83, 69, 80, 65, 82, 65, 84, 79, 82] -- "SEPARATOR"

/-- ASCII byte vector for the literal `"pedersen_hash_length"`
(20 bytes). Used by `pedersen_hash_with_separator` for the
length-slot generator. -/
def pedersenHashLengthBytes : List Nat :=
  [112, 101, 100, 101, 114, 115, 101, 110, 95,  -- "pedersen_"
   104, 97, 115, 104, 95,                       -- "hash_"
   108, 101, 110, 103, 116, 104]                 -- "length"

/-! ### BN254 instances -/

/-- BN254 scalar field prime — the field for Pedersen scalars and the
base field for Grumpkin. -/
abbrev P : Lampe.Prime := bn254Prime

/-! ### Reference functions -/

/-- Canonical limb decomposition: `f = lo + 2^128 * hi` with
`lo = f.val % 2^128`, `hi = f.val / 2^128`. This is the
deterministic decomposition produced by `from_field_unsafe` on a
canonical input. -/
def canonicalDecomp (f : Fp P) :
    Lampe.Stdlib.EmbeddedCurveOps.Scalar.denote P :=
  Lampe.Stdlib.EmbeddedCurveOps.Scalar.mk
    ((f.val % (2 ^ 128 : Nat) : Nat) : Fp P)
    ((f.val / (2 ^ 128 : Nat) : Nat) : Fp P)

/-- Deterministic Lean reference for `pedersen_commitment_with_separator`:
canonically decomposes each `input[i]` into a `Scalar`, builds the
generator at index `separator + i` via `pedersenGenerator`, and
sums up the `scalarValueNat`-scaled generators. -/
def pedersenCommitmentRef
    (input : List (Fp P)) (separator : Nat) :
    (affineCurve P).Point :=
  let pairs : List ((affineCurve P).Point) :=
    input.zipIdx.map (fun (f, i) =>
      let s := scalarValueNat (canonicalDecomp f)
      let g := pedersenGenerator (p := P) defaultDomainBytes (separator + i)
      s • g)
  pairs.foldl (· + ·) (0 : (affineCurve P).Point)

/-- Deterministic Lean reference for `pedersen_hash_with_separator`:
runs the commitment MSM, appends the length-slot term `N • lenGen`
(where `lenGen` is the index-0 generator under the
`pedersen_hash_length` domain), and returns the `x` coordinate of
the result. -/
def pedersenHashRef
    (input : List (Fp P)) (separator : Nat) :
    Fp P :=
  let N := input.length
  let commitment := pedersenCommitmentRef input separator
  let lenGen := pedersenGenerator (p := P) pedersenHashLengthBytes 0
  let total : (affineCurve P).Point := commitment + (N : ℕ) • lenGen
  match total with
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x _ _ => x

/-! ### Reference test vectors

The expected values below are taken verbatim from the `assert_pedersen`
Noir function (extracted at
`stdlib/lampe/std-1.0.0-beta.14/Extracted/Hash/Mod.lean` starting at
line 251). Negative literals are field elements expressed as their
signed representative; the `Int` → `Fp P` cast reduces them mod `p`. -/

-- N = 1

/-- pedersen_hash_with_separator<1>([1], 1) — Aztec reference. -/
example :
    pedersenHashRef [1] 1 =
      ((-9563966249275741675388072609438711537348680428347819854678797696612266004386 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<1>([1], 1) — Aztec reference. -/
example :
    pedersenCommitmentRef [1] 1 =
      .some
        ((2393473289045184898987089634332637236754766663897650125720167164137088869378 : Int) : Fp P)
        (((-7135402912423807765050323395026152633898511180575289670895350565966806597339 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 2

/-- pedersen_hash_with_separator<2>([1, 2], 2) — Aztec reference. -/
example :
    pedersenHashRef [1, 2] 2 =
      ((-4514641934080458214240751313245257091597283372119704256508270041112972328364 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<2>([1, 2], 2) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2] 2 =
      .some
        (((-1005469533000889117657666498472954572857833872027279582301287737791321798830 : Int) : Fp P))
        (((-197930408253518363600434091261593976805802346006803044607495721019065268361 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 3

/-- pedersen_hash_with_separator<3>([1, 2, 3], 3) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3] 3 =
      ((5326303462429251635333445553787815334884504473158538697533567972354818497508 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<3>([1, 2, 3], 3) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3] 3 =
      .some
        (((-7445492827528947374509602945629683494533192071041804482180938699494227714940 : Int) : Fp P))
        (((-346969586742294743999106690738565516862306986837138292504091779330690805808 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 4

/-- pedersen_hash_with_separator<4>([1..4], 4) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4] 4 =
      ((386725976317305842536127973743796063021078557104668993698335256486699462108 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<4>([1..4], 4) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4] 4 =
      .some
        ((3474050104565946163748262682994355436071725368663608454945085151569694677961 : Int) : Fp P)
        ((4969143737471383592015577254419974288705429190161323890019554309538525237268 : Int) : Fp P)
        (by native_decide) := by
  native_decide

-- N = 5

/-- pedersen_hash_with_separator<5>([1..5], 5) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5] 5 =
      ((445627510378474786942205982382342880084933256779806571759234109296077544482 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<5>([1..5], 5) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5] 5 =
      .some
        ((10552833461612204383225982278685649771700648236894998952452362214619168226089 : Int) : Fp P)
        (((-1251131729610909206337824637802607977413231765663205492654376476649374713610 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 6

/-- pedersen_hash_with_separator<6>([1..6], 6) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5, 6] 6 =
      ((10217545977856619241380062255630350521414270790482717416408002401121937565042 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<6>([1..6], 6) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5, 6] 6 =
      .some
        ((11335069702571578236117888955050736139682779524214984889155721704928197387927 : Int) : Fp P)
        (((-7733361908666485801415200275635877656445756448956549185022038133647049615622 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 7

/-- pedersen_hash_with_separator<7>([1..7], 7) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5, 6, 7] 7 =
      ((8389099894375185114295483291630893019224023442848409888108611454294869536227 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<7>([1..7], 7) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5, 6, 7] 7 =
      .some
        ((601182919381464537093882307577577658521785998356796832152269409048770009401 : Int) : Fp P)
        (((-8704984668101593449807889537070046830501821124601109099832679891796819531525 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 8

/-- pedersen_hash_with_separator<8>([1..8], 8) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5, 6, 7, 8] 8 =
      ((-364414833671337260860436705614307386127212237115043515297237560718972836517 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<8>([1..8], 8) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5, 6, 7, 8] 8 =
      .some
        ((10105395258059943854471547573391327707179901153940064586773125525172385465411 : Int) : Fp P)
        (((-7764172381957047914625405480055519449068901615240110013280942913930205438090 : Int) : Fp P))
        (by native_decide) := by
  native_decide

-- N = 9

/-- pedersen_hash_with_separator<9>([1..9], 9) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5, 6, 7, 8, 9] 9 =
      ((5694292929090063810102755351119629986122166830204542196709417013467308391399 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<9>([1..9], 9) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5, 6, 7, 8, 9] 9 =
      .some
        ((4630760469979870165820917922898436050077118370325830990580986530746633543789 : Int) : Fp P)
        ((445421188486227550820408419830973545028032672242093648088931561027838255858 : Int) : Fp P)
        (by native_decide) := by
  native_decide

-- N = 10

/-- pedersen_hash_with_separator<10>([1..10], 10) — Aztec reference. -/
example :
    pedersenHashRef [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 =
      ((-1612865150156425111011383725280441289912228955196006102547487828548180279661 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<10>([1..10], 10) — Aztec reference. -/
example :
    pedersenCommitmentRef [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] 10 =
      .some
        (((-311556882567474412576811669014419164866085063813982345701073780395111226613 : Int) : Fp P))
        (((-163948955461070038478898748306472919392980231474444415480716967232318545340 : Int) : Fp P))
        (by native_decide) := by
  native_decide

end Tests.Pedersen
