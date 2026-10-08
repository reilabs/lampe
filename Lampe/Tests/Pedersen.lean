import Lampe.Crypto.Bn254.Prime
import Lampe.Crypto.Pedersen

/-!
# Pedersen reference vectors

Verifies the pure `pedersenCommitment` and `pedersenHash` functions
(`Lampe.Crypto.Pedersen`) — the exact closed
forms guaranteed by the stdlib `_spec_canonical` theorems — against
Aztec's published test vectors (from `assert_pedersen` in the Noir
stdlib, extracted at
`stdlib/lampe/std-1.0.0-beta.25/Extracted/Hash/Mod.lean` starting at
line 251).

Inputs are `[1, 2, ..., N]` as Fields, separator = N. Outputs are
the published Aztec curve points (for commitment) and field elements
(for hash). Negative literals are field elements expressed as their
signed representative; the `Int` → `Fp P` cast reduces them mod `p`.
-/

namespace Tests.Pedersen

open Lampe (Fp Prime)
open Lampe.Crypto.EmbeddedCurve
open Lampe.Crypto.Pedersen

/-- BN254 scalar field prime — the field for Pedersen scalars and the
base field for Grumpkin. -/
abbrev P : Lampe.Prime := Lampe.Crypto.Bn254.prime

/-- The test-vector input `[1, 2, ..., n]` as field elements. -/
def inputs (n : Nat) : List.Vector (Fp P) n :=
  List.Vector.ofFn (fun i : Fin n => ((i.val + 1 : Nat) : Fp P))

-- N = 1

/-- pedersen_hash_with_separator<1>([1], 1) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 1) 1 =
      ((-9563966249275741675388072609438711537348680428347819854678797696612266004386 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<1>([1], 1) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 1) 1 =
      mkPoint
        ((2393473289045184898987089634332637236754766663897650125720167164137088869378 : Int) : Fp P)
        ((-7135402912423807765050323395026152633898511180575289670895350565966806597339 : Int) : Fp P)
        false := by
  native_decide

-- N = 2

/-- pedersen_hash_with_separator<2>([1..2], 2) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 2) 2 =
      ((-4514641934080458214240751313245257091597283372119704256508270041112972328364 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<2>([1..2], 2) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 2) 2 =
      mkPoint
        ((-1005469533000889117657666498472954572857833872027279582301287737791321798830 : Int) : Fp P)
        ((-197930408253518363600434091261593976805802346006803044607495721019065268361 : Int) : Fp P)
        false := by
  native_decide

-- N = 3

/-- pedersen_hash_with_separator<3>([1..3], 3) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 3) 3 =
      ((5326303462429251635333445553787815334884504473158538697533567972354818497508 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<3>([1..3], 3) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 3) 3 =
      mkPoint
        ((-7445492827528947374509602945629683494533192071041804482180938699494227714940 : Int) : Fp P)
        ((-346969586742294743999106690738565516862306986837138292504091779330690805808 : Int) : Fp P)
        false := by
  native_decide

-- N = 4

/-- pedersen_hash_with_separator<4>([1..4], 4) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 4) 4 =
      ((386725976317305842536127973743796063021078557104668993698335256486699462108 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<4>([1..4], 4) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 4) 4 =
      mkPoint
        ((3474050104565946163748262682994355436071725368663608454945085151569694677961 : Int) : Fp P)
        ((4969143737471383592015577254419974288705429190161323890019554309538525237268 : Int) : Fp P)
        false := by
  native_decide

-- N = 5

/-- pedersen_hash_with_separator<5>([1..5], 5) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 5) 5 =
      ((445627510378474786942205982382342880084933256779806571759234109296077544482 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<5>([1..5], 5) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 5) 5 =
      mkPoint
        ((10552833461612204383225982278685649771700648236894998952452362214619168226089 : Int) : Fp P)
        ((-1251131729610909206337824637802607977413231765663205492654376476649374713610 : Int) : Fp P)
        false := by
  native_decide

-- N = 6

/-- pedersen_hash_with_separator<6>([1..6], 6) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 6) 6 =
      ((10217545977856619241380062255630350521414270790482717416408002401121937565042 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<6>([1..6], 6) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 6) 6 =
      mkPoint
        ((11335069702571578236117888955050736139682779524214984889155721704928197387927 : Int) : Fp P)
        ((-7733361908666485801415200275635877656445756448956549185022038133647049615622 : Int) : Fp P)
        false := by
  native_decide

-- N = 7

/-- pedersen_hash_with_separator<7>([1..7], 7) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 7) 7 =
      ((8389099894375185114295483291630893019224023442848409888108611454294869536227 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<7>([1..7], 7) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 7) 7 =
      mkPoint
        ((601182919381464537093882307577577658521785998356796832152269409048770009401 : Int) : Fp P)
        ((-8704984668101593449807889537070046830501821124601109099832679891796819531525 : Int) : Fp P)
        false := by
  native_decide

-- N = 8

/-- pedersen_hash_with_separator<8>([1..8], 8) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 8) 8 =
      ((-364414833671337260860436705614307386127212237115043515297237560718972836517 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<8>([1..8], 8) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 8) 8 =
      mkPoint
        ((10105395258059943854471547573391327707179901153940064586773125525172385465411 : Int) : Fp P)
        ((-7764172381957047914625405480055519449068901615240110013280942913930205438090 : Int) : Fp P)
        false := by
  native_decide

-- N = 9

/-- pedersen_hash_with_separator<9>([1..9], 9) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 9) 9 =
      ((5694292929090063810102755351119629986122166830204542196709417013467308391399 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<9>([1..9], 9) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 9) 9 =
      mkPoint
        ((4630760469979870165820917922898436050077118370325830990580986530746633543789 : Int) : Fp P)
        ((445421188486227550820408419830973545028032672242093648088931561027838255858 : Int) : Fp P)
        false := by
  native_decide

-- N = 10

/-- pedersen_hash_with_separator<10>([1..10], 10) — Aztec reference. -/
example :
    pedersenHash P defaultDomainBytes (inputs 10) 10 =
      ((-1612865150156425111011383725280441289912228955196006102547487828548180279661 : Int) : Fp P) := by
  native_decide

/-- pedersen_commitment_with_separator<10>([1..10], 10) — Aztec reference. -/
example :
    pedersenCommitment P defaultDomainBytes (inputs 10) 10 =
      mkPoint
        ((-311556882567474412576811669014419164866085063813982345701073780395111226613 : Int) : Fp P)
        ((-163948955461070038478898748306472919392980231474444415480716967232318545340 : Int) : Fp P)
        false := by
  native_decide

end Tests.Pedersen
