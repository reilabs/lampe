import Lampe
import Lampe.Crypto.Poseidon2

namespace Tests.Poseidon2

open Lampe.Crypto.Poseidon2
open Lampe.Crypto.Poseidon2.BN254T4

def testParams : Params Nat where
  rate := 3
  width := 4
  rate_pos := by decide
  rate_lt_width := by decide
  permute := id

example :
    Sponge.hashWithIV? testParams [1, 2, 3] 3 false 0 = some 1 := by
  rfl

example :
    Sponge.hashWithIV? testParams [1, 2, 0] 2 true 0 = some 1 := by
  rfl

example :
    Sponge.hashWithIV? testParams [1, 2, 3, 4] 4 false 0 = some 5 := by
  rfl

namespace BN254Vectors

-- Concrete BN254/T4 reference vectors for the Noir/TACEO validation path.

abbrev Fr := ZMod scalarModulus

def vals (state : List.Vector Fr 4) : List Nat :=
  state.toList.map ZMod.val

def val? : Option Fr → Option Nat :=
  Option.map ZMod.val

example :
    vals (permutation (vec4 (c 0) (c 1) (c 2) (c 3) : List.Vector Fr 4)) =
      [ 786823568102245344938517132468097745676732687098822989626730198331658606391
      , 16105493617470833344375945651585194737369509580406730765188791202038211593826
      , 2169165722086073256768101917994796590773204847633762971322389403847680713675
      , 20837792685223053096472825292260687493226094382304778455120670180090619921530
      ] := by
  native_decide

example :
    vals (permutation (vec4 (c 1) (c 2) (c 3) (c 4) : List.Vector Fr 4)) =
      [ 15505005361706012551741834895355031099510014664842462842053262257331543442865
      , 15540689879131394802373076737172779194862932999849486641952351767738780953784
      , 7917159902307905727813080625122777309809151624119093977983495514817909259553
      , 10305078288915035001787281422329641624507094761680960003698404035062931519465
      ] := by
  native_decide

example :
    val? (Sponge.hash? (bn254T4Params Fr) [c 1, c 2, c 3] 3 false) =
      some 16068223842875184682212183064520144190817798559788034419026031423767658184152 := by
  native_decide

example :
    val? (Sponge.hash? (bn254T4Params Fr) [c 1, c 2, c 0] 2 true) =
      some 2304388032127604510543726135849368789537863614140798013660173624597943578110 := by
  native_decide

end BN254Vectors

end Tests.Poseidon2
