import Mathlib.Data.Vector.Basic

import Lampe.Data.Integers

open Lampe

structure FixedLenStr (n : Nat) where
  data : String
  data_len : data.length = n := by rfl

namespace FixedLenStr

attribute [simp] data_len

def ofString (s : String) : FixedLenStr s.length where
  data := s

instance (s : String) : CoeDep String s (FixedLenStr s.length) where
  coe := ofString s

def toVector (u : U 32) (s : FixedLenStr u.toNat)  : Mathlib.Vector Char u.toNat :=
  ⟨s.data.toList, by change s.data.length = u.toNat ; apply FixedLenStr.data_len⟩

end FixedLenStr
