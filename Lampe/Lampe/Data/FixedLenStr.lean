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

def fromVector (u : U 32) (vec : List.Vector Char u.toNat) : FixedLenStr u.toNat :=
  let ⟨cs, h⟩ := vec
  ⟨⟨cs⟩, by simp only [String.length, h]⟩

def toVector {n : Nat} (s : FixedLenStr n) : List.Vector Char n :=
  ⟨s.data.toList, by change s.data.length = n ; apply FixedLenStr.data_len⟩

end FixedLenStr
