import Lampe.Data.Field

import Merkle.Field

open Field
namespace Ref

open Lampe (U Fp)

def RC : Array bnField := #[
    17829420340877239108687448009732280677191990375576158938221412342251481978692,
    5852100059362614845584985098022261541909346143980691326489891671321030921585,
    17048088173265532689680903955395019356591870902241717143279822196003888806966,
    71577923540621522166602308362662170286605786204339342029375621502658138039,
    1630526119629192105940988602003704216811347521589219909349181656165466494167,
    7807402158218786806372091124904574238561123446618083586948014838053032654983,
    13329560971460034925899588938593812685746818331549554971040309989641523590611,
    16971509144034029782226530622087626979814683266929655790026304723118124142299
]

def SIGMA : bnField := 9915499612839321149637521777990102151350674507940716049588462388200839649614

def rl (u : U 8) : U 8 :=
    let top_bit := u >>> 7;
    (u <<< 1) ||| top_bit

def rotateLeft (u N : U 8) : U 8 := Nat.repeat rl N.toNat u

def sbox (v : U 8) : U 8 :=
  v ^^^ rotateLeft (rotateLeft v.not 1 &&& rotateLeft v 2 &&& rotateLeft v 3) 1

def bar (a : bnField) : bnField :=
  let bytes := Fp.toBytesLE 32 a
  let left := bytes.take 16
  let right := bytes.drop 16
  let new_left := left.map sbox
  let new_right := right.map sbox
  let new_bytes := new_right.append new_left
  Fp.ofBytesLE new_bytes.toList

def square (a : bnField) : bnField :=
  a * a * SIGMA

structure State where
  left : bnField
  right : bnField
deriving Repr

namespace State

def permute (s : State) : State :=
  let (l, r) := (s.left, s.right)
  let (l, r) := (r + square l, l)
  let (l, r) := (r + square l + RC[0], l)
  let (l, r) := (r + bar l + RC[1], l)
  let (l, r) := (r + bar l + RC[2], l)
  let (l, r) := (r + square l + RC[3], l)
  let (l, r) := (r + square l + RC[4], l)
  let (l, r) := (r + bar l + RC[5], l)
  let (l, r) := (r + bar l + RC[6], l)
  let (l, r) := (r + square l + RC[7], l)
  let (l, r) := (r + square l, l)
  { left := l, right := r }

def compress (v : List.Vector bnField 2) : bnField :=
  let x := permute ⟨v[0], v[1]⟩
  x.left + v[0]

end State

end Ref
