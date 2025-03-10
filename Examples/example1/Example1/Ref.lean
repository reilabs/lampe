import Lampe

namespace Ref

open Lampe

variable {p : Prime}

def Hash (t : Type) (n : Nat) := List.Vector t n -> t

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : List.Vector Bool depth) (proof : List.Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
    | false => H ⟨[recover', pitem], by tauto⟩
    | true => H ⟨[pitem, recover'], by tauto⟩
