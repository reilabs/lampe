import Lampe

import Mathlib.Data.Vector.Snoc

open Lampe


@[reducible, simp]
def Lampe.FunctionDecl.call {lp} (f : FunctionDecl)
    (gs : HList Kind.denote f.fn.generics)
    (args : HList (Tp.denote lp) (f.fn.body (Tp.denote lp) gs).argTps):
    Expr (Tp.denote lp) (f.fn.body (Tp.denote lp) gs).outTp :=
    (.call
        (f.fn.body (Tp.denote lp) gs).argTps
        (f.fn.body (Tp.denote lp) gs).outTp
        (FuncRef.decl f.name f.fn.generics gs)
        args)

namespace Test

nr_struct_def DummyHasher<> {

}

nr_trait_impl[impl_405] <> BinaryHasher<Field> for DummyHasher<> where  {
    fn «hash»<> (a : Field, b : Field) -> Field {
        #fAdd(a, b) : Field;
}
}

nr_def «mtree_recover»<H, @N : 32>(idx : [bool; N], p : [Field; N], item : Field) -> Field {
    let mut curr_h = item;
    for i in 0 : u32 .. @N {
            let dir = #arrayIndex(idx, #cast(i) : u32) : bool;
        let sibling_root = #arrayIndex(p, #cast(i) : u32) : Field;
        if dir {
                curr_h = ((H as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(sibling_root, curr_h);
        } else {
                curr_h = ((H as BinaryHasher<Field>)::hash<> as λ(Field, Field) → Field)(curr_h, sibling_root);
        };
    };
    curr_h;
}

#check mtree_recover

def env := Lampe.Env.mk [(«mtree_recover».name, «mtree_recover».fn)] [impl_405]

def p := 21888242871839275222246405745257275088548364400416034343698204186575808495617 - 1

axiom pPrime : Nat.Prime (p + 1)

def lp : Lampe.Prime := ⟨p, pPrime⟩

def Hash (t : Type) (n : Nat) := List.Vector t n -> t

def recover {depth : Nat} {F: Type} (H : Hash F 2) (ix : List.Vector Bool depth) (proof : List.Vector F depth) (item : F) : F := match depth with
  | Nat.zero => item
  | Nat.succ _ =>
    let pitem := proof.head
    let recover' := recover H ix.tail proof.tail item
    match ix.head with
    | false => H ⟨[recover', pitem], by tauto⟩
    | true => H ⟨[pitem, recover'], by tauto⟩

def recover_zero (h : n = 0) : recover (depth := n) H' idx proof item = item := by
  cases h
  rfl

def List.Vector.takeF {α : Type} {n : Nat} (v : List.Vector α n) (i : Nat) (hi : i ≤ n) : List.Vector α i :=
  List.Vector.congr (by simp [hi]) (v.take i)

theorem List.Vector.takeF_congr (he: i₁ = i₂) : List.Vector.takeF v i₁ h = he ▸ List.Vector.takeF v i₂ (he ▸ h) := by
  cases he
  rfl

theorem List.Vector.takeF_succ_eq_snoc_get {v : List.Vector α n} : List.Vector.takeF v (i + 1) hi = (List.Vector.takeF v i (by linarith)).snoc (v.get ⟨i, by linarith⟩) := by
  rcases v with ⟨v, rfl⟩
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, List.Vector.snoc, List.Vector.get, List.take_succ]

@[simp]
theorem List.Vector.congrArg₂ {f : {n : Nat} → List.Vector α n → List.Vector β n → γ} (h₁ h₂ : n = n₁):
  @f n₁ (h₁ ▸ v₁) (h₂ ▸ v₂) = @f n v₁ v₂ := by
  cases h₁
  cases h₂
  rfl

@[simp]
theorem List.Vector.cast_reverse {h : n₁ = n₂} {v : List.Vector α n₁} : (h ▸ v).reverse = h ▸ v.reverse := by
  cases h
  rfl

@[simp]
theorem List.Vector.takeF_all {v : List.Vector α n} : List.Vector.takeF v n (by simp) = v := by
  cases v
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, *]

@[simp]
theorem List.Vector.takeF_all_of_eq {v : List.Vector α n} (h : n₁ = n) : List.Vector.takeF v n₁ (by simp_all) = h ▸ v := by
  cases h
  cases v
  apply List.Vector.eq
  simp [List.Vector.takeF, List.Vector.congr, List.Vector.take, *]

theorem recover_intro {H N idx proof item}
    (hHash : ∀ {a b}, STHoare lp env
        ⟦True⟧
        (Expr.call [Tp.field, Tp.field] Tp.field
          (FuncRef.trait (some H) "BinaryHasher" [Kind.type] (HList.cons Tp.field HList.nil) "hash" [] HList.nil) h![a,b])
        (fun v => v = H' (a ::ᵥ b ::ᵥ .nil))):
    STHoare lp env ⟦True⟧ (mtree_recover.call h![H, N] h![idx, proof, item]) (fun v => v = recover H' idx.reverse proof.reverse item) := by
  enter_decl
  simp only [mtree_recover]
  steps
  loop_inv fun i _ _ =>
    [curr_h ↦ ⟨Tp.field,
      recover H' (List.Vector.takeF idx i.toNat (by simpa [←BitVec.lt_def];)).reverse
                 (List.Vector.takeF proof i.toNat (by simpa [←BitVec.lt_def])).reverse item⟩]
  · simp [BitVec.le_def, Int.cast, IntCast.intCast]
  · intro i _ hi
    steps
    enter_block_as m =>
      ([curr_h ↦ ⟨Tp.field, m⟩])
      (fun _ => [curr_h ↦ ⟨Tp.field, if dir then H' (sibling_root ::ᵥ m ::ᵥ .nil) else H' (m ::ᵥ sibling_root ::ᵥ .nil) ⟩])
    apply STHoare.ite_intro <;> {
      rintro rfl
      steps [hHash]
      simp_all
    }
    steps
    have : (i + 1).toNat = i.toNat + 1 := by
      rcases N with ⟨N, lt⟩
      simp [BitVec.lt_def] at hi
      simp
      linarith []
    congr 1
    simp_rw [List.Vector.takeF_congr this, List.Vector.cast_reverse]
    rw [Eq.comm]
    apply Eq.trans
    apply List.Vector.congrArg₂ (f := fun a b => recover H' a b item)
    casesm* ∃_, _
    rename dir = _ => hdir
    rename sibling_root = _ => hsr
    simp at hdir hsr
    simp [recover, List.Vector.takeF_succ_eq_snoc_get, ←hdir, ←hsr]
    cases dir <;> rfl

  steps
  subst_vars
  congr
  all_goals simp
