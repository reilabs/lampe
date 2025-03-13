import Merkle.Extracted
import Merkle.Field
import Merkle.Ref
import Lampe

import ProvenZk

import Mathlib.Data.Vector.Snoc

open Lampe Ref Extracted

namespace Spec

def lp : Lampe.Prime := ⟨p, pPrime⟩

theorem recover_zero (h : n = 0) : MerkleTree.recover (depth := n) H' idx proof item = item := by
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
    STHoare lp env ⟦True⟧ (mtree_recover.call h![H, N] h![idx, proof, item]) (fun v => v = MerkleTree.recover H' idx.reverse proof.reverse item) := by
  enter_decl
  simp only [mtree_recover]
  steps
  loop_inv fun i _ _ =>
    [curr_h ↦ ⟨Tp.field,
      MerkleTree.recover H' (List.Vector.takeF idx i.toNat (by simpa [←BitVec.lt_def];)).reverse
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
    rw [List.Vector.congrArg₂ (f := fun a b => MerkleTree.recover _ a b _)]
    casesm* ∃_, _
    rename dir = _ => hdir
    rename sibling_root = _ => hsr
    simp at hdir hsr
    simp [MerkleTree.recover, List.Vector.takeF_succ_eq_snoc_get, ←hdir, ←hsr]
    cases dir <;> rfl

  steps
  subst_vars
  congr
  all_goals simp

def RC : List Int :=
    [-4058822530962036113558957735524994411356374024839875405476791844324326516925,
    5852100059362614845584985098022261541909346143980691326489891671321030921585,
    -4840154698573742532565501789862255731956493498174317200418381990571919688651,
    71577923540621522166602308362662170286605786204339342029375621502658138039,
    1630526119629192105940988602003704216811347521589219909349181656165466494167,
    7807402158218786806372091124904574238561123446618083586948014838053032654983,
    -8558681900379240296346816806663462402801546068866479372657894196934284905006,
    -4916733727805245440019875123169648108733681133486378553671899463457684353318]

def SIGMA : Int :=
    9915499612839321149637521777990102151350674507940716049588462388200839649614

theorem rl_intro : STHoare lp env ⟦⟧
  (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "rl" [] HList.nil) h![input])
    fun output => output = Ref.rl input := by
  enter_decl
  steps
  subst_vars
  rfl

theorem u8_ge_zero (u : U 8) : 0 ≤ u := by bv_decide

theorem rotateLeft_spec : STHoare lp env ⟦N < 254⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Ref.rotateLeft input N := by
  simp only [Extracted.rotate_left]

  steps
  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Ref.rl i.toNat input⟩]
  change 0 ≤ N
  exact u8_ge_zero N
  · intros i hlo hhi
    steps [rl_intro]
    simp_all
    congr
    have : (i.toNat + 1) % 256 = i.toNat + 1 := by
      have : i.toNat < N.toNat := hhi
      have : N.toNat < 254 := by rename_i a _ _ ; exact a
      omega
    rw [this]
    simp [Nat.repeat]
  · steps
    simp_all [Ref.rotateLeft]

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Ref.rotateLeft input N := by
  enter_decl
  apply STHoare.consequence (h_hoare := rotateLeft_spec)
  simp_all [SLP.entails]
  simp [SLP.star, SLP.top, SLP.entails]

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Ref.sbox input := by
  simp only [Extracted.sbox]
  steps [rotate_left_intro]
  · subst_vars; rfl
  all_goals decide

theorem sbox_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "sbox" [] HList.nil) h![input])
    fun output => output = Ref.sbox input := by
  enter_decl
  apply sbox_spec

theorem sgn0_spec : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.u 1) (FuncRef.decl "sgn0" [] HList.nil) h![input])
    fun output => output = (input.val % 2) := by
  enter_decl
  simp only [sgn0]
  steps
  simp_all

opaque BitVec.bytesLE : BitVec n → List.Vector (U 8) n

axiom toLeBytesPadLen {input : Lampe.Fp lp} : (padEnd 32 (Lampe.toLeBytes input)).length = 32

axiom to_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.array (Tp.u 8) 32) (FuncRef.decl "to_le_bytes" [] HList.nil) h![input])
    fun output => output = ⟨List.takeD 32 (Lampe.toLeBytes input) 0, List.takeD_length _ _ _⟩

axiom from_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.array (Tp.u 8) 32] Tp.field (FuncRef.decl "from_le_bytes" [] HList.nil) h![input])
    fun output => output = Merkle.bnField.fromLeBytes input.toList

def _root_.List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
| 0, _ => List.Vector.nil
| d+1, 0 => pad ::ᵥ List.Vector.pad v d pad
| d+1, _+1 => v.head ::ᵥ List.Vector.pad v.tail d pad

@[simp]
theorem List.Vector.toList_pad {v : List.Vector α n} {pad} : (v.pad d pad).toList = v.toList.takeD d pad := by
  rcases v with ⟨l, prop⟩
  induction d generalizing l n with
  | zero => simp
  | succ d ih =>
    cases n
    · simp [List.Vector.pad, ih, List.replicate_succ]
    · rcases (List.exists_of_length_succ _ prop) with ⟨h, t, ⟨rfl⟩⟩
      simp at prop
      simp [List.Vector.pad, List.Vector.head, List.Vector.tail, ih]

theorem List.takeD_eq_take_append : List.takeD n l pad = List.take n l ++ List.replicate (n - l.length) pad := by
  induction n generalizing l with
  | zero => simp
  | succ n ih =>
    cases l
    · simp [List.replicate]
    · simp [List.takeD, List.take, ih]

theorem as_array_intro (hi : input.length = 32) : STHoare lp env ⟦⟧ (Expr.call [Tp.slice (Tp.u 8)] (Tp.array (Tp.u 8) 32) (FuncRef.decl "as_array" [] HList.nil) h![input])
    fun output => output = ⟨input, hi⟩ := by
  enter_decl
  simp only [as_array]
  steps
  loop_inv fun i _ _ => [array ↦ ⟨Tp.array (Tp.u 8) 32, List.Vector.pad ⟨input.takeD i.toNat 0#8, List.takeD_length i.toNat _ _⟩ 32 0#8⟩]
  · decide
  · intros i hlo hhi
    steps
    casesm* ∃_,_
    subst_vars
    simp [Access.modify]
    congr 1
    rcases i with ⟨i, _⟩
    simp [IntCast.intCast, Int.cast, Fin.lt_def, OfNat.ofNat] at hhi
    apply List.Vector.eq
    simp only [List.Vector.toList_set, List.Vector.toList_pad, BitVec.toNat]
    simp only [List.Vector.toList]
    rw [Nat.mod_eq_of_lt (by linarith)]
    simp only [List.takeD_eq_take_append]
    have : i ≤ 32 := by linarith
    have : i + 1 ≤ 32 := by linarith
    simp [*, List.take_take]
    rw [List.take_succ, List.append_assoc]
    congr 1
    generalize_proofs
    have : 32 - i = (31 - i) + 1 := by omega
    simp [getElem?, decidableGetElem?, *, List.replicate]
  steps
  subst_vars
  apply List.Vector.eq
  simp only [List.Vector.toList_pad]
  simp only [List.Vector.toList]
  conv => enter [1,2,1]; whnf
  have : input.length ≤ input.length := by linarith
  simp only [←hi, Int.cast, IntCast.intCast, BitVec.ofInt, List.takeD_eq_take, this, List.take_length]

set_option maxHeartbeats 3000000000000
theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Ref.bar input := by
  simp only [Extracted.bar]
  steps [to_le_bytes_intro]

  enter_block_as
    ([new_left ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take 16 |>.map Ref.sbox⟩])

  · loop_inv fun i _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Ref.sbox |>.pad 16 (0:U 8)⟩]
    · decide
    · congr 1
      apply List.Vector.eq
      simp [-List.takeD_succ, List.takeD_eq_take_append, Int.cast, IntCast.intCast]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps [sbox_intro]
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      have : i + 1 < 4294967296 := by
        linarith
      casesm* ∃_,_
      subst_vars
      congr 1
      apply List.Vector.eq
      simp [-List.takeD_zero, -List.takeD_succ, Access.modify, List.Vector.get, Fin.add_def, Nat.mod_eq_of_lt, this]
      have i₁ : i ≤ 32 := by linarith
      have i₂ : i + 1 ≤ 32 := by linarith
      have i₃ : i ≤ 16 := by linarith
      have i₄ : i + 1 ≤ 16 := by linarith
      have i₅ : i < 32 := by linarith
      simp [-List.takeD_zero, -List.takeD_succ,
        List.takeD_eq_take_append,
        List.take_take,
        i₁, i₂, i₃, i₄]
      simp only [List.take_succ, List.append_assoc]
      have : (16 - i) = (15 - i) + 1 := by omega
      simp [this, List.replicate_succ, getElem?, decidableGetElem?, i₅, List.Vector.toList]

  steps

  enter_block_as
    ([new_right ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.map Ref.sbox⟩])

  · loop_inv fun i _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Ref.sbox |>.pad 16 (0:U 8)⟩]
    · decide
    · congr 1
      apply List.Vector.eq
      simp [-List.takeD_succ, Int.cast, IntCast.intCast, List.takeD_eq_take_append, List.take_take]
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps [sbox_intro]
      casesm* ∃_,_
      subst_vars
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      simp [-List.takeD_zero, -List.takeD_succ, Builtin.CastTp.cast, Access.modify]
      congr 1
      apply List.Vector.eq
      simp [-List.takeD_zero, -List.takeD_succ, -List.map_drop, List.Vector.get, Fin.add_def, Int.cast, IntCast.intCast, OfNat.ofNat]
      have : 16 + i < 4294967296 := by linarith
      have : i + 1 < 4294967296 := by linarith
      simp only [Nat.mod_eq_of_lt, *, List.getElem_drop']
      simp only [List.takeD_eq_take_append]
      have i₁ : i ≤ 16 := by linarith
      have i₂ : i + 1 ≤ 16 := by linarith
      simp [i₁, i₂, List.take_take]
      simp only [List.take_succ, List.append_assoc]
      congr 1
      have : (16 - i) = (15 - i) + 1 := by omega
      simp [this, List.replicate_succ, getElem?, decidableGetElem?]
      simp only [hlt, dite_true, Option.toList]
      simp [List.cons_append, List.nil_append, List.Vector.toList]

  steps

  rename' «#v_25» => v

  enter_block_as =>
    ([new_bytes ↦ ⟨(Tp.u 8).slice, v.toList⟩])
    (fun _ => [new_bytes ↦ ⟨(Tp.u 8).slice, v.toList ++ ζi0.toList⟩])
  · loop_inv fun i _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice, v.toList ++ ζi0.toList.take i.toNat⟩]
    · decide
    · congr 1
      simp [Int.cast, IntCast.intCast]
    · congr 1
      simp
    · intro i _ hlt
      rename bytes = _ => bytes_def
      clear bytes_def
      steps
      simp
      congr 1
      rcases i with ⟨i, hi⟩
      rw [BitVec.lt_def] at hlt
      conv at hlt => congr <;> whnf
      casesm* ∃_,_
      subst «#v_30» elem
      have : i + 1 < 4294967296 := by linarith
      simp [Nat.mod_eq_of_lt, this, List.take_succ]
      simp [getElem?, decidableGetElem?, hlt]
      rfl

  steps [as_array_intro, from_le_bytes_intro]
  rotate_left
  · subst «#v_35» v
    simp
  · subst_vars
    rfl

theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
    fun output => output = Ref.bar input := by
  enter_decl
  apply bar_spec

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
      fun output => output = Ref.SIGMA := by
  enter_decl
  simp only [Extracted.SIGMA]
  steps []
  unfold Ref.SIGMA
  assumption

theorem rc_intro : STHoare lp env (⟦⟧)
    (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
      fun output => output = ⟨Ref.RC.toList, by rfl⟩ := by
  enter_decl
  simp only [Extracted.RC]
  steps []
  subst_vars
  unfold Ref.RC
  rfl

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Ref.square input := by
  enter_decl
  simp only [Extracted.square]
  steps [sigma_intro]
  unfold Ref.square
  subst_vars
  rfl

theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
    fun output => output = (Ref.State.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Ref.State.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by
  enter_decl
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn with | cons _ i =>
  cases i using List.Vector.casesOn
  simp only [Extracted.permute]
  steps [bar_intro, square_intro, rc_intro]
  casesm* ∃_,_
  simp [Builtin.indexTpl, Nat.mod_eq_of_lt, lp] at *
  subst_vars
  rfl

instance {α H n} : Membership α (MerkleTree α H n) where
  mem t e := ∃p, e = MerkleTree.itemAt t p

lemma SkyscraperHash_correct: STHoare lp env ⟦⟧ (Expr.call [Tp.field, Tp.field] Tp.field
          (FuncRef.trait (some $ «struct#Skyscraper».tp h![]) "BinaryHasher" [Kind.type] (HList.cons Tp.field HList.nil) "hash" [] HList.nil) h![a,b]) (fun v => v = Ref.State.compress ⟨[a, b], rfl⟩) := by
  enter_trait [] env
  steps [permute_intro]
  casesm*∃_,_
  subst_vars
  congr 1

theorem main_correct [Fact (CollisionResistant Ref.State.compress)] {tree : MerkleTree (Fp lp) Ref.State.compress 32}:
    STHoare lp env
        ⟦⟧
        (main.call h![] h![tree.root, proof, item, index])
        (fun _ => item ∈ tree) := by
  enter_decl
  simp only
  steps [recover_intro (H:= «struct#Skyscraper».tp h![]) (N:=32) (hHash := SkyscraperHash_correct)]
  use index.reverse
  rename ∃_, True => heq
  simp at heq
  cases heq
  rename tree.root = _ => hroot
  rw [Eq.comm, MerkleTree.recover_eq_root_iff_proof_and_item_correct] at hroot
  exact hroot.2
