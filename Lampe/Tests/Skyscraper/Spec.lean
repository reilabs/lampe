import Tests.Skyscraper.Ref
import Tests.Skyscraper.Extracted

open Lampe Extracted

def lp : Lampe.Prime := ⟨p, pPrime⟩

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
    fun output => output = Skyscraper.rl input := by
  enter_decl
  simp only [rl]
  steps
  subst_vars
  rfl

-- This is almost certainly stated incorrectly, but something like this is true
theorem bitvec_lt (w : Nat) (b N : BitVec w) (hb : b < N) (hN : N < (2 ^ w : Nat) - 1)
    : b.toNat < N.toNat := by
  sorry

lemma rfl_iff_true : α = α ↔ True := by tauto

set_option trace.Lampe.SL true

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  enter_decl
  simp only [rotate_left]
  steps

  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Skyscraper.rl i.toNat input⟩]
  · simp only [Int.cast, IntCast.intCast]
    bv_decide
  · intros i hlo hhi
    steps [rl_intro]
    congr
    simp_all
    have i_lt : i < 254 := by bv_decide
    have i_succ_lt : i + 1 < 255 := by bv_decide
    have x := bitvec_lt 8 i N hhi (by bv_decide)
    have y := bitvec_lt 8 N 254 (by assumption) (by decide)
    set iNat := BitVec.toNat i
    have : (iNat + 1) % 256 = iNat + 1 := by
      simp_all
      linarith
    rw [this]
    rfl

  steps
  simp_all
  rfl


set_option pp.rawOnError true

set_option trace.Lampe.STHoare.Helpers true

theorem sbox_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "sbox" [] HList.nil) h![input])
    fun output => output = Skyscraper.sbox input := by
  enter_decl
  simp only [sbox]
  steps [rotate_left_intro]
  any_goals decide
  subst_vars
  rfl

theorem sgn0_spec : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.u 1) (FuncRef.decl "sgn0" [] HList.nil) h![input])
    fun output => output = (input.val % 2) := by
  enter_decl
  simp only [sgn0]
  steps
  simp_all

opaque BitVec.bytesLE : BitVec n → List.Vector (U 8) n

axiom toLeBytesPadLen {input : Lampe.Fp lp} : (padEnd 256 (Lampe.toLeBytes input)).length = 32

axiom to_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.array (Tp.u 8) 32) (FuncRef.decl "to_le_bytes" [] HList.nil) h![input])
    fun output => output = ⟨padEnd 256 (Lampe.toLeBytes input), toLeBytesPadLen⟩

lemma SLP.exists_prop_of_proof {P : Prop} {h} [LawfulHeap h] {Q : P → SLP h} {pr : P}: (∃∃ (x : P), Q x) = Q pr := by
  unfold SLP.exists'
  funext st
  simp only [←iff_iff_eq]
  apply Iff.intro
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨pr, h⟩

lemma blockExit : STHoare lp Γ ⟦⟧ (Expr.var (tp := .unit) ()) (fun _ => ⟦⟧) := by
  apply STHoare.consequence (h_hoare := STHoare.var_intro)
  apply SLP.entails_self
  intro ()
  simp [SLP.entails_self]

lemma Lens.modify_array_isSome_iff_len_lt {p : Lampe.Prime} {size: U 32} {idx} {val : Tp.denote p elt} {vec : Tp.denote p (Tp.array elt size)} : ((Lens.nil.cons (Access.array idx)).modify vec val |>.isSome) ↔ idx.toNat < vec.length := by
  simp [Access.modify]

lemma Lens.modify_array_length {p : Lampe.Prime} {size: U 32} {idx} {val : Tp.denote p elt} {vec : Tp.denote p (Tp.array elt size)} {hp} : ((Lens.nil.cons (Access.array idx)).modify vec val |>.get hp).length = vec.length := by
  simp

lemma Access.modify_array_isSome_iff_len_lt {p : Lampe.Prime} {size: U 32} {idx} {val : Tp.denote p elt} {vec : Tp.denote p (Tp.array elt size)} : ((Access.array idx).modify vec val |>.isSome) ↔ idx.toNat < vec.length := by
  simp [Access.modify]

lemma unusedFn : (fun _ => body) () = body := by rfl

lemma ent_star_top_unused[LawfulHeap h]{H : SLP h} : H ⊢ (fun (_ : Tp.denote lp .unit) => H) () ⋆ ⊤ := by
  exact SLP.ent_star_top

theorem STHoare.consequence' {p tp} {e : Expr (Tp.denote p) tp} {H₁ H₂} {Q₁ Q₂ : Tp.denote p tp → SLP (State p)}
    (h_hoare: STHoare p Γ H₁ e Q₁)
    (h_pre_conseq : H₂ ⊢ H₁)
    (h_post_conseq : ∀ v, Q₁ v ⋆ ⊤ ⊢ Q₂ v ⋆ ⊤):
    STHoare p Γ H₂ e Q₂:= by
  apply STHoare.consequence
  all_goals assumption

set_option trace.Lampe.SL true

theorem exi_pure' [LawfulHeap α] {P : α → Prop} : (SLP.exists' fun x =>  ⟦P x⟧) = SLP.lift (α := α) (∃x, P x) := by
  unfold SLP.exists' SLP.lift
  simp

def List.Vector.map_pfx {α n} (v : List.Vector α n) (d : Nat) (f : α → α) : List.Vector α n := match d, n with
| 0, _ => v
| _, 0 => v
| Nat.succ d, Nat.succ _ => f v.head ::ᵥ List.Vector.map_pfx v.tail d f

lemma List.Vector.map_pfx_get_of_lt {n} {v : Vector α n} {f} {i} {hi : i.val < d} : (map_pfx v d f).get i = f (v.get i) := by
  induction d generalizing v i n with
  | zero => simp_all
  | succ d ih =>
    have : ∃n', n = n' + 1 := by
      have := i.prop
      simp
      linarith
    rcases this with ⟨n, rfl⟩
    simp only [map_pfx]
    cases i using Fin.cases
    · simp
    · simp only [get_cons_succ]
      simp at hi
      rw [ih]
      · simp
      assumption

def List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
| 0, _ => List.Vector.nil
| d+1, 0 => pad ::ᵥ List.Vector.pad v d pad
| d+1, _+1 => v.head ::ᵥ List.Vector.pad v.tail d pad

def List.pad {α} (l : List α) (d : Nat) (pad : α) : List α := match d, l with
| 0, _ => []
| d+1, [] => pad :: List.pad [] d pad
| d+1, h::t => h :: List.pad t d pad

@[simp]
lemma List.Vector.toList_pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : (List.Vector.pad v d pad).toList = List.pad v.toList d pad := by
  sorry



theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [bar]
  steps [to_le_bytes_intro]

  loop_inv fun (i: U 32) _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · decide
  · intro i _ hlt
    steps [sbox_intro]
    · casesm* ∃_,_
      subst_vars
      simp [Builtin.CastTp.cast, Access.modify]
      congr 1
      apply List.Vector.eq
      simp
      -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
      sorry

  steps [sbox_intro]

  loop_inv fun (i: U 32) _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · decide
  · intro i _ hlt
    steps [sbox_intro]
    casesm* ∃_,_
    subst_vars
    simp [Builtin.CastTp.cast, Access.modify]
    sorry
      -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
  steps

  loop_inv fun (i : U 32) _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice,  bytes.drop 16 |>.append (bytes.take 16) |>.map Skyscraper.sbox |>.take (16 + i.toNat) |>.pad 32 0 |>.toList⟩]
  · simp [BitVec.le_def, Int.cast, IntCast.intCast]
  · sorry
  · intro i _ _
    steps
    casesm* ∃_,_
    subst_vars
    simp [Builtin.CastTp.cast, Access.modify]
    -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
    sorry

  sorry -- missing fn

theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
    fun output => output = Skyscraper.bar input := by
  enter_decl
  apply bar_spec

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
      fun output => output = Skyscraper.SIGMA := by
  enter_decl
  simp only [Extracted.SIGMA]
  steps
  simp_all [Skyscraper.SIGMA]

theorem rc_intro : STHoare lp env (⟦⟧)
    (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
      fun output => output = ⟨Skyscraper.RC.toList, by rfl⟩ := by
  enter_decl
  simp only [Extracted.RC]
  steps
  subst_vars; rfl

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Skyscraper.square input := by
  enter_decl
  simp only [Extracted.square]
  steps [sigma_intro]
  subst_vars
  rfl

theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
    fun output => output = (Skyscraper.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Skyscraper.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by
  enter_decl
  simp only [Extracted.permute]
  steps [square_intro, rc_intro, bar_intro]
  casesm* ∃_,_
  simp [Builtin.indexTpl, OfNat.ofNat] at *
  subst_vars
  rfl

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  simp only [compress]
  steps [permute_intro]
  casesm* ∃_,_
  subst_vars
  simp [Skyscraper.compress, HList.toVec, HList.toList]
  rfl
