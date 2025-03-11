import Tests.Skyscraper.Ref
import Tests.Skyscraper.Extracted

open Lampe Extracted

-- set_option trace.Lampe.SL true

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
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.rl.fn
  all_goals try tauto
  simp only [rl]
  steps
  simp_all
  tauto

theorem u8_ge_zero (u : U 8) : 0 ≤ u := by bv_decide

theorem rotateLeft_spec : STHoare lp env ⟦N < 254⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Skyscraper.rotateLeft input N := by
  simp only [Extracted.rotate_left]

  steps
  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Skyscraper.rl i.toNat input⟩]
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
    simp_all [Skyscraper.rotateLeft]

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  enter_decl
  apply STHoare.consequence (h_hoare := rotateLeft_spec)
  simp_all [SLP.entails]
  simp [SLP.star, SLP.top, SLP.entails]

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  simp only [sbox]
  steps [rotate_left_intro]
  · subst_vars; rfl
  all_goals decide

theorem sbox_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "sbox" [] HList.nil) h![input])
    fun output => output = Skyscraper.sbox input := by
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

-- TODO: Do we want this as an axiom or not?
axiom from_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.array (Tp.u 8) 32] Tp.field (FuncRef.decl "from_le_bytes" [] HList.nil) h![input])
    fun output => output = Skyscraper.bnField.fromLeBytes input.toList -- := by
  -- enter_decl
  -- simp only [from_le_bytes]
  -- steps

def List.Vector.pad {α n} (v : List.Vector α n) (d : Nat) (pad : α) : List.Vector α d := match d, n with
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
    · simp [replicate]
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

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [bar]
  steps [to_le_bytes_intro]

  enter_block_as
    ([new_left ↦ ⟨(Tp.u 8).array 16, List.Vector.replicate 16 0⟩])
    (fun _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take 16 |>.map Skyscraper.sbox⟩])

  · loop_inv fun i _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
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
    (fun _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.map Skyscraper.sbox⟩])

  · loop_inv fun i _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
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

-- theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
--     fun output => output = Skyscraper.bar input := by
--   enter_decl
--   apply bar_spec

-- theorem sigma_intro : STHoare lp env (⟦⟧)
--     (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
--       fun output => output = Skyscraper.SIGMA := by
--   enter_decl
--   simp only [Extracted.SIGMA]
--   steps []
--   unfold Skyscraper.SIGMA
--   assumption

-- theorem rc_intro : STHoare lp env (⟦⟧)
--     (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
--       fun output => output = ⟨Skyscraper.RC.toList, by rfl⟩ := by
--   enter_decl
--   simp only [Extracted.RC]
--   steps []
--   subst_vars
--   unfold Skyscraper.RC
--   rfl

-- theorem square_intro : STHoare lp env (⟦⟧)
--     (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
--       fun output => output = Skyscraper.square input := by
--   enter_decl
--   simp only [Extracted.square]
--   steps [sigma_intro]
--   unfold Skyscraper.square
--   subst_vars
--   rfl

-- theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
--     fun output => output = (Skyscraper.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Skyscraper.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by sorry -- TODO: This has a bad timeout now?
--   -- enter_decl
--   -- simp only [Extracted.permute]
--   -- steps [bar_intro, square_intro, rc_intro]
--   -- casesm* ∃_,_
--   -- simp [Builtin.indexTpl] at *
--   -- subst_vars
--   -- unfold Skyscraper.permute

-- theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
--     fun output => output = Skyscraper.compress l r := by
--   simp only [compress]
--   steps [permute_intro]
--   unfold Skyscraper.compress
--   subst_vars
--   simp [Skyscraper.State.permute]
--   casesm*∃_,_
--   subst_vars
--   simp
--   congr 1
