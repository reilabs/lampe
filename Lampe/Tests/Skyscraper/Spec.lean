import Tests.Skyscraper.Ref
import Tests.Skyscraper.Extracted

open Lampe Extracted

set_option trace.Lampe.SL true

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
  simp_all [Skyscraper.sbox]
  congr
  · change 1 < 254; bv_decide
  · change 3 < 254; bv_decide
  · change 2 < 254; bv_decide
  · change 1 < 254; bv_decide

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
    fun output => output = ⟨padEnd 32 (Lampe.toLeBytes input), toLeBytesPadLen⟩

-- TODO: Do we want this as an axiom or not?
axiom from_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.array (Tp.u 8) 32] Tp.field (FuncRef.decl "from_le_bytes" [] HList.nil) h![input])
    fun output => output = Skyscraper.bnField.fromLeBytes input.toList -- := by
  -- enter_decl
  -- simp only [from_le_bytes]
  -- steps

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

lemma List.Vector.pad_eq_self {α n} (v : List.Vector α n) (pad : α) : v.pad n pad = v := by
  induction n with
  | zero =>
    unfold List.Vector.pad
    simp [List.Vector.eq_nil]
  | succ i ih =>
    unfold List.Vector.pad
    simp? [ih]

lemma asdfasdf {d n : Nat} : (min d.succ n.succ) = (min d (n.succ - 1)).succ := by omega

lemma List.Vector.toList_cast (h : n₁ = n₂) (v : List.Vector α n₁) :
    (h ▸ v : List.Vector α n₂).toList = v.toList := by
  cases v
  cases h
  rfl

lemma List.Vector.take_cons_head_tail {α} {n d : Nat} (v : List.Vector α (n.succ))
    : v.head ::ᵥ (v.tail.take d) = Nat.succ_min_succ _ _ ▸ v.take d.succ := by
  apply List.Vector.eq
  cases v using List.Vector.casesOn
  simp [List.Vector.toList_cast]

lemma List.Vector.take_eq_take_list {α} {n d : Nat} (v : List.Vector α n) (hd : d ≤ n):
    (Nat.min_eq_left hd ▸ v.take d : List.Vector α d) = ⟨v.val.take d, by aesop⟩ := by
  convert_to v.take d = ⟨v.val.take d, by aesop⟩
  · rw [Nat.min_eq_left hd]
  · simp
  · rename_i h
    sorry -- TODO: This seems like an obvious HEq goal
  · aesop

lemma aaasdf (n : Nat) : (n.succ ⊓ (n + 1)) = (n ⊓ (n + 1 - 1)).succ := by aesop

lemma List.Vector.pad_thm_le {α n} (v : List.Vector α n) (d : Nat) (hd : d ≤ n) (pad : α) :
    v.pad d pad = ⟨v.val.take d, by simp; omega⟩ := by
  induction n with
  | zero =>
    have : d = 0 := by omega
    subst this
    rfl
  | succ n hn =>
    match Nat.lt_trichotomy d (n + 1) with
    | .inl hlt =>
      cases d with
      | zero => rfl
      | succ d =>
        unfold List.Vector.pad
        simp
        have := hn v.tail (by omega)
        rw [List.Vector.pad_thm_le]
        · have this1 := List.Vector.take_eq_take_list (d := d) v.tail (by omega)
          have this2 := List.Vector.take_eq_take_list (d := d + 1) v (by omega)
          rw [←this1]
          rw [←this2]
          convert_to v.head ::ᵥ (v.tail.take d) = Nat.succ_min_succ _ _ ▸ v.take d.succ
          · aesop
          · sorry -- TODO: This seems like an obvious HEq goal
          · simp
          · convert List.Vector.take_cons_head_tail v
        · omega
    | .inr (.inl heq) =>
      unfold List.Vector.pad
      subst heq
      simp
      rw [List.Vector.pad_thm_le]
      simp
      have this1 := List.Vector.take_eq_take_list (d := n) v.tail (by omega)
      have this2 := List.Vector.take_eq_take_list (d := n + 1) v (by omega)
      simp [List.Vector.tail_val] at this1
      rw [←this1]
      rw [←this2]
      convert_to v.head ::ᵥ (v.tail.take n) = (aaasdf n) ▸ v.take n.succ
      · simp
      · sorry -- TODO: This seems like an obvious HEq goal
      · simp
      · convert List.Vector.take_cons_head_tail v
      omega
    | .inr (.inr hgt) => linarith

abbrev paddedInput : ZMod lp.natVal → List.Vector (U 8) 32 := fun input => ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩

lemma take_get_eq_get (vec : List.Vector α n) (k : Fin (i ⊓ n)):  (vec.take i)[k] = vec[k] := by
  let ⟨l, _⟩ := vec
  simp [List.Vector.take, List.Vector.getElem_def]

lemma take_map_comm (vec : List.Vector α n) (f : α → β) :
    (vec.take i |>.map f) = (vec.map f |>.take i) := by
  let ⟨l, _⟩ := vec
  simp [List.Vector.get, List.Vector.take, List.Vector.map]

lemma pad_get (vec : List.Vector α n) (a : α) (i : Nat) (hi : i < n) (hi' : i < N) :
    (vec.pad N a).get ⟨i, hi'⟩ = vec.get ⟨i, hi⟩ := by
  match Nat.lt_trichotomy n N with
  | .inl hlt =>
    unfold List.Vector.pad
    cases n
    · linarith
    · have ha : ∃(k : Nat), N = k.succ := by simp; omega
      simp
      rcases ha with ⟨w, rfl⟩
      simp
      cases i
      · simp
      · rename_i t
        conv_rhs =>
          change vec.get (Fin.succ ⟨t, by omega⟩)
        rw [← List.Vector.get_tail_succ]
        conv_lhs =>
          change (vec.head ::ᵥ vec.tail.pad w a).get (Fin.succ ⟨t, by omega⟩)
        rw [List.Vector.get_cons_succ]
        rw [pad_get]
  | .inr (.inl eq) =>
    let ⟨l, _⟩ := vec
    simp [List.Vector.pad, List.Vector.get]
    rw [List.Vector.pad_thm_le]
    simp
    omega
  | .inr (.inr gt) =>
    let ⟨l, _⟩ := vec
    simp [List.Vector.pad, List.Vector.get]
    rw [List.Vector.pad_thm_le]
    simp
    omega

lemma drop_get (vec : List.Vector α n) (d i : Nat) (h : d + i < n) :
    (vec.drop d |>.get ⟨i, by omega⟩) = vec.get ⟨d + i, h⟩ := by
  rcases vec with ⟨l, rfl⟩
  unfold List.Vector.get List.Vector.drop
  simp

lemma take_pad_lt (vec : List.Vector α n) (a : α) (d : Nat) (h : d < n)
    : (vec.take d |>.pad d a) = Nat.min_eq_left (Nat.le_of_lt h) ▸ vec.take d := by
  cases d
  · convert_to List.Vector.nil = ⟨List.take 0 vec.val, by simp [List.take_length]⟩
    unfold List.Vector.take
    simp
    conv_lhs =>
      congr
      change ⟨[], _⟩
    apply List.Vector.eq
    rw [List.Vector.toList_cast]
    simp
    rfl
  · sorry -- TODO: haven't thought hard about this

lemma take_pad_eq (vec : List.Vector α n) (a : α) (d : Nat) (h : d ≤ n) :
    (vec.take d |>.pad d a) = (Nat.min_eq_left h ▸ vec.take d) := by
  sorry -- TODO: haven't thought hard about this

lemma take_succ_pad (vec : List.Vector α n) (a : α) (i : Nat) (hi : i < n) (hi' : i < N) :
    (vec |>.take (i + 1) |>.pad N a) = (vec |>.take i |>.pad N a |>.set ⟨i, hi'⟩ (vec.get ⟨i, hi⟩))
    := by
  sorry -- TODO: haven't thought hard about this

lemma take_succ_map_pad_eq (vec : List.Vector α n) (b : β) (f : α → β) (i : Nat) (hi : i < n) (hi' : i < N):
    (vec |>.take (i + 1)
         |>.map f
         |>.pad N b) =
    (vec |>.take i
         |>.map f
         |>.pad N b
         |>.set ⟨i, hi'⟩ (f (vec.get ⟨i, hi⟩))) := by
    rw [take_map_comm, take_map_comm]
    have := take_succ_pad (vec.map f) b i (n := n) (N := N) hi hi'
    convert this
    · simp

lemma List.Vector.cast_head {n m : Nat} (h : n = m) (vec : List.Vector α n.succ) :
    (h ▸ vec).head = vec.head := by
  cases vec
  cases h
  rfl

lemma List.Vector.take_head {n d : Nat} (vec : List.Vector α n.succ) (d : Nat) (h : d.succ < n.succ) :
    vec.head = ((Nat.succ_min_succ _ _ ▸ vec.take d.succ) : List.Vector α (min d n ).succ).head := by
  sorry -- TODO: Haven't thought hard about this

lemma List.Vector.take_eq_self_iff (vec : List.Vector α n) : vec.take n = (Nat.min_self n |>.symm) ▸ vec := by
  rcases vec with ⟨l, p⟩
  simp [List.Vector.take]
  congr
  have := List.take_eq_self_iff l (n := n) |>.mpr (by omega)
  rw [this]
  sorry -- TODO: Some annoying cast issue

lemma List.Vector.take_append (vec₁ : List.Vector α n₁) (vec₂ : List.Vector α n₂) :
    (vec₁.append vec₂ |>.take n₁) = (Nat.min_eq_left (Nat.le_add_right _ _)) ▸ vec₁ := by
  cases vec₁
  cases vec₂
  unfold List.Vector.take
  split
  aesop
  unfold List.Vector.append at heq
  simp_all
  have : l = val ++ val_1 := by
    cases heq
    rfl
  simp [this]
  congr
  sorry -- TODO: Some annoying cast issue

lemma List.Vector.map_append (vec₁ : List.Vector α n₁) (vec₂ : List.Vector α n₂) (f : α → β) :
    (vec₁.append vec₂).map f = (vec₁.map f).append (vec₂.map f) := by
  cases vec₁
  cases vec₂
  simp [List.Vector.map, List.Vector.append]

lemma upList {l₁ l₂ : List α} {len} (hl₁ : l₁.length = len) (hl₂ : l₂.length = len):
  (Subtype.mk l₁ hl₁ : List.Vector α len) = (Subtype.mk l₂ hl₂ : List.Vector α len) → l₁ = l₂ := by
  intro h
  cases h
  rfl

lemma List.Vector.pad_eq_listpad {d : Nat} {a : α} (vec : List.Vector α n) (h : n ≤ d)
    : vec.pad d a = ⟨vec.val.rightpad d a, by simp [h]⟩ := by
  sorry -- TODO: Haven't thought hard about this

lemma rightpad_taked_set_succ (a : α) (d N : Nat) (l : List α) (h : d < l.length):
  (l.takeD d a |>.rightpad N a |>.set d l[d]) = (l.takeD (d + 1) a |>.rightpad N a) := by
  sorry -- TODO: Haven't thought hard about this

theorem as_array_intro (hi : input.length = 32) : STHoare lp env ⟦⟧ (Expr.call [Tp.slice (Tp.u 8)] (Tp.array (Tp.u 8) 32) (FuncRef.decl "as_array" [] HList.nil) h![input])
    fun output => output = ⟨input, hi⟩ := by
  enter_decl
  simp only [as_array]
  steps
  loop_inv fun i _ _ => [array ↦ ⟨Tp.array (Tp.u 8) 32, List.Vector.pad ⟨input.takeD i.toNat 0#8, List.takeD_length i.toNat _ _⟩ 32 0#8⟩]
  · decide
  · intros i hlo hhi
    steps
    congr
    simp_all [Access.modify]
    have hisucc : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by simp; omega
    simp only [hisucc]
    have := List.Vector.pad_eq_listpad (d := 32) (a := 0#8) ⟨List.takeD (BitVec.toNat i) input 0#8, List.takeD_length i.toNat _ _⟩ (by omega)
    simp only [this]
    have := List.Vector.pad_eq_listpad (d := 32) (a := 0#8) ⟨List.takeD (BitVec.toNat i + 1) input 0#8, List.takeD_length (i.toNat + 1) _ _⟩ (by omega)
    rename_i h _
    have len1 : (List.rightpad 32 (0#8) (List.takeD (BitVec.toNat i) input 0#8)).length = BitVec.toNat 32#32 := by
      simp [h]
      omega
    have len2 : (List.rightpad 32 0#8 (⟨List.takeD (BitVec.toNat i + 1) input 0#8, List.takeD_length (i.toNat + 1) _ _⟩ : List.Vector (U 8) (i.toNat + 1)).val |>.length) = 32 := by
      simp [h]
      omega
    convert_to List.Vector.set ⟨List.rightpad 32 (0#8) (List.takeD (BitVec.toNat i) input 0#8), len1⟩ ⟨BitVec.toNat i, hhi⟩ input[BitVec.toNat i] = ⟨List.rightpad 32 0#8 (⟨List.takeD (BitVec.toNat i + 1) input 0#8, List.takeD_length (i.toNat + 1) _ _⟩ : List.Vector (U 8) (i.toNat + 1)).val, len2⟩
    convert this
    unfold List.Vector.set
    congr
    simp only
    have := rightpad_taked_set_succ 0#8 (i.toNat) 32 input (by omega)
    rw [this]
  · steps []
    simp_all
    have : BitVec.toNat (n := 32) (IntCast.intCast 32) = 32 := by rfl
    rw [this]
    simp [List.take_self_eq_iff, List.takeD_eq_take, hi, List.Vector.pad_eq_self]
    congr
    have : input.head?.getD 0#8 = input[0] := by
      simp [List.head?_eq_head, List.ne_nil_of_length_eq_add_one, hi, Option.getD_some, List.head_eq_getElem]
    rw [this]
    apply Eq.symm
    apply upList hi rfl
    rw [←List.Vector.ofFn_get (v:=⟨input, hi⟩)]
    rfl

set_option maxHeartbeats 500000000000000 in
theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [bar]
  steps [to_le_bytes_intro]

  loop_inv fun (i: U 32) _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · decide
  · intro i _ hlt
    steps [sbox_intro]

    casesm* ∃_,_
    subst_vars
    simp [Builtin.CastTp.cast, Access.modify]
    congr
    have : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by
      set iNat := i.toNat
      simp
      have : iNat < 16 := by aesop
      omega
    rw [this]
    have : i.toNat < 16 := by aesop
    apply Eq.symm
    convert take_succ_map_pad_eq ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩ 0#8 Skyscraper.sbox i.toNat (by omega) this

  steps

  loop_inv fun (i: U 32) _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · decide
  · intro i _ hlt
    steps [sbox_intro]
    casesm* ∃_,_
    subst_vars
    simp [Builtin.CastTp.cast, Access.modify]
    congr
    have : (BitVec.toNat i + 1) % 4294967296 = BitVec.toNat i + 1 := by
      set iNat := BitVec.toNat i
      simp
      have : iNat < 16 := by aesop
      omega
    rw [this]
    have weirdcast : BitVec.toNat (BitVec.instIntCast.intCast 16 : U 32) = 16 := by decide
    have ilt : BitVec.toNat i < 16 := by aesop
    have :
    List.Vector.get ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩ ⟨(16 + BitVec.toNat i) % 4294967296, by omega⟩ =
    (List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩ |>.get (BitVec.toNat i)) := by
      have i16lt : (16 + i.toNat) % 4294967296 = 16 + i.toNat := by omega
      simp [i16lt]
      have asdf := drop_get ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩ 16 i.toNat (by omega)
      convert asdf.symm
      aesop
    conv_lhs =>
      congr
      · skip
      · skip
      · congr
        congr
        · skip
        · congr
          congr
          congr
          · rw [weirdcast]
    rw [this]
    have asdf :=
    take_succ_map_pad_eq (List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩) 0#8 Skyscraper.sbox (BitVec.toNat i) (by omega) ilt
    convert asdf.symm
    simp [ilt]

  steps []

  loop_inv fun (i : U 32) _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice,  bytes.drop 16 |>.append (bytes.take 16) |>.map Skyscraper.sbox |>.take (16 + i.toNat) |>.toList⟩]
  · decide
  · congr
    subst_vars
    change (List.Vector.map Skyscraper.sbox (List.Vector.take 16 (List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩))).pad 16 0 = List.Vector.take (16) (List.Vector.map Skyscraper.sbox ((List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩).append (List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)))
    rw [take_map_comm]
    rw [take_pad_eq]
    · simp
      rw [List.Vector.map_append]
      have := List.Vector.take_append (List.Vector.map Skyscraper.sbox ((List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩))) (List.Vector.map Skyscraper.sbox (List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩))
      simp at this
      simp [this, List.Vector.take_eq_self_iff]
    · decide
  · intros i hilo hihi
    steps
    subst_vars
    simp [Builtin.CastTp.cast, Access.modify]
    congr
    have : 16 + (BitVec.toNat i + 1) % 4294967296 = 16 + BitVec.toNat i + 1 := by
      set iNat := BitVec.toNat i
      have : iNat < 16 := by aesop
      omega
    rw [this]
    apply List.ext_getElem
    · simp
      have : (padEnd 32 (toLeBytes input)).length = 32 := toLeBytesPadLen
      rw [this]
      rename_i hhi _ _ _
      simp at hhi
      have : i.toNat < 16 := by
        change i.toNat < (16#32).toNat
        aesop
      omega
    · intro n hn hn'
      simp [List.getElem_append]
      have : (padEnd 32 (toLeBytes input)).length = 32 := toLeBytesPadLen
      simp [this]
      match Nat.lt_trichotomy n 16 with
      | .inl lt =>
        simp_all [lt]
        have : (n < 16 + i.toNat ∧ n < 32) := by
          constructor
          · omega
          · omega
        simp [this]
      | .inr (.inl eq) =>
        simp [eq]
        match Nat.lt_trichotomy 0 i.toNat with
        | .inl lt =>
          simp_all [lt]
        | .inr (.inl eq) =>
          simp_all [eq]
          conv_rhs =>
            congr
            congr
            · skip
            · rw [←eq]
          casesm*∃_,_
          simp_all
          apply Eq.symm
          convert_to Skyscraper.sbox (padEnd 32 (toLeBytes input))[0] = ((List.Vector.map Skyscraper.sbox (List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)).pad 16 0).get ⟨0, by aesop⟩
          conv_lhs =>
            congr
            · congr
              · skip
              · rw [←eq]
          congr
          · simp [eq]
          · simp [eq]
          · rw [take_map_comm]
            have := pad_get (N := 16) (List.Vector.take 16 (List.Vector.map Skyscraper.sbox ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)) 0 0 (by omega) (by omega)
            rw [this]
            unfold List.Vector.take List.Vector.get
            simp; split
            rename_i heq
            rcases heq
            simp only [List.getElem_take, List.getElem_map]
        | .inr (.inr gt) =>
          simp_all [gt]
      | .inr (.inr gt) =>
        have : ¬(n < 16) := by omega
        simp [this]
        match Nat.lt_trichotomy n (16 + i.toNat) with
        | .inl lt =>
          simp_all
          have : i.toNat < 16 := by
            exact hihi
          have : n < 32 := by
            calc n < 16 + i.toNat := by assumption
                 _ < 16 + 16 := by omega
                 _ = 32 := by decide
          simp [this]
        | .inr (.inl eq) =>
          casesm*∃_,_
          simp_all [eq]
          subst_vars
          rw [take_map_comm]
          change ((List.Vector.take 16 (List.Vector.map Skyscraper.sbox ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)).pad 16 0#8).get ⟨BitVec.toNat i, hihi⟩ = Skyscraper.sbox (padEnd 32 (toLeBytes input))[BitVec.toNat i]
          simp [take_pad_eq]
          simp [List.Vector.get, List.Vector.map, List.Vector.take]
        | .inr (.inr gt) =>
          casesm*∃_,_
          have : ¬(n < 16 + i.toNat) := by omega
          simp only [this]
          simp
          subst_vars
          simp [toLeBytesPadLen] at hn
          have : n - 16 < (padEnd 32 (toLeBytes input)).length := by
            rw [toLeBytesPadLen]
            omega
          change  ((List.Vector.map Skyscraper.sbox (List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)).pad 16 0).get ⟨i.toNat, hihi⟩ = Skyscraper.sbox (padEnd 32 (toLeBytes input))[n - 16]
          rw [take_map_comm]
          sorry -- Is this even true? RHS doesn't have any `i` dependence...`

  steps [as_array_intro]
  · subst_vars
    simp [toLeBytesPadLen]
  · steps [from_le_bytes_intro]
    unfold Skyscraper.bar
    simp
    subst_vars
    congr 1
    simp
    have : (List.drop 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input))) ++ List.take 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input)))).length = 32 := by
      simp [toLeBytesPadLen]
    have := (List.take_eq_self_iff (n := 32) (List.drop 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input))) ++ List.take 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input)))) |>.mpr) (by omega)
    apply this

theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
    fun output => output = Skyscraper.bar input := by
  enter_decl
  apply bar_spec

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
      fun output => output = Skyscraper.SIGMA := by
  enter_decl
  simp only [Extracted.SIGMA]
  steps []
  unfold Skyscraper.SIGMA
  assumption

theorem rc_intro : STHoare lp env (⟦⟧)
    (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
      fun output => output = ⟨Skyscraper.RC.toList, by rfl⟩ := by
  enter_decl
  simp only [Extracted.RC]
  steps []
  subst_vars
  unfold Skyscraper.RC
  rfl

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Skyscraper.square input := by
  enter_decl
  simp only [Extracted.square]
  steps [sigma_intro]
  unfold Skyscraper.square
  subst_vars
  rfl

theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
    fun output => output = (Skyscraper.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Skyscraper.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by sorry -- TODO: This has a bad timeout now?
  -- enter_decl
  -- simp only [Extracted.permute]
  -- steps [bar_intro, square_intro, rc_intro]
  -- casesm* ∃_,_
  -- simp [Builtin.indexTpl] at *
  -- subst_vars
  -- unfold Skyscraper.permute

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  simp only [compress]
  steps [permute_intro]
  unfold Skyscraper.compress
  subst_vars
  simp [Skyscraper.State.permute]
  casesm*∃_,_
  subst_vars
  simp
  congr 1
