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

-- lemma SLP.pure_star_iff_and [LawfulHeap α] {H : SLP α} : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
--   simp [SLP.star, SLP.lift]
--   apply Iff.intro
--   · rintro ⟨st₁, st₂, hdis, hst, ⟨hp, rfl⟩, hH⟩
--     simp only [LawfulHeap.empty_union] at hst
--     cases hst
--     simp_all
--   · intro ⟨hP, hH⟩
--     exists ∅, st
--     simp_all

lemma STHoare.pure_left_of_imp (h : P → STHoare lp Γ ⟦P⟧ E Q): STHoare lp Γ ⟦P⟧ E Q := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

-- lemma STHoare.pluck_pures : (P → STHoare lp Γ H e Q) → (STHoare lp Γ (P ⋆ H) e (fun v => P ⋆ Q v)) := by
--   intro h
--   simp_all [STHoare, THoare, SLP.pure_star_iff_and]

lemma STHoare.pure_left {E : Expr (Tp.denote lp) tp} {Γ P Q} : (P → STHoare lp Γ ⟦True⟧ E Q) → STHoare lp Γ ⟦P⟧ E Q := by
  intro h
  apply STHoare.pure_left_of_imp
  intro
  apply STHoare.consequence (h_hoare := h (by assumption))
  · simp [SLP.lift, SLP.entails]
  · intro; apply SLP.entails_self

-- lemma STHoare.pure_left_star {p tp} {E : Expr (Tp.denote p) tp} {Γ P₁ P₂ Q} : (P₁ → STHoare  p Γ P₂ E Q) → STHoare p Γ (⟦P₁⟧ ⋆ P₂) E Q := by
--   intro h
--   intro H st Hh
--   unfold STHoare THoare at h
--   apply h
--   · simp [SLP.star, SLP.lift, SLP.entails] at Hh
--     casesm* ∃_,_, _∧_
--     assumption
--   · simp only [SLP.star, SLP.lift, SLP.entails] at Hh
--     rcases Hh with ⟨s₁, s₂, hdss, rfl, ⟨s₃, s₄, hdsss, rfl, ⟨⟨hp, rfl⟩⟩⟩, _⟩
--     unfold SLP.star
--     exists s₄
--     exists s₂
--     simp_all [LawfulHeap.union_empty, LawfulHeap.empty_union]

-- TODO fix this in Lampe
axiom castField_u1_intro {p Γ f}: STHoare p Γ ⟦⟧ (Expr.callBuiltin [Tp.field] (Tp.u 1) Builtin.cast h![f]) fun o => o = f.val % 2
axiom castU_self {p Γ s u} : STHoare p Γ ⟦⟧ (Expr.callBuiltin [Tp.u s] (Tp.u s) Builtin.cast h![u]) fun o => o = u

-- lemma STHoare.letIn_trivial_intro {p tp₁ tp₂} {P Q} {E : Expr (Tp.denote p) tp₁} {v'} {cont : Tp.denote p tp₁ → Expr (Tp.denote p) tp₂}
--     (hE : STHoare p Γ ⟦True⟧ E (fun v => v = v'))
--     (hCont : STHoare p Γ P (cont v') Q):
--     STHoare p Γ P (E.letIn cont) Q := by
--   apply STHoare.letIn_intro
--   apply STHoare.ramified_frame_top hE (Q₂:= fun v => ⟦v = v'⟧ ⋆ P)
--   · simp
--     apply SLP.forall_right
--     intro
--     apply SLP.wand_intro
--     rw [SLP.star_comm]
--     apply SLP.pure_left
--     rintro rfl
--     simp
--   · intro
--     apply STHoare.pure_left_star
--     rintro rfl
--     assumption

syntax "trivial_steps" ("[" term,* "]")?: tactic
macro_rules
| `(tactic|trivial_steps []) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro
      (first
      | apply STHoare.fn_intro
      | apply STHoare.litU_intro
      | apply STHoare.litField_intro
      | apply castField_u1_intro
      | apply castU_self
      | apply (STHoare.consequence (h_hoare := STHoare.fMul_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uNot_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uAnd_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uXor_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uOr_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uShr_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.uShl_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      | apply (STHoare.consequence (h_hoare := STHoare.mkArray_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
      )
    | apply STHoare.var_intro
  )
)
macro_rules | `(tactic|trivial_steps [$x]) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro; apply $x
    | trivial_steps []
  )
)
macro_rules | `(tactic|trivial_steps [$x,$xs:term,*]) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro; apply $x
    | trivial_steps [$xs,*]
  )
)

theorem callDecl_direct_intro {p} {Γ : Env} {func} {args} {Q H}
    (h_found : (Γ.functions.find? (fun (n, f) => n = fnName)) = some (fnName, func))
    (hkc : func.generics = kinds)
    (htci : (func.body _ (hkc ▸ generics) |>.argTps) = argTps)
    (htco : (func.body _ (hkc ▸ generics) |>.outTp) = outTp)
    (h_hoare: STHoare p Γ H (htco ▸ (func.body _ (hkc ▸ generics) |>.body (htci ▸ args))) (htco ▸ Q)) :
    STHoare p Γ H (Expr.call argTps outTp (.decl fnName kinds generics) args) Q := by
  apply STHoare.callDecl_intro (fnName := fnName) (outTp := outTp) (generics := generics)
  · exact func
  · simp [SLP.entails_top]
  all_goals sorry

syntax "enter_fn" : tactic
macro_rules | `(tactic|enter_fn) => `(tactic|apply callDecl_direct_intro (by rfl) (by rfl) (by rfl) (by rfl))

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

-- This is almost certainly stated incorrectly, but something like this is true
theorem bitvec_lt (w : Nat) (b N : BitVec w) (hb : b < N) (hN : N < (2 ^ w : Nat) - 1)
    : b.toNat < N.toNat := by
  sorry

lemma SLP.exists_true [LawfulHeap α] (Q : (x : True) → SLP α) : (∃∃ (x : True), Q x) = Q ⟨⟩ := by
  unfold SLP.exists'
  funext st
  simp only [←iff_iff_eq]
  apply Iff.intro
  · rintro ⟨_, h⟩
    exact h
  · intro h
    exact ⟨⟨⟩, h⟩

lemma SLP.exists_prop_unused [LawfulHeap α] (P : Prop) (Q : SLP α) : (∃∃ (_ : P), Q) = (P ⋆ Q) := by
  apply SLP.eq_of_iff
  · apply exi_prop_l
    intro
    apply SLP.entails_self
  · apply SLP.pure_left
    intro
    apply SLP.exists_intro
    apply SLP.entails_self
    assumption

lemma rfl_iff_true : α = α ↔ True := by tauto


set_option trace.Lampe.SL true

theorem pluck_pure_exi_l' [LawfulHeap α] {P : Prop} {f : β → SLP α} : (SLP.exists' f ⋆ P) = (P ⋆ SLP.exists' f) := by
  simp [SLP.star_comm]


theorem rotateLeft_spec : STHoare lp env ⟦N < 254⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Skyscraper.rotateLeft input N := by
  simp only [Extracted.rotate_left]

  steps
  loop_inv fun i _ _ => [result ↦ ⟨Tp.u 8, Nat.repeat Skyscraper.rl i.toNat input⟩]
  · intros i hlo hhi
    steps
    · apply STHoare.consequence_frame_left rl_intro
      sl
    · steps
      intro
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
  · simp only [Int.cast, IntCast.intCast]
    bv_decide
  · simp only [SLP.exists_prop_unused]
    steps
    simp_all
    rfl

theorem star_lift_entails {α : Type _} [LawfulHeap α] (P Q : Prop) : (⟦P⟧ : SLP α) ⋆ ⟦Q⟧ ⊢ ⟦Q⟧ := by
  intro st ⟨st1, ⟨st2, ⟨_, ⟨h12, ⟨p, h1⟩, q, h2⟩⟩⟩⟩
  have : st = ∅ := by
    rw [h12, h1, h2]
    exact LawfulHeap.union_empty
  tauto

theorem rotate_left_intro : STHoare lp env ⟦N < 254⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  enter_fn
  apply STHoare.consequence (h_hoare := rotateLeft_spec)
  simp_all [SLP.entails]
  simp [SLP.star, SLP.top, SLP.entails]

set_option pp.rawOnError true

set_option trace.Lampe.STHoare.Helpers true

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  simp only [sbox]
  steps' [rotate_left_intro]
  any_goals (intro; decide)
  intro
  subst_vars
  rfl

theorem sbox_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.u 8] (Tp.u 8) (FuncRef.decl "sbox" [] HList.nil) h![input])
    fun output => output = Skyscraper.sbox input := by
  enter_fn
  apply sbox_spec

theorem sgn0_spec : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.u 1) (FuncRef.decl "sgn0" [] HList.nil) h![input])
    fun output => output = (input.val % 2) := by
  enter_fn
  simp only [sgn0]
  steps
  rintro rfl
  simp_all

opaque BitVec.bytesLE : BitVec n → List.Vector (U 8) n

axiom toLeBytesPadLen {input : Lampe.Fp lp} : (padEnd 32 (Lampe.toLeBytes input)).length = 32

axiom to_le_bytes_intro {input} : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.array (Tp.u 8) 32) (FuncRef.decl "to_le_bytes" [] HList.nil) h![input])
    fun output => output = ⟨padEnd 32 (Lampe.toLeBytes input), toLeBytesPadLen⟩

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
    sorry -- This seems like an obvious HEq goal
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
          · sorry -- This seems like an obvious HEq goal
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
      · sorry -- This seems like an obvious HEq goal
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
  · sorry

lemma take_pad_eq (vec : List.Vector α n) (a : α) (d : Nat) (h : d ≤ n) :
    (vec.take d |>.pad d a) = (Nat.min_eq_left h ▸ vec.take d) := by
  sorry

lemma take_succ_pad (vec : List.Vector α n) (a : α) (i : Nat) (hi : i < n) (hi' : i < N) :
    (vec |>.take (i + 1) |>.pad N a) = (vec |>.take i |>.pad N a |>.set ⟨i, hi'⟩ (vec.get ⟨i, hi⟩))
    := by
  sorry

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
  sorry

set_option maxHeartbeats 5000000000000

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [bar]
  steps' [to_le_bytes_intro]

  loop_inv fun (i: U 32) _ _ => [new_left ↦ ⟨(Tp.u 8).array 16, bytes.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · intro i _ hlt
    steps' [sbox_intro]
    · intro
      casesm* ∃_,_
      subst_vars
      simp [Builtin.CastTp.cast, Access.modify]
      -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
      congr
      have : (i.toNat + 1) % 4294967296 = i.toNat + 1 := by
        set iNat := i.toNat
        simp
        have : iNat < 16 := by aesop
        omega
      rw [this]
      have : i.toNat < 16 := by aesop
      convert take_succ_map_pad_eq ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩ 0#8 Skyscraper.sbox i.toNat (by omega) this
  · decide

  steps

  loop_inv fun (i: U 32) _ _ => [new_right ↦ ⟨(Tp.u 8).array 16, bytes.drop 16 |>.take i.toNat |>.map Skyscraper.sbox |>.pad 16 (0:U 8)⟩]
  · intro i _ hlt
    steps' [sbox_intro]
    · intro
      casesm* ∃_,_
      subst_vars
      simp [Builtin.CastTp.cast, Access.modify]
      -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
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
      conv_rhs =>
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
      convert asdf
      simp [ilt]
  · decide

  steps' []
  on_goal 2 => intro; rfl

  loop_inv fun (i : U 32) _ _ => [new_bytes ↦ ⟨(Tp.u 8).slice,  bytes.drop 16 |>.append (bytes.take 16) |>.map Skyscraper.sbox |>.take (16 + i.toNat) |>.toList⟩]
  · intro i _ _
    steps
    · intro
      casesm* ∃_,_
      subst_vars
      simp [Builtin.CastTp.cast, Access.modify]
      -- THIS IS A SOLVABLE GOAL ABOUT VECTORS
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
            conv_lhs =>
              congr
              congr
              · skip
              · rw [←eq]
            conv_rhs =>
              congr
              · skip
              · congr
                rw [←eq]
            convert_to Skyscraper.sbox (padEnd 32 (toLeBytes input))[0] = ((List.Vector.map Skyscraper.sbox (List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)).pad 16 0).get ⟨0, by aesop⟩

            have asdf :=
              pad_get (N := 16) (((List.Vector.take 16 ⟨padEnd 32 (toLeBytes input), toLeBytesPadLen⟩)).map Skyscraper.sbox) 0#8 0 (by omega) (by omega)
            convert asdf.symm
            simp
            congr
            sorry -- Should use List.take_head + List.Vector.cast_head ....
          | .inr (.inr gt) =>
            simp_all [gt]
        | .inr (.inr gt) =>
          have : ¬(n < 16) := by omega
          simp [this]
          match Nat.lt_trichotomy n (16 + i.toNat) with
          | .inl lt =>
            simp_all
            have : n < 32 := by
              simp [toLeBytesPadLen] at hn
              exact hn.right
            simp [this]
          | .inr (.inl eq) =>
            simp [eq]
            sorry -- Continue this, should be a continuation of pad_get etc...
          | .inr (.inr gt) =>
            aesop
            sorry -- Continue this, should be a continuation of pad_get etc...

  · simp [BitVec.le_def, Int.cast, IntCast.intCast]

  steps' []

  · simp_all
    congr
    apply List.ext_getElem
    simp [toLeBytesPadLen]
    change 16 = min 16 32
    decide
    intro n h1 h2
    change ((List.Vector.map Skyscraper.sbox
            (List.Vector.take 16 (List.Vector.drop 16 ⟨padEnd 32 (toLeBytes input),
            toLeBytesPadLen⟩))).pad 16 0#8).toList[n] = (List.take 16 (List.drop 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input))) ++ List.take 16 (List.map Skyscraper.sbox (padEnd 32 (toLeBytes input)))))[n]
    rename_i a a_1 h
    subst a
    simp_all only [Nat.reduceSub, List.getElem_take]
    obtain ⟨left, right⟩ := a_1
    subst right
    simp [take_map_comm]
    simp [take_pad_eq]
    simp only [List.Vector.toList_length] at h1
    simp [List.getElem_append, toLeBytesPadLen, h1]

  steps' []

#exit

theorem bar_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field] Tp.field (FuncRef.decl "bar" [] HList.nil) h![input])
    fun output => output = Skyscraper.bar input := by
  enter_fn
  apply bar_spec

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
      fun output => output = Skyscraper.SIGMA := by
  enter_fn
  simp only [Extracted.SIGMA]
  steps' []

theorem rc_intro : STHoare lp env (⟦⟧)
    (Expr.call [] (Tp.field.array 8) (FuncRef.decl "RC" [] HList.nil) h![])
      fun output => output = ⟨Skyscraper.RC.toList, by rfl⟩ := by
  enter_fn
  simp only [Extracted.RC]
  steps' []

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Skyscraper.square input := by
  enter_fn
  simp only [Extracted.square]
  steps' [sigma_intro]

set_option trace.Lampe.STHoare.Helpers false
set_option trace.Lampe.SL false

theorem permute_intro : STHoare lp env ⟦⟧ (Expr.call [Tp.field.array 2] (Tp.field.array 2) (FuncRef.decl "permute" [] HList.nil) h![i])
    fun output => output = (Skyscraper.permute ⟨i[0], i[1]⟩).1 ::ᵥ (Skyscraper.permute ⟨i[0], i[1]⟩).2 ::ᵥ List.Vector.nil := by
  enter_fn
  simp only [Extracted.permute]
  steps' [bar_intro, square_intro, rc_intro]
  casesm* ∃_,_
  simp [Builtin.indexTpl] at *
  intro
  subst_vars
  rfl

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  simp only [compress]
  sorry
