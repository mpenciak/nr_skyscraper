import Skyscraper.Ref
import Skyscraper.Extracted

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

lemma SLP.pure_star_iff_and [LawfulHeap α] {H : SLP α} : (⟦P⟧ ⋆ H) st ↔ P ∧ H st := by
  simp [SLP.star, SLP.lift]
  apply Iff.intro
  · rintro ⟨st₁, st₂, hdis, hst, ⟨hp, rfl⟩, hH⟩
    simp only [LawfulHeap.empty_union] at hst
    cases hst
    simp_all
  · intro ⟨hP, hH⟩
    exists ∅, st
    simp_all

lemma STHoare.pure_left_of_imp (h : P → STHoare lp Γ ⟦P⟧ E Q): STHoare lp Γ ⟦P⟧ E Q := by
  simp_all [STHoare, THoare, SLP.pure_star_iff_and]

lemma STHoare.pure_left {E : Expr (Tp.denote lp) tp} {Γ P Q} : (P → STHoare lp Γ ⟦True⟧ E Q) → STHoare lp Γ ⟦P⟧ E Q := by
  intro h
  apply STHoare.pure_left_of_imp
  intro
  apply STHoare.consequence (h_hoare := h (by assumption))
  · simp [SLP.lift, SLP.entails]
  · intro; apply SLP.entails_self

lemma STHoare.pure_left_nontriv {E : Expr (Tp.denote lp) tp} {Γ P Q}
    : (P → STHoare lp Γ H E Q) → STHoare lp Γ (⟦P⟧ ⋆ H) E Q := by
  intro h
  simp_all only [STHoare, THoare, SLP.star_assoc, SLP.pure_star_iff_and, implies_true]

theorem rl_spec : STHoare lp env ⟦⟧ (rl.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.rl input := by
  simp only [rl, Skyscraper.rl]
  steps
  intro h
  simp_all
  rfl

theorem rl_intro : STHoare lp env ⟦v = FuncRef.decl "rl" [] HList.nil⟧
  (Expr.call [Tp.u 8] (Tp.u 8) v h![input])
    fun output => output = Skyscraper.rl input := by
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.rl.fn
  all_goals try tauto
  · fapply STHoare.consequence
    · exact ⟦⟧
    · exact fun u => ⟦u = Skyscraper.rl input⟧
    · rintro _ ⟨_, r⟩ -- H ⊢ ⟦True⟧ should be obvious right?
      exact ⟨.intro, r⟩
    · intro h
      simp [SLP.entails_self]
    · convert rl_spec

-- This is almost certainly stated incorrectly, but something like this is true
theorem bitvec_lt (w : Nat) (b N : BitVec w) (hb : b < N) (hN : N < (2 ^ w : Nat) - 1)
    : b.toNat < N.toNat := by
  sorry

theorem rotateLeft_spec : STHoare lp env ⟦N < 254⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Skyscraper.rotateLeft input N := by
  simp only [Extracted.rotate_left]
  apply STHoare.pure_left_of_imp
  intro h
  steps
  rename_i a _
  loop_inv fun i _ _ => [a ↦ ⟨Tp.u 8, Nat.repeat Skyscraper.rl i.toNat input⟩]
  · intros i hlo hhi
    steps
    · apply STHoare.consequence_frame_left rl_intro
      sl
      assumption
    · steps
      · congr
        simp_all
        have i_lt : i < 254 := by bv_decide
        have i_succ_lt : i + 1 < 255 := by bv_decide
        have x := bitvec_lt 8 i N hhi (by bv_decide)
        have y := bitvec_lt 8 N 254 h (by decide)
        set iNat := BitVec.toNat i
        have : (iNat + 1) % 256 = iNat + 1 := by
          simp_all
          linarith
        rw [this]
        rfl
  · rename_i b c d
    change b = 0 at c
    bv_decide
  · congr
    rename_i b c d e
    change b = 0 at d
    rw [d]
    rfl
  · steps
    subst_vars
    rfl

theorem star_lift_entails {α : Type _} [LawfulHeap α] (P Q : Prop) : (⟦P⟧ : SLP α) ⋆ ⟦Q⟧ ⊢ ⟦Q⟧ := by
  intro st ⟨st1, ⟨st2, ⟨_, ⟨h12, ⟨p, h1⟩, q, h2⟩⟩⟩⟩
  have : st = ∅ := by
    rw [h12, h1, h2]
    exact LawfulHeap.union_empty
  tauto

theorem rotate_left_intro : STHoare lp env (⟦v = FuncRef.decl "rotate_left" [] HList.nil⟧ ⋆ ⟦N < 254⟧)
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) v h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.rotate_left.fn
  all_goals try tauto
  · simp [env, Extracted.rotate_left]
  · fapply STHoare.consequence
    · exact ⟦N < 254⟧
    · exact fun output => ⟦output = Skyscraper.rotateLeft input N⟧
    · apply star_lift_entails
    · intro h
      simp [SLP.entails_self]
    · convert rotateLeft_spec


theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  simp only [Extracted.sbox]

  apply STHoare.letIn_intro
  apply STHoare.uNot_intro
  -- intro v1; apply STHoare.pure_left
  simp only [BitVec.not, exists_const]
  intro v2; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.fn_intro
  intro v3; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.litU_intro
  intro v4; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence (h_hoare := rotate_left_intro)
    (h_post_conseq := fun _ => SLP.entails_self)
  simp [SLP.entails, SLP.lift]
  decide
  intro v5; apply STHoare.pure_left; rintro rfl

  intro v6; apply STHoare.pure_left; simp only [forall_const]
  apply STHoare.letIn_intro
  apply STHoare.fn_intro
  intro v7; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.litU_intro
  intro v8; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence (h_hoare := rotate_left_intro) (h_post_conseq := fun _ => SLP.entails_self)
  simp [SLP.entails, SLP.lift]
  decide

  intro v9; apply STHoare.pure_left; rintro rfl
  apply STHoare.letIn_intro
  apply STHoare.fn_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.litU_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence (h_hoare := rotate_left_intro) (h_post_conseq := fun _ => SLP.entails_self)
  simp [SLP.entails, SLP.lift]
  decide
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.uAnd_intro
  simp only [BitVec.reduceAllOnes, exists_const]
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.uAnd_intro
  simp only [BitVec.reduceAllOnes, exists_const]
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.fn_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.litU_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence (h_hoare := rotate_left_intro) (h_post_conseq := fun _ => SLP.entails_self)
  simp [SLP.entails, SLP.lift]
  decide
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.uXor_intro
  simp only [BitVec.xor_eq, exists_const]
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.var_intro

theorem sbox_intro : STHoare lp env (⟦v = FuncRef.decl "sbox" [] HList.nil⟧)
    (Expr.call [Tp.u 8] (Tp.u 8) v h![input])
    fun output => output = Skyscraper.sbox input := by
  apply STHoare.callDecl_intro
  · sl
    exact id
  on_goal 3 => exact Extracted.sbox.fn
  all_goals try tauto
  fapply STHoare.consequence
  · exact ⟦⟧
  · exact fun output => ⟦output = Skyscraper.sbox input⟧
  · rintro _ ⟨_, r⟩
    exact ⟨.intro, r⟩
  · intro h
    exact SLP.entails_self
  exact sbox_spec

theorem to_le_bytes_spec : STHoare lp env ⟦⟧ (to_le_bytes.fn.body _ h![] |>.body h![input])
    fun output => output.toList = toLeBytes input := by sorry -- TODO: This isn't stated correctly

theorem to_le_bytes_intro : STHoare lp env (⟦v = FuncRef.decl "to_le_bytes" [] HList.nil⟧)
    (Expr.call [Tp.field] (Tp.array (Tp.u 8) 32) v h![input])
    fun output => output.toList = toLeBytes input := by
  apply STHoare.callDecl_intro
  · sl
    exact id
  on_goal 3 => exact Extracted.to_le_bytes.fn
  all_goals try tauto
  · simp [to_le_bytes, env]
  fapply STHoare.consequence
  · exact ⟦⟧
  · exact fun output => ⟦output.toList = toLeBytes input⟧
  · rintro _ ⟨_, r⟩
    exact ⟨.intro, r⟩
  · intro h
    exact SLP.entails_self
  exact to_le_bytes_spec

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar input := by
  simp only [Extracted.bar]

  apply STHoare.letIn_intro
  apply STHoare.fn_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence (h_hoare := to_le_bytes_intro)
    (h_post_conseq := fun _ => SLP.entails_self)
  simp [SLP.entails, SLP.lift]
  intro v; apply STHoare.pure_left; intro h

  apply STHoare.letIn_intro
  apply STHoare.litU_intro
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.mkArray_intro
  decide
  simp only [Nat.cast_ofNat, BitVec.ofNat_eq_ofNat, List.reduceReplicate, BitVec.reduceToNat,
    BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, exists_true_left]
  intro v; apply STHoare.pure_left; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.ref_intro
  intro left

  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left STHoare.litU_intro
  sl
  intro v; apply STHoare.pure_left_nontriv; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left STHoare.mkArray_intro
  sl
  decide
  intro v; simp?; apply STHoare.pure_left_nontriv; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left STHoare.ref_intro
  sl
  intro right

  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left STHoare.litU_intro
  sl
  intro v; apply STHoare.pure_left_nontriv; rintro rfl

  apply STHoare.letIn_intro
  apply STHoare.consequence_frame_left STHoare.litU_intro
  sl
  intro v; apply STHoare.pure_left_nontriv; rintro rfl

  sorry


theorem bar_intro : STHoare lp env (⟦v = FuncRef.decl "bar" [] HList.nil⟧)
    (Expr.call [Tp.field] (Tp.field) v h![input])
    fun output => output = Skyscraper.bar input := by
  apply STHoare.callDecl_intro
  · sl
    exact id
  on_goal 3 => exact Extracted.bar.fn
  all_goals try tauto
  · simp [env, Extracted.bar]
  fapply STHoare.consequence
  · exact ⟦⟧
  · exact fun output => ⟦output = Skyscraper.bar input⟧
  · rintro _ ⟨_, r⟩
    exact ⟨.intro, r⟩
  · intro h
    exact SLP.entails_self
  exact bar_spec

theorem sigma_intro : STHoare lp env (⟦v = FuncRef.decl "SIGMA" [] HList.nil⟧)
    (Expr.call [] Tp.field v h![])
      fun output => output = Skyscraper.SIGMA := by
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.SIGMA.fn
  all_goals try tauto
  · simp [env, Extracted.SIGMA]
  · fapply STHoare.consequence
    · exact ⟦⟧
    · exact fun output => ⟦output = Skyscraper.SIGMA⟧
    · rintro _ ⟨_, r⟩ -- H ⊢ ⟦True⟧ should be obvious right?
      exact ⟨.intro, r⟩
    · intro h
      simp [SLP.entails_self]
    · simp [Extracted.SIGMA, Skyscraper.SIGMA]
      steps
      intro h
      rename_i x y hh
      rw [h, hh]
      rfl

theorem square_spec : STHoare lp env ⟦⟧ (square.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.square input := by
  simp only [square]
  steps
  · apply STHoare.consequence_frame_left sigma_intro
    · exact SLP.entails_self
  · steps
    intro h
    rename_i a b c d e f g v
    have ⟨_, f⟩ := f
    have ⟨_, v⟩ := v
    rw [h, f, g, v, Skyscraper.square]

theorem square_intro : STHoare lp env (⟦v = FuncRef.decl "square" [] HList.nil⟧)
    (Expr.call [Tp.field] Tp.field v h![input])
      fun output => output = Skyscraper.square input := by
  apply STHoare.callDecl_intro
  · sl
    tauto
  on_goal 3 => exact Extracted.square.fn
  all_goals try tauto
  · simp [env, Extracted.square]
  · fapply STHoare.consequence
    · exact ⟦⟧
    · exact fun output => ⟦output = Skyscraper.square input⟧
    · rintro _ ⟨_, r⟩ -- H ⊢ ⟦True⟧ should be obvious right?
      exact ⟨.intro, r⟩
    · intro h
      simp [SLP.entails_self]
    · convert square_spec

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  sorry
