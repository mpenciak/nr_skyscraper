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

lemma STHoare.pure_left_star {p tp} {E : Expr (Tp.denote p) tp} {Γ P₁ P₂ Q} : (P₁ → STHoare  p Γ P₂ E Q) → STHoare p Γ (⟦P₁⟧ ⋆ P₂) E Q := by
  intro h
  intro H st Hh
  unfold STHoare THoare at h
  apply h
  · simp [SLP.star, SLP.lift, SLP.entails] at Hh
    casesm* ∃_,_, _∧_
    assumption
  · simp only [SLP.star, SLP.lift, SLP.entails] at Hh
    rcases Hh with ⟨s₁, s₂, hdss, rfl, ⟨s₃, s₄, hdsss, rfl, ⟨⟨hp, rfl⟩⟩⟩, _⟩
    unfold SLP.star
    exists s₄
    exists s₂
    simp_all [LawfulHeap.union_empty, LawfulHeap.empty_union]

-- TODO fix this in Lampe
axiom castField_u1_intro {p Γ f}: STHoare p Γ ⟦⟧ (Expr.callBuiltin [Tp.field] (Tp.u 1) Builtin.cast h![f]) fun o => o = f.val % 2

lemma STHoare.letIn_trivial_intro {p tp₁ tp₂} {P Q} {E : Expr (Tp.denote p) tp₁} {v'} {cont : Tp.denote p tp₁ → Expr (Tp.denote p) tp₂}
    (hE : STHoare p Γ ⟦True⟧ E (fun v => v = v'))
    (hCont : STHoare p Γ P (cont v') Q):
    STHoare p Γ P (E.letIn cont) Q := by
  apply STHoare.letIn_intro
  apply STHoare.ramified_frame_top hE (Q₂:= fun v => ⟦v = v'⟧ ⋆ P)
  · simp
    apply SLP.forall_right
    intro
    apply SLP.wand_intro
    rw [SLP.star_comm]
    apply SLP.pure_left
    rintro rfl
    simp
  · intro
    apply STHoare.pure_left_star
    rintro rfl
    assumption

syntax "trivial_steps" ("[" term,* "]")?: tactic
macro_rules
| `(tactic|trivial_steps []) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro STHoare.fn_intro
    | apply STHoare.letIn_trivial_intro STHoare.litU_intro
    | apply STHoare.letIn_trivial_intro STHoare.litField_intro
    | apply STHoare.letIn_trivial_intro castField_u1_intro
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.fMul_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uNot_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uAnd_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uXor_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uOr_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uShr_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.letIn_trivial_intro (STHoare.consequence (h_hoare := STHoare.uShl_intro) (h_pre_conseq := SLP.entails_self) (by intro; simp only [exists_const]; apply SLP.entails_self))
    | apply STHoare.var_intro
  )
)
macro_rules | `(tactic|trivial_steps [$x]) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro ($x)
    | trivial_steps []
  )
)
macro_rules | `(tactic|trivial_steps [$x,$xs:term,*]) => `(tactic |
  repeat1 (first
    | apply STHoare.letIn_trivial_intro ($x)
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

theorem rl_spec : STHoare lp env ⟦⟧ (rl.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.rl input := by
  simp only [rl, Skyscraper.rl]
  trivial_steps []

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

theorem rotate_left_intro (hN : N < 254) : STHoare lp env ⟦⟧
    (Expr.call [Tp.u 8, Tp.u 8] (Tp.u 8) (FuncRef.decl "rotate_left" [] HList.nil) h![input, N])
      fun output => output = Skyscraper.rotateLeft input N := by
  enter_fn
  apply STHoare.consequence (h_hoare := rotateLeft_spec)
  simp_all [SLP.entails]
  simp [SLP.star, SLP.top, SLP.entails]

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  trivial_steps [rotate_left_intro (by decide)]

theorem sgn0_spec : STHoare lp env ⟦⟧ (Expr.call [Tp.field] (Tp.u 1) (FuncRef.decl "sgn0" [] HList.nil) h![input])
    fun output => output = (input.val % 2) := by
  enter_fn
  trivial_steps []

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar output := by
  simp only [bar]
  trivial_steps []
  sorry

theorem sigma_intro : STHoare lp env (⟦⟧)
    (Expr.call [] Tp.field (FuncRef.decl "SIGMA" [] HList.nil) h![])
      fun output => output = Skyscraper.SIGMA := by
  enter_fn
  trivial_steps []

theorem square_intro : STHoare lp env (⟦⟧)
    (Expr.call [Tp.field] Tp.field (FuncRef.decl "square" [] HList.nil) h![input])
      fun output => output = Skyscraper.square input := by
  enter_fn
  trivial_steps [sigma_intro]

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  simp only [compress]
  sorry
