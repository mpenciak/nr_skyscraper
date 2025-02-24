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

-- DELETE: I thought I needed these
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

#check BitVec.ofNat_lt_ofNat
#check BitVec.toNat_ofNatLt

theorem asdf (w : Nat) (b N : BitVec w) (hb : b < N) (hN : N < (2 ^ w : Nat) - 1)
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
        have x := asdf 8 i N hhi (by bv_decide)
        have y := asdf 8 N 254 h (by decide)
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
    · unfold SLP.star
      unfold SLP.entails
      intros x y
      let ⟨st1, ⟨st2,⟨h12, ⟨a, ⟨c, d⟩⟩⟩⟩⟩ := y
      sorry
    · intro h
      simp [SLP.entails_self]
    · convert rotateLeft_spec

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox input := by
  simp only [Extracted.sbox]
  steps
  apply STHoare.consequence_frame_left rotate_left_intro
  · sl
    tauto
  · steps
    apply STHoare.consequence_frame_left rotate_left_intro
    · sl
      tauto
    · steps
      · apply STHoare.consequence_frame_left rotate_left_intro
        · sl
          tauto
      · steps
        · apply STHoare.consequence_frame_left rotate_left_intro
          · sl
            sorry
        · steps
          intro h
          simp_all [Skyscraper.sbox]
          congr
          · sorry
          · sorry

theorem bar_spec : STHoare lp env ⟦⟧ (bar.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.bar output := by
  sorry

theorem square_spec : STHoare lp env ⟦⟧ (square.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.square input := by
  simp only [square]
  steps
  simp_all
  fapply STHoare.callDecl_intro
  · exact "SIGMA"
  · exact []
  · exact h![]
  · exact Extracted.SIGMA.fn
  · sl
    intro h
    assumption
  · unfold env
    simp [Extracted.SIGMA]
  · simp [Extracted.SIGMA]
  · simp [Extracted.SIGMA]
  · simp [Extracted.SIGMA]
  · simp [Extracted.SIGMA]
    steps
    · sorry
    · exact fun u => True
  · steps
    simp [Skyscraper.square]
    sorry

theorem compress_spec : STHoare lp env ⟦⟧ (compress.fn.body _ h![] |>.body h![l, r])
    fun output => output = Skyscraper.compress l r := by
  sorry

