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
--
-- lemma STHoare.pure_left_of_imp (h : P → STHoare lp Γ ⟦P⟧ E Q): STHoare lp Γ ⟦P⟧ E Q := by
--   simp_all [STHoare, THoare, SLP.pure_star_iff_and]

theorem rl_spec : STHoare lp env ⟦⟧ (rl.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.rl input := by
  simp only [rl, Skyscraper.rl]
  steps
  simp_all
  apply STHoare.consequence_frame_left STHoare.uOr_intro
  · sl
  · steps
    intro h
    simp_all
    rfl

theorem rotateLeft_spec : STHoare lp env ⟦⟧ (rotate_left.fn.body _ h![] |>.body h![input, N])
    fun output => output = Skyscraper.rotateLeft input N := by
  simp only [Extracted.rotate_left]
  steps
  sorry

theorem sbox_spec : STHoare lp env ⟦⟧ (sbox.fn.body _ h![] |>.body h![input])
    fun output => output = Skyscraper.sbox output := by
  sorry

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

