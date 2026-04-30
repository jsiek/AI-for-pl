module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

open import Data.Product using (Σ-syntax; _,_)

open import Types
open import UpDown using (Up; Down; Label)
open import Terms using (Term; _up_; _down_; _⦂∀_[_]; blame)
open import ImprecisionIndexed
open import TermImprecisionIndexed
open import ReductionFresh

-- Worker W01 helper slot

-- Worker W02 helper slot

-- Worker W03 helper slot

-- Worker W04 helper slot

-- Worker W05 helper slot

-- Worker W06 helper slot

-- Worker W07 helper slot

-- Worker W08 helper slot

-- Worker W09 helper slot

-- Worker W10 helper slot

-- Worker W11 helper slot

-- Worker W12 helper slot

-- R14: propagate a left-side blame trace through wrappers introduced only on
-- the left of a term-imprecision derivation.
sim-right-w12-up-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {u : Up} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up u) —↠ Σ′ ∣ blame ℓ
sim-right-w12-up-blame-↠ {u = u} {ℓ = ℓ} (M ∎) =
  (blame ℓ up u) —→⟨ id-step blame-up ⟩ blame ℓ ∎
sim-right-w12-up-blame-↠ {u = u} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up u) —→⟨ ξ-up M→M′ ⟩
  sim-right-w12-up-blame-↠ M′↠blame

-- R14.
sim-right-w12-down-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {d : Down} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down d) —↠ Σ′ ∣ blame ℓ
sim-right-w12-down-blame-↠ {d = d} {ℓ = ℓ} (M ∎) =
  (blame ℓ down d) —→⟨ id-step blame-down ⟩ blame ℓ ∎
sim-right-w12-down-blame-↠ {d = d} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down d) —→⟨ ξ-down M→M′ ⟩
  sim-right-w12-down-blame-↠ M′↠blame

-- R14.
sim-right-w12-tyapp-blame-↠ :
  ∀ {Σ Σ′ : Store} {M : Term} {B T : Ty} {ℓ : Label} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w12-tyapp-blame-↠ {B = B} {T = T} {ℓ = ℓ} (M ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
sim-right-w12-tyapp-blame-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w12-tyapp-blame-↠ M′↠blame

-- R14: if the more-imprecise side is already blame, the precise side either is
-- blame or reaches blame after stripping left-only wrappers.
sim-right-w12-right-blame-blames :
  ∀ {E M A B ℓ} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ blame ℓ ⦂ p →
  Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ]
    (TPEnv.store E ∣ M —↠ Σ′ ∣ blame ℓ′)
sim-right-w12-right-blame-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-tyapp-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑upL Φ lenΦ rel hu)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames (⊑upL Φ lenΦ rel hu)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑downL Φ lenΦ rel hd)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-blames (⊑downL Φ lenΦ rel hd)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-down-blame-↠ M↠blame
sim-right-w12-right-blame-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)

-- R14: inversion for a right-side `blame up _` redex.
sim-right-w12-right-blame-up-blames :
  ∀ {E M A B ℓ u′} {p : TPEnv.Ξ E ⊢ A ⊑ᵢ B} →
  E ⊢ M ⊑ ((blame ℓ) up u′) ⦂ p →
  Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ]
    (TPEnv.store E ∣ M —↠ Σ′ ∣ blame ℓ′)
sim-right-w12-right-blame-up-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames
    (⊑⦂∀-ν A B p rel wfA hT inst)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-tyapp-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑up Φ lenΦ rel hu hu′)
    with sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-up-blames (⊑up Φ lenΦ rel hu hu′)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑upL Φ lenΦ rel hu)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames (⊑upL Φ lenΦ rel hu)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-up-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑upR Φ lenΦ rel hu′) =
  sim-right-w12-right-blame-blames rel
sim-right-w12-right-blame-up-blames (⊑downL Φ lenΦ rel hd)
    with sim-right-w12-right-blame-up-blames rel
sim-right-w12-right-blame-up-blames (⊑downL Φ lenΦ rel hd)
  | Σ′ , ℓ′ , M↠blame =
  Σ′ , ℓ′ , sim-right-w12-down-blame-↠ M↠blame
sim-right-w12-right-blame-up-blames (⊑blameR {ℓ = ℓ′} hM) =
  _ , ℓ′ , (blame ℓ′ ∎)
