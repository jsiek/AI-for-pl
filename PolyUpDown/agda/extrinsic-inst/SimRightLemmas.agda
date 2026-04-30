module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Product using (_,_; Σ-syntax)

open import Types
open import UpDown using (Down; Label)
open import Terms using (Term; blame; _up_; _down_; _⦂∀_[_])
open import ImprecisionIndexed
open import TermImprecisionIndexed
open import ReductionFresh
  using
    ( _∣_—↠_∣_
    ; _∎
    ; _—→⟨_⟩_
    ; id-step
    ; blame-up
    ; blame-down
    ; blame-·α
    ; ξ-up
    ; ξ-down
    ; ξ-·α
    )

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

-- Worker W01 helper slot

sim-right-w01-up-blame-↠ :
  ∀ {Σ Σ′ M ℓ p} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M up p) —↠ Σ′ ∣ blame ℓ
sim-right-w01-up-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎
sim-right-w01-up-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M up p) —→⟨ ξ-up M→M′ ⟩ sim-right-w01-up-blame-↠ M′↠blame

sim-right-w01-down-blame-↠ :
  ∀ {Σ Σ′ M ℓ p} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M down p) —↠ Σ′ ∣ blame ℓ
sim-right-w01-down-blame-↠ {ℓ = ℓ} {p = p} (_ ∎) =
  (blame ℓ down p) —→⟨ id-step blame-down ⟩ blame ℓ ∎
sim-right-w01-down-blame-↠ {p = p} (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M down p) —→⟨ ξ-down M→M′ ⟩
  sim-right-w01-down-blame-↠ M′↠blame

sim-right-w01-tyapp-blame-↠ :
  ∀ {Σ Σ′ M ℓ B T} →
  Σ ∣ M —↠ Σ′ ∣ blame ℓ →
  Σ ∣ (M ⦂∀ B [ T ]) —↠ Σ′ ∣ blame ℓ
sim-right-w01-tyapp-blame-↠ {ℓ = ℓ} {B = B} {T = T} (_ ∎) =
  (blame ℓ ⦂∀ B [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎
sim-right-w01-tyapp-blame-↠ {B = B} {T = T}
    (M —→⟨ M→M′ ⟩ M′↠blame) =
  (M ⦂∀ B [ T ]) —→⟨ ξ-·α M→M′ ⟩
  sim-right-w01-tyapp-blame-↠ M′↠blame

mutual
  -- Supports SimRight.agda R15: a right-side blame forces the left term to
  -- reach blame through any left-only wrappers.
  sim-right-w01-right-blame :
    ∀ {Ψ Σ M A B ℓ} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
    Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ′)
  sim-right-w01-right-blame (⊑⦂∀-ν A B pν rel wfA hT closed) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-tyapp-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑upL Φ lenΦ rel hu) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-up-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑downL Φ lenΦ rel hd) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-blame (⊑blameR hM) = _ , _ , (blame _ ∎)

  -- Supports SimRight.agda R15: a right `blame down p` step is simulated by
  -- showing that the left term already reaches blame.
  sim-right-w01-right-down-blame :
    ∀ {Ψ Σ M A B ℓ d} {p : [] ⊢ A ⊑ᵢ B} →
    ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ (blame ℓ down d) ⦂ p →
    Σ[ Σ′ ∈ Store ] Σ[ ℓ′ ∈ Label ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ′)
  sim-right-w01-right-down-blame (⊑⦂∀-ν A B pν rel wfA hT closed) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-tyapp-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑upL Φ lenΦ rel hu) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-up-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑down Φ lenΦ rel hd hd′) with
      sim-right-w01-right-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑downL Φ lenΦ rel hd) with
      sim-right-w01-right-down-blame rel
  ... | Σ′ , ℓ′ , M↠blame =
    Σ′ , ℓ′ , sim-right-w01-down-blame-↠ M↠blame
  sim-right-w01-right-down-blame (⊑downR Φ lenΦ rel hd′) =
    sim-right-w01-right-blame rel
  sim-right-w01-right-down-blame (⊑blameR hM) = _ , _ , (blame _ ∎)

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
