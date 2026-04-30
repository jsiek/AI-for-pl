module SimRightLemmas where

-- File Charter:
--   * Local helper lemmas for the right-to-left simulation proof in
--   * `SimRight.agda`.
--   * This module is the shared helper namespace for parallel worker tasks.
--   * Keep helper lemmas grouped by worker slot to minimize merge conflicts.

open import Data.List using ([])
open import Data.Product using (_,_; ∃-syntax)

open import Types
open import ImprecisionIndexed
open import Terms using (Term; blame; _⊕[_]_; _⦂∀_[_]; _up_; _down_)
open import TermImprecisionIndexed
open import ReductionFresh

--------------------------------------------------------------------------------
-- Worker helper slots for `sim-right` parallelization.
--
-- Rule: add new helper lemmas only in your worker slot and use the prefix
-- `sim-right-wXX-...` where XX is your worker id.
--
-- Keep each helper self-contained: statement + implementation + short note
-- naming the `SimRight.agda` hole lines it supports.

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

sim-right-w10-Blames : Store → Term → Set
sim-right-w10-Blames Σ M = ∃[ Σ′ ] ∃[ ℓ ] (Σ ∣ M —↠ Σ′ ∣ blame ℓ)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-up-blames :
  ∀ {Σ M p} →
  sim-right-w10-Blames Σ M →
  sim-right-w10-Blames Σ (M up p)
sim-right-w10-up-blames {p = p} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (up-↠ M↠blame)
    ((blame ℓ up p) —→⟨ id-step blame-up ⟩ blame ℓ ∎)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-down-blames :
  ∀ {Σ M p} →
  sim-right-w10-Blames Σ M →
  sim-right-w10-Blames Σ (M down p)
sim-right-w10-down-blames {p = p} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (down-↠ M↠blame)
    ((blame ℓ down p) —→⟨ id-step blame-down ⟩ blame ℓ ∎)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-tyapp-↠ :
  ∀ {Σ Σ′ M N A T} →
  Σ ∣ M —↠ Σ′ ∣ N →
  Σ ∣ (M ⦂∀ A [ T ]) —↠ Σ′ ∣ (N ⦂∀ A [ T ])
sim-right-w10-tyapp-↠ {A = A} {T = T} (M ∎) =
  (M ⦂∀ A [ T ]) ∎
sim-right-w10-tyapp-↠ {A = A} {T = T} (M —→⟨ M→M₁ ⟩ M₁↠N) =
  (M ⦂∀ A [ T ]) —→⟨ ξ-·α M→M₁ ⟩ sim-right-w10-tyapp-↠ M₁↠N

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-tyapp-blames :
  ∀ {Σ M A T} →
  sim-right-w10-Blames Σ M →
  sim-right-w10-Blames Σ (M ⦂∀ A [ T ])
sim-right-w10-tyapp-blames {A = A} {T = T} (Σ′ , ℓ , M↠blame) =
  Σ′ , ℓ ,
  multi-trans (sim-right-w10-tyapp-↠ M↠blame)
    ((blame ℓ ⦂∀ A [ T ]) —→⟨ id-step blame-·α ⟩ blame ℓ ∎)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-⊕L-↠ :
  ∀ {Σ Σ′ L L′ M op} →
  Σ ∣ L —↠ Σ′ ∣ L′ →
  Σ ∣ (L ⊕[ op ] M) —↠ Σ′ ∣ (L′ ⊕[ op ] M)
sim-right-w10-⊕L-↠ {M = M} {op = op} (L ∎) = (L ⊕[ op ] M) ∎
sim-right-w10-⊕L-↠ {M = M} {op = op} (L —→⟨ L→L₁ ⟩ L₁↠L′) =
  (L ⊕[ op ] M) —→⟨ ξ-⊕₁ L→L₁ ⟩ sim-right-w10-⊕L-↠ L₁↠L′

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-⊕L-blames :
  ∀ {Σ L M op} →
  sim-right-w10-Blames Σ L →
  sim-right-w10-Blames Σ (L ⊕[ op ] M)
sim-right-w10-⊕L-blames {M = M} {op = op} (Σ′ , ℓ , L↠blame) =
  Σ′ , ℓ ,
  multi-trans (sim-right-w10-⊕L-↠ L↠blame)
    ((blame ℓ ⊕[ op ] M) —→⟨ id-step blame-⊕₁ ⟩ blame ℓ ∎)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-right-blame :
  ∀ {Ψ Σ M A B ℓ} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ blame ℓ ⦂ p →
  sim-right-w10-Blames Σ M
sim-right-w10-right-blame (⊑⦂∀-ν A B p rel wfA hT inst) =
  sim-right-w10-tyapp-blames (sim-right-w10-right-blame rel)
sim-right-w10-right-blame (⊑upL Φ lenΦ rel hu) =
  sim-right-w10-up-blames (sim-right-w10-right-blame rel)
sim-right-w10-right-blame (⊑downL Φ lenΦ rel hd) =
  sim-right-w10-down-blames (sim-right-w10-right-blame rel)
sim-right-w10-right-blame (⊑blameR {ℓ = ℓ} hM) =
  _ , ℓ , ((blame ℓ) ∎)

-- Supports R16 (SimRight.agda:75), where the right term takes `blame-⊕₁`.
sim-right-w10-r16-left-blames :
  ∀ {Ψ Σ M R A B ℓ op} {p : [] ⊢ A ⊑ᵢ B} →
  ⟪ 0 , Ψ , Σ , [] , [] ⟫ ⊢ M ⊑ (blame ℓ ⊕[ op ] R) ⦂ p →
  sim-right-w10-Blames Σ M
sim-right-w10-r16-left-blames (⊑⦂∀-ν A B p rel wfA hT inst) =
  sim-right-w10-tyapp-blames (sim-right-w10-r16-left-blames rel)
sim-right-w10-r16-left-blames (⊑⊕ relL relM) =
  sim-right-w10-⊕L-blames (sim-right-w10-right-blame relL)
sim-right-w10-r16-left-blames (⊑upL Φ lenΦ rel hu) =
  sim-right-w10-up-blames (sim-right-w10-r16-left-blames rel)
sim-right-w10-r16-left-blames (⊑downL Φ lenΦ rel hd) =
  sim-right-w10-down-blames (sim-right-w10-r16-left-blames rel)
sim-right-w10-r16-left-blames (⊑blameR {ℓ = ℓ} hM) =
  _ , ℓ , ((blame ℓ) ∎)

-- Worker W11 helper slot

-- Worker W12 helper slot
