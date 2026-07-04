{-# OPTIONS --allow-unsolved-metas #-}

module proof.CatchupSeparated where

-- File Charter:
--   * Separated-store catchup surface for migrating DGG away from the shared
--     `StoreNrw` namespace.
--   * Defines left-side store-change application on `SealCorr`, with projection
--     lemmas showing only the left runtime store changes.
--   * States the left catchup lemma with an unchanged target term.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (zero; suc; z<s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Types
open import Coercions
open import NuTerms
open import NuReduction using
  ( StoreChange
  ; StoreChanges
  ; keep
  ; bind
  ; applyStore
  ; applyStores
  ; applyTyCtx
  ; applyTys
  ; applyTyCtxs
  ; _—↠[_]_
  )
open import StoreCorrespondence
open import TermNarrowingSeparated
open import proof.ReductionProperties using (applyCoercions)

------------------------------------------------------------------------
-- Left-side catchup store changes
------------------------------------------------------------------------

applyLeftChange : StoreChange → SealCorr → SealCorr
applyLeftChange keep ρ = ρ
applyLeftChange (bind A) ρ = left-only zero (⇑ᵗ A) ∷ ⇑ˡᶜorr ρ

applyLeftChanges : StoreChanges → SealCorr → SealCorr
applyLeftChanges [] ρ = ρ
applyLeftChanges (χ ∷ χs) ρ =
  applyLeftChanges χs (applyLeftChange χ ρ)

applyLeftChanges-++ :
  ∀ χs χs′ ρ →
  applyLeftChanges (χs ++ χs′) ρ ≡
    applyLeftChanges χs′ (applyLeftChanges χs ρ)
applyLeftChanges-++ [] χs′ ρ = refl
applyLeftChanges-++ (χ ∷ χs) χs′ ρ =
  applyLeftChanges-++ χs χs′ (applyLeftChange χ ρ)

leftStore-applyLeftChange :
  ∀ χ ρ →
  leftStore (applyLeftChange χ ρ) ≡ applyStore χ (leftStore ρ)
leftStore-applyLeftChange keep ρ = refl
leftStore-applyLeftChange (bind A) ρ =
  cong ((zero , ⇑ᵗ A) ∷_) (leftStore-⇑ˡᶜorr ρ)

rightStore-applyLeftChange :
  ∀ χ ρ →
  rightStore (applyLeftChange χ ρ) ≡ rightStore ρ
rightStore-applyLeftChange keep ρ = refl
rightStore-applyLeftChange (bind A) ρ = rightStore-⇑ˡᶜorr ρ

leftStore-applyLeftChanges :
  ∀ χs ρ →
  leftStore (applyLeftChanges χs ρ) ≡ applyStores χs (leftStore ρ)
leftStore-applyLeftChanges [] ρ = refl
leftStore-applyLeftChanges (χ ∷ χs) ρ =
  trans
    (leftStore-applyLeftChanges χs (applyLeftChange χ ρ))
    (cong (applyStores χs) (leftStore-applyLeftChange χ ρ))

rightStore-applyLeftChanges :
  ∀ χs ρ →
  rightStore (applyLeftChanges χs ρ) ≡ rightStore ρ
rightStore-applyLeftChanges [] ρ = refl
rightStore-applyLeftChanges (χ ∷ χs) ρ =
  trans
    (rightStore-applyLeftChanges χs (applyLeftChange χ ρ))
    (rightStore-applyLeftChange χ ρ)

------------------------------------------------------------------------
-- Right-side target store changes
------------------------------------------------------------------------

applyRightChange : StoreChange → SealCorr → SealCorr
applyRightChange keep ρ = ρ
applyRightChange (bind A) ρ = right-only zero (⇑ᵗ A) ∷ ⇑ʳᶜorr ρ

applyRightChanges : StoreChanges → SealCorr → SealCorr
applyRightChanges [] ρ = ρ
applyRightChanges (χ ∷ χs) ρ =
  applyRightChanges χs (applyRightChange χ ρ)

applyRightChanges-++ :
  ∀ χs χs′ ρ →
  applyRightChanges (χs ++ χs′) ρ ≡
    applyRightChanges χs′ (applyRightChanges χs ρ)
applyRightChanges-++ [] χs′ ρ = refl
applyRightChanges-++ (χ ∷ χs) χs′ ρ =
  applyRightChanges-++ χs χs′ (applyRightChange χ ρ)

leftStore-applyRightChange :
  ∀ χ ρ →
  leftStore (applyRightChange χ ρ) ≡ leftStore ρ
leftStore-applyRightChange keep ρ = refl
leftStore-applyRightChange (bind A) ρ = leftStore-⇑ʳᶜorr ρ

rightStore-applyRightChange :
  ∀ χ ρ →
  rightStore (applyRightChange χ ρ) ≡ applyStore χ (rightStore ρ)
rightStore-applyRightChange keep ρ = refl
rightStore-applyRightChange (bind A) ρ =
  cong ((zero , ⇑ᵗ A) ∷_) (rightStore-⇑ʳᶜorr ρ)

leftStore-applyRightChanges :
  ∀ χs ρ →
  leftStore (applyRightChanges χs ρ) ≡ leftStore ρ
leftStore-applyRightChanges [] ρ = refl
leftStore-applyRightChanges (χ ∷ χs) ρ =
  trans
    (leftStore-applyRightChanges χs (applyRightChange χ ρ))
    (leftStore-applyRightChange χ ρ)

rightStore-applyRightChanges :
  ∀ χs ρ →
  rightStore (applyRightChanges χs ρ) ≡ applyStores χs (rightStore ρ)
rightStore-applyRightChanges [] ρ = refl
rightStore-applyRightChanges (χ ∷ χs) ρ =
  trans
    (rightStore-applyRightChanges χs (applyRightChange χ ρ))
    (cong (applyStores χs) (rightStore-applyRightChange χ ρ))

store-corr-applyLeftKeep :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreCorr (applyTyCtx keep ΔL) ΔR (applyLeftChange keep ρ)
store-corr-applyLeftKeep corr = corr

store-corr-applyLeftBind :
  ∀ {ΔL ΔR ρ A} →
  WfTy (suc ΔL) (⇑ᵗ A) →
  WfTy zero (⇑ᵗ A) →
  StoreCorr ΔL ΔR ρ →
  StoreCorr (applyTyCtx (bind A) ΔL) ΔR (applyLeftChange (bind A) ρ)
store-corr-applyLeftBind hA hA-old corr =
  corr-left z<s hA hA-old
    (λ h → ⊥-elim (leftStore-⇑ˡᶜorr-zero∉ h))
    (corr-⇑ˡᶜorr corr)

store-corr-applyRightKeep :
  ∀ {ΔL ΔR ρ} →
  StoreCorr ΔL ΔR ρ →
  StoreCorr ΔL (applyTyCtx keep ΔR) (applyRightChange keep ρ)
store-corr-applyRightKeep corr = corr

store-corr-applyRightBind :
  ∀ {ΔL ΔR ρ A} →
  WfTy (suc ΔR) (⇑ᵗ A) →
  WfTy zero (⇑ᵗ A) →
  StoreCorr ΔL ΔR ρ →
  StoreCorr ΔL (applyTyCtx (bind A) ΔR) (applyRightChange (bind A) ρ)
store-corr-applyRightBind hA hA-old corr =
  corr-right z<s hA hA-old
    (λ h → ⊥-elim (rightStore-⇑ʳᶜorr-zero∉ h))
    (corr-⇑ʳᶜorr corr)

------------------------------------------------------------------------
-- Separated left catchup
------------------------------------------------------------------------

catchup-lemmaˡ :
  ∀ {ΔL ΔR ρ M V p A B} →
  RuntimeOK M →
  Value V →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ V ∶ p ⦂ A ⊒ B →
  ∃[ χs ] ∃[ W ] ∃[ ΔL′ ]
    Value W ×
    No• W ×
    (M —↠[ χs ] W) ×
    (ΔL′ ≡ applyTyCtxs χs ΔL) ×
    StoreCorr ΔL′ ΔR (applyLeftChanges χs ρ) ×
    (leftStore (applyLeftChanges χs ρ) ≡
      applyStores χs (leftStore ρ)) ×
    (rightStore (applyLeftChanges χs ρ) ≡ rightStore ρ) ×
    (ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ
      ⊢ applyCoercions χs p ∶ᶜ applyTys χs A ⊒ B) ×
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
      ⊢ W ⊒ V ∶ applyCoercions χs p ⦂ applyTys χs A ⊒ B
catchup-lemmaˡ (ok-no noM) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-• vW noW) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-·₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-·₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-ν okL) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-⊕₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-⊕₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaˡ (ok-⟨⟩ okM) vV M⊒V = {! ? !}
