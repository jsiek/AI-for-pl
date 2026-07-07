{-# OPTIONS --allow-unsolved-metas #-}

module proof.CatchupMediated where

-- File Charter:
--   * The left catchup lemma over the mediated narrowing relation:
--     the source term reduces to a value while the relation is
--     transported across the accumulated left store changes.
--   * Port of `proof.CatchupSeparated.catchup-lemmaˡ` (whose proof
--     skeleton is likewise open).  The decisive difference is in the
--     statement: the returned relation keeps the ORIGINAL coercion
--     index `p` — under the mediated judgment a source store change
--     never rewrites the index raw (`left-changes-transportᵐ`) —
--     where the old statement had to return `applyCoercions χs p`.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)

open import Types
open import Coercions
open import NuTerms
open import NuReduction
open import StoreCorrespondence
open import Mediation
open import MediatedNarrowing
open import proof.CatchupSeparated using
  ( applyLeftChanges
  )
open import proof.MediationProperties using
  ( left-changes-transportᵐ
  ; rightStore-applyLeftChanges
  )

catchup-lemmaᵐ :
  ∀ {ΔL ΔR ρ M V p A B} →
  RuntimeOK M →
  Value V →
  ΔL ∣ ΔR ∣ ρ ∣ [] ⊢ M ⊒ V ∶ p ⦂ A ⊒ᵐ B →
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
      ⊢ p ∶ᶜ applyTys χs A ⊒ᵐ B) ×
    ΔL′ ∣ ΔR ∣ applyLeftChanges χs ρ ∣ []
      ⊢ W ⊒ V ∶ p ⦂ applyTys χs A ⊒ᵐ B
catchup-lemmaᵐ (ok-no noM) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-• vW noW) vV ()
catchup-lemmaᵐ (ok-·₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-·₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-ν okL) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⟨⟩ okM) vV M⊒V = {! ? !}
