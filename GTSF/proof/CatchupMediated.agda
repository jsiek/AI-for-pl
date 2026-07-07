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

catchup-zeroᵐ :
  ∀ {ΔL ΔR ρ M V p A B} →
  Value M →
  No• M →
  ΔL ∣ ΔR ∣ ρ ⊢ p ∶ᶜ A ⊒ᵐ B →
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
catchup-zeroᵐ {ΔL = ΔL} vM noM pᶜ M⊒V =
  [] , _ , ΔL , vM , noM , ↠-refl , refl ,
  narrowing-store-corrᵐᶜ pᶜ , refl , refl , pᶜ , M⊒V

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
catchup-lemmaᵐ (ok-no noM) () (⊒blameᵗ M⊢ q⊒)
catchup-lemmaᵐ (ok-no noM) () (x⊒xᵗ qᶜ x∋q)
catchup-lemmaᵐ (ok-no noM) (ƛ N′) rel@(ƛ⊒ƛᵗ p↦qᶜ N⊒N′) =
  catchup-zeroᵐ (ƛ _) noM p↦qᶜ rel
catchup-lemmaᵐ (ok-no noM) () (·⊒·ᵗ p↦qᶜ L⊒L′ M⊒M′)
catchup-lemmaᵐ (ok-no noM) (Λ vV′) rel@(Λ⊒Λᵗ allᶜ vV vV′₁ V⊒V′) =
  catchup-zeroᵐ (Λ vV) noM allᶜ rel
catchup-lemmaᵐ (ok-no noM) vV (⊒Λᵗ N⊢ genᶜ vV′ N⊒V′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV
    (⊒⟨ν⟩ᵗ N⊢ genS⊢ V′⊢ genᶜ i N⊒V′s) = {! ? !}
catchup-lemmaᵐ (ok-no noM) () (α⊒αᵗ vL noL vL′ noL′ qᶜ pᶜ L⊒L′)
catchup-lemmaᵐ (ok-no noM) () (⊒αᵗ vL′ noL′ pᶜ L⊒L′)
catchup-lemmaᵐ (ok-no noM) () (ν⊒νᵗ hA hA′ N⊢ N′⊢ sₗ⊢ sᵣ⊢ pᶜ qᶜ N⊒N′)
catchup-lemmaᵐ (ok-no noM) () (⊒νᵗ N⊢ hA N′⊢ s⊢ pᶜ N⊒N′)
catchup-lemmaᵐ (ok-no noM) ($ κ) rel@(κ⊒κᵗ κ qᶜ) =
  catchup-zeroᵐ ($ κ) noM qᶜ rel
catchup-lemmaᵐ (ok-no noM) () (⊕⊒⊕ᵗ pᶜ M⊒M′ N⊒N′)
catchup-lemmaᵐ (ok-no noM) vV (⊒cast+ᵗ pᶜ rᶜ t⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV (⊒cast-ᵗ pᶜ rᶜ t⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV (cast+⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-no noM) vV (cast-⊒ᵗ qᶜ rᶜ s⊒ M⊒M′) = {! ? !}
catchup-lemmaᵐ (ok-• vW noW) vV ()
catchup-lemmaᵐ (ok-·₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-·₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-ν okL) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₁ okL noR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⊕₂ vL noL okR) vV M⊒V = {! ? !}
catchup-lemmaᵐ (ok-⟨⟩ okM) vV M⊒V = {! ? !}
