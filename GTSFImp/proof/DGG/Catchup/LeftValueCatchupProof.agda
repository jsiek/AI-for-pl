module proof.DGG.Catchup.LeftValueCatchupProof where

-- File Charter:
--   * Develops the direct left value catch-up proof by induction on CTI.
--   * Is parameterized by the separately named cast, type-application,
--     conversion, and source-rebase semantic inductions.
--   * Closes every structural CTI case directly and contains no proof holes.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
import CastTerms as CT
open import CastTerms using (Value; _《_》; _↑_; _↓_)
open import Reduction using ([]; ↠-refl)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.Catchup.LeftSourceCastCatchupDef using
  (LeftSourceCastCatchupAt)
open import proof.DGG.Catchup.LeftSourceTypeAppCatchupDef using
  (LeftSourceTypeAppCatchupAt)
open import proof.DGG.Catchup.LeftSourceConversionCatchupDef using
  (LeftSourceRevealCatchupAt; LeftSourceConcealCatchupAt)
open import proof.DGG.Catchup.LeftPairedConversionCatchupDef using
  (LeftPairedRevealCatchupAt; LeftPairedConcealCatchupAt)
open import proof.DGG.Catchup.LeftTargetRevealRebaseCatchupDef using
  (LeftTargetRevealRebaseCatchupAt)
open import proof.DGG.Catchup.LeftValueCatchupDef using
  (LeftValueCatchupAt)
open import proof.DGG.WorldEvolutionSequence using
  ( evolutions-refl
  ; multi-⊑ᵀ
  )


module _
    (source-cast-catchup : ∀ {fuel} → LeftSourceCastCatchupAt fuel)
    (source-type-app-catchup : ∀ {fuel}
      → LeftSourceTypeAppCatchupAt fuel)
    (source-reveal-catchup : ∀ {fuel}
      → LeftSourceRevealCatchupAt fuel)
    (source-conceal-catchup : ∀ {fuel}
      → LeftSourceConcealCatchupAt fuel)
    (paired-reveal-catchup : ∀ {fuel}
      → LeftPairedRevealCatchupAt fuel)
    (paired-conceal-catchup : ∀ {fuel}
      → LeftPairedConcealCatchupAt fuel)
    (target-reveal-rebase-catchup : ∀ {fuel}
      → LeftTargetRevealRebaseCatchupAt fuel)
  where

  left-value-catchup : ∀ {fuel} → LeftValueCatchupAt fuel
  left-value-catchup no-rebase (CTI.x⊑x² _ _) () bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.ƛ⊑ƛ² prem) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.ƛ _ ,
      evolutions-refl , rel)

  left-value-catchup no-rebase (CTI.·⊑·² prem₁ prem₂) () bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.Λ⊑Λ² vV vV′ prem q) target-value bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.Λ vV ,
      evolutions-refl , rel)

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.Λ⊑² Anv zero∈A vV target⊢ prem q) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.Λ vV ,
      evolutions-refl , rel)

  left-value-catchup no-rebase (CTI.•⊑•² p∀ prem q r) () bound

  left-value-catchup no-rebase (CTI.•⊑² p∀ prem q r) vV′ bound =
    source-type-app-catchup no-rebase prem vV′ bound

  left-value-catchup {γ = γ} {M = M} {p = p} no-rebase
      rel@(CTI.κ⊑κ² κ q) vV′ bound =
    inj₁ (_ , _ , [] , M , γ , p , ↠-refl , CT.$ κ ,
      evolutions-refl , rel)

  left-value-catchup no-rebase
      rel@(CTI.cast⊑cast² c c′ prem q) vV′ bound =
    source-cast-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑cast² c′ prem q) (vV′ 《 inert 》) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑cast² c′ V⊑V′ (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑reveal-identity c′⊢ absent prem q) (vV′ ↑ reveal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑reveal-identity c′⊢ absent V⊑V′ (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
      with left-value-catchup no-rebase prem vV′ bound
  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
    | inj₂ blame-result = inj₂ blame-result
  left-value-catchup no-rebase
      (CTI.⊑conceal-identity c′⊢ absent prem q) (vV′ ↓ conceal) bound
    | inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , q′ , M↠V , vV , evol ,
         V⊑V′) =
      inj₁
        (Δᴸ′ , Σᴸ′ , χsᴸ , V , γ′ , multi-⊑ᵀ evol q ,
         M↠V , vV , evol ,
         CTI.⊑conceal-identity c′⊢ absent V⊑V′
           (multi-⊑ᵀ evol q))

  left-value-catchup no-rebase rel@(CTI.cast⊑² c prem q) vV′ bound =
    source-cast-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      rel@(CTI.reveal⊑-identity c⊢ absent prem q) vV′ bound =
    source-reveal-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      rel@(CTI.reveal⊑-only²
        c⊢ present mark free represented prem q) vV′ bound =
    source-reveal-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      rel@(CTI.conceal⊑-identity c⊢ absent prem q) vV′ bound =
    source-conceal-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      rel@(CTI.conceal⊑-only²
        c⊢ present mark free represented prem q) vV′ bound =
    source-conceal-catchup no-rebase rel vV′ bound

  left-value-catchup no-rebase
      rel@(CTI.reveal⊑reveal²
        c⊢ c′⊢ positions aligned represented prem q)
      target-value bound =
    paired-reveal-catchup no-rebase rel target-value bound

  left-value-catchup no-rebase
      rel@(CTI.conceal⊑conceal²
        c⊢ c′⊢ positions aligned represented prem q)
      target-value bound =
    paired-conceal-catchup no-rebase rel target-value bound

  left-value-catchup no-rebase
      rel@(CTI.⊑reveal-rebase² c′⊢ ok represented prem q)
      target-value bound =
    target-reveal-rebase-catchup no-rebase rel target-value bound

  left-value-catchup ()
      (CTI.⊑conceal-rebase² c′⊢ ok represented prem q)
      vV′ bound

  left-value-catchup {γ = γ} {M = M} no-rebase
      (CTI.blame⊑² target⊢ p) vV′ bound =
    inj₂ (_ , _ , [] , γ , ↠-refl , evolutions-refl)

  left-value-catchup no-rebase
      (CTI.⊕⊑⊕² op prem₁ prem₂ r) () bound
