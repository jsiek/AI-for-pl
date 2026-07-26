module
  proof.Quotient.NuImprecisionReductionClosedQuotientDef
  where

-- File Charter:
--   * Defines the smaller quotient-imprecision prototype used to test
--     simulation up to reduction.
--   * Keeps quotient indices only across one paired narrowing cast and closes
--     them with compatible paired widenings.
--   * Retains ordinary application only after both premises have returned to
--     an ordinary imprecision index.
--   * Defines pure-reduction closure for focused function-beta experiments.
--   * Does not change or re-export the live term-imprecision relation.

open import Data.List using ([]; _∷_)

open import CastImprecisionShape using
  (narrowing; widening; _⊢ᶜ_⦂_)
open import Coercions using (ModeEnv)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import Imprecision using (ImpCtx)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuReduction using
  (StoreChanges; keep; _—↠[_]_)
open import NuTermImprecision using
  (CtxImp; StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using (Term; _·_; _⟨_⟩)
open import QuotientedTermImprecision using
  (PairedCast; QuotientWideningPair;
   _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; _⇒_)
open import
  proof.Quotient.NuImprecisionCompositionalQuotientDef
  using
  ( SpineCastMode
  ; QuotientWideningCompatible
  )

------------------------------------------------------------------------
-- Store-neutral reduction sequences
------------------------------------------------------------------------

data AllKeep : StoreChanges → Set where
  []ᵏ : AllKeep []
  keep∷ᵏ_ : ∀ {χs} → AllKeep χs → AllKeep (keep ∷ χs)

------------------------------------------------------------------------
-- Smaller ordinary and quotient relations
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
infix 4 _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_

mutual
  data _∣_∣_∣_∣_⊢ᴿ_⊑_⦂_⊑_∶_
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
      (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ) :
      Term → Term → (A B : Ty) →
      Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ → Set₁ where

    ordinaryᴿ :
      ∀ {M M′ A A′ p} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴺ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p

    _·ᴿ_ :
      ∀ {L L′ M M′ A A′ B B′ pA pB} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L ⊑ L′
        ⦂ A ⇒ B ⊑ A′ ⇒ B′ ∶ pA ImprecisionWf.↦ pB →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ pA →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ L · M ⊑ L′ · M′ ⦂ B ⊑ B′ ∶ pB

    closeᴿ :
      ∀ {N N′ D D′ A A′ q p u u′ s s′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ N ⊑ N′ ⦂ D ⊑ᵖ D′ ∶ q →
      QuotientWideningPair Δᴸ Δᴿ ρ u u′ D D′ A A′ →
      widening ⊢ᶜ u ⦂ s →
      widening ⊢ᶜ u′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      QuotientWideningCompatible Φ Δᴸ Δᴿ u u′ q p s s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ N ⟨ u ⟩ ⊑ N′ ⟨ u′ ⟩ ⦂ A ⊑ A′ ∶ p

    paired-castᴿ :
      ∀ {M M′ A A′ B B′ p q c c′} →
      PairedCast Φ Δᴸ Δᴿ ρ c c′ p q →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⟨ c ⟩ ⊑ M′ ⟨ c′ ⟩ ⦂ B ⊑ B′ ∶ q

  data _∣_∣_∣_∣_⊢ᴿᵖ_⊑_⦂_⊑ᵖ_∶_
      (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
      (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ) :
      Term → Term → (D D′ : Ty) →
      Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ → Set₁ where

    paired-downᴿ :
      ∀ {M M′ A A′ D D′ p d d′ s s′ q μ μ′} →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ M ⊑ M′ ⦂ A ⊑ A′ ∶ p →
      SpineCastMode (leftStoreⁱ ρ) μ →
      μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ d ∶ A ⊒ D →
      narrowing ⊢ᶜ d ⦂ s →
      SpineCastMode (rightStoreⁱ ρ) μ′ →
      μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ d′ ∶ A′ ⊒ D′ →
      narrowing ⊢ᶜ d′ ⦂ s′ →
      s ；⌊ p ⌋≋ᵖ q ； s′ →
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿᵖ M ⟨ d ⟩ ⊑ M′ ⟨ d′ ⟩
        ⦂ D ⊑ᵖ D′ ∶ q

------------------------------------------------------------------------
-- Reduction-saturated use of the smaller ordinary relation
------------------------------------------------------------------------

infix 4 _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_

record _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : StoreImp Φ Δᴸ Δᴿ) (γ : CtxImp Φ Δᴸ Δᴿ)
    (M M′ : Term) (A A′ : Ty)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ) : Set₁ where
  constructor related-after-pure-reduction
  field
    sourceChanges : StoreChanges
    targetChanges : StoreChanges
    sourceChangesKeep : AllKeep sourceChanges
    targetChangesKeep : AllKeep targetChanges
    sourceResult : Term
    targetResult : Term
    sourceReduction : M —↠[ sourceChanges ] sourceResult
    targetReduction : M′ —↠[ targetChanges ] targetResult
    resultImprecision :
      Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ γ
        ⊢ᴿ sourceResult ⊑ targetResult ⦂ A ⊑ A′ ∶ p

open _∣_∣_∣_∣_⊢ᴿ↠_⊑_⦂_⊑_∶_ public
