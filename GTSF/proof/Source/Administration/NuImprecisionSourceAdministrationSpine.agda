module
  proof.Source.Administration.NuImprecisionSourceAdministrationSpine
  where

-- File Charter:
--   * Defines the typed hereditary spine for private source administration.
--   * Associates each constructor-form administration state with the live
--     term-imprecision derivation that justifies the whole pending source
--     term.
--   * Uses the term relation itself as the typed evidence, avoiding a false
--     ordinary imprecision index between quotient narrowing and widening.
--   * Applies casts from the head outward, matching the list order used by
--     `sourceAdministrationRank`.
--   * Contains no semantic theorem, result carrier, postulate, hole,
--     permissive option, termination bypass, or compatibility shim.

open import Coercions using (Coercion)
open import Data.List using (List; []; _∷_)
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using (StoreImp)
import NuTerms
open import NuTerms using (Term; Value; _•; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty)
import
  proof.Source.Administration.NuImprecisionSourceAdministrationState
  as SourceState
open import
  proof.Source.Administration.NuImprecisionSourceAdministrationState
  using (SourceAdministrationState)


applySourcePendingCasts : Term → List Coercion → Term
applySourcePendingCasts M [] = M
applySourcePendingCasts M (c ∷ cs) =
  applySourcePendingCasts (M ⟨ c ⟩) cs


data SourceAdministrationSpine
    {Φ Δᴸ Δᴿ}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (V′ : Term) :
    ∀ {V A B} →
    Value V →
    SourceAdministrationState →
    Term →
    (p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ) →
    Set₁ where

  source-casts :
    ∀ {V A B cs}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      (vV : Value V) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ applySourcePendingCasts V cs
        ⊑ V′ ⦂ A ⊑ B ∶ p →
    SourceAdministrationSpine ρ V′ vV
      (SourceState.casts cs) (applySourcePendingCasts V cs) p

  source-bullet :
    ∀ {V A B cs}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      (vV : Value V) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ applySourcePendingCasts (V •) cs
        ⊑ V′ ⦂ A ⊑ B ∶ p →
    SourceAdministrationSpine ρ V′ vV
      (SourceState.bullet cs) (applySourcePendingCasts (V •) cs) p

  source-ν :
    ∀ {V X A B c cs}
      {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
      (vV : Value V) →
    Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
      ⊢ᴺ applySourcePendingCasts (NuTerms.ν X V c) cs
        ⊑ V′ ⦂ A ⊑ B ∶ p →
    SourceAdministrationSpine ρ V′ vV
      (SourceState.ν c cs)
      (applySourcePendingCasts (NuTerms.ν X V c) cs) p
