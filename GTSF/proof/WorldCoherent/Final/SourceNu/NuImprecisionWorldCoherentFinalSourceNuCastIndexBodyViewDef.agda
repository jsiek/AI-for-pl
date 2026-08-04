module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastIndexBodyViewDef
  where

-- File Charter:
--   * Classifies the body index beneath a source-polymorphic imprecision
--     index used by exact-final source-`ν ★` cast catch-up.
--   * Exposes only the body's imprecision shape while retaining the paired
--     and source-only body derivations in their proper lifted contexts.
--   * Contains no reduction, catch-up implementation, or compatibility
--     equation.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Bool using (true)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋)
open import ImprecisionWf using
  ( ImpCtx
  ; NonVar
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import Types using (Ty; TyCtx; `∀; occurs)


data SourceNuCastIndexBodyView
    {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx} {C : Ty} :
    ∀ {B′ : Ty} →
    (q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ) →
    ImprecisionShape → Set where

  paired-index-body :
    ∀ {C′}
      (r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ) →
    SourceNuCastIndexBodyView (∀ⁱ r) ⌊ r ⌋

  source-only-index-body :
    ∀ {B′} {{safe : NonVar C}} {occ : occurs zero C ≡ true}
      (r : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
        ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ) →
    SourceNuCastIndexBodyView (ν safe occ r) ⌊ r ⌋


source-nu-cast-index-body-view-reindex :
  ∀ {Φ Δᴸ Δᴿ C B′ s}
    {p q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  p ≡ q →
  SourceNuCastIndexBodyView p s →
  SourceNuCastIndexBodyView q s
source-nu-cast-index-body-view-reindex refl view = view
