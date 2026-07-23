module
  proof.WorldCoherent.Final.Paired.NuImprecisionWorldCoherentFinalPairedWideningCatchupDef
  where

-- File Charter:
--   * Defines exact-world terminal catch-up for paired widening casts.
--   * Exposes both cast modes and typings for source cancellation and
--     synchronized instantiation allocation.
--   * Contains no paired-conversion or recursive dispatcher dependency.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert; ModeEnv)
open import Data.List using ([])
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import NuTerms using
  (No•; Term; Value; blame; _⟨_⟩)
open import PairedWideningCompatibility using
  (PairedWideningCompatible)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalPairedWideningCatchupᵀ : Set₁
WorldCoherentFinalPairedWideningCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W V′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {μ μ′ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  Value V′ →
  No• V′ →
  Inert c′ →
  CastMode μ →
  SealModeStore★ μ (leftStoreⁱ ρ) →
  μ ∣ Δᴸ ∣ leftStoreⁱ ρ ⊢ c ∶ A ⊑ B →
  CastMode μ′ →
  SealModeStore★ μ′ (rightStoreⁱ ρ) →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ c′ ∶ A′ ⊑ B′ →
  PairedWideningCompatible Φ Δᴸ Δᴿ c c′ B A′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ c ⟩}
    {V′ = V′ ⟨ c′ ⟩}
    {ρ = ρ} q
