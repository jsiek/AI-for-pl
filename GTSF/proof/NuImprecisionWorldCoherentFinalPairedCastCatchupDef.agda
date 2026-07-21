module proof.NuImprecisionWorldCoherentFinalPairedCastCatchupDef where

-- File Charter:
--   * Defines exact-world catch-up for a paired cast whose source operand is
--     already a value or blame.
--   * Retains target-cast inertness and all three final-world invariants.
--   * Contains no accumulated-change transport or recursive dispatcher.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using (Coercion; Inert)
open import Data.List using ([])
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  (StoreImp; leftStoreⁱ)
open import NuStore using (StoreWf)
open import NuTerms using
  (No•; Term; Value; blame; _⟨_⟩)
open import QuotientedTermImprecision using
  ( PairedCast
  ; _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  )
open import Types using (Ty; TyCtx)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalPairedCastCatchupᵀ : Set₁
WorldCoherentFinalPairedCastCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {W V′ : Term} {A A′ B B′ : Ty} {c c′ : Coercion}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  ((Value W × No• W) ⊎ (W ≡ blame)) →
  Value V′ →
  No• V′ →
  Inert c′ →
  PairedCast Φ Δᴸ Δᴿ ρ
    c c′ {A} {A′} {B} {B′} p q →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ W ⊑ V′ ⦂ A ⊑ A′ ∶ p →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ c ⟩}
    {V′ = V′ ⟨ c′ ⟩}
    {ρ = ρ} q
