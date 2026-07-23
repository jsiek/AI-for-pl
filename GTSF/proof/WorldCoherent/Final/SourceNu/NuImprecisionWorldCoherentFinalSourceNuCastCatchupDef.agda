module proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastCatchupDef where

-- File Charter:
--   * Defines exact-final coherent catch-up for source-only runtime `ν ★`.
--   * Retains the runtime cast and desired outer precision index while the
--     proof classifies the final polymorphic source value and allocates its
--     fresh source seal.
--   * Exposes the allocation-sensitive boundary used by the accumulated-world
--     source-`ν ★` adapter and the source-instantiation mutual proof.
--   * Contains no implementation, recursive dispatcher, or permissive option.

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuStore using (StoreWf)
open import NuTermImprecision using (StoreImp; leftStoreⁱ)
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalSourceNuCastCatchupᵀ : Set₁
WorldCoherentFinalSourceNuCastCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L V′ : Term} {B B′ C : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  Value L →
  No• L →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ q →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν ★ L s} {V′ = V′} {ρ = ρ} p
