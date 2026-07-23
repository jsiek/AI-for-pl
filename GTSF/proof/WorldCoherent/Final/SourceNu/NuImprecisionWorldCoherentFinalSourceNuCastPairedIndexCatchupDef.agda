module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCastPairedIndexCatchupDef
  where

-- File Charter:
--   * Defines exact-final source-`ν ★` catch-up for the paired inner
--     universal precision index.
--   * Preserves the one-sided allocation boundary without assuming a target
--     allocation or administrative target step.
--   * Contains no implementation, recursive dispatcher, or permissive option.

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  )
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


WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ : Set₁
WorldCoherentFinalSourceNuCastPairedIndexCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {L V′ : Term} {B C C′ : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
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
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ `∀ C′ ∶ ∀ⁱ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν ★ L s} {V′ = V′} {ρ = ρ} p
