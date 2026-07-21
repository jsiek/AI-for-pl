module proof.NuImprecisionWorldCoherentSourceNuCatchupDef where

-- File Charter:
--   * Defines coherent catch-up for an ordinary source-only `ν` allocation.
--   * Keeps this acyclic handler separate from the mutually recursive
--     `ν ★`/instantiation subsystem.
--   * Contains no implementation or recursive dispatcher dependency.

open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ; ⟰ᵗ)
open import Coercions using (Coercion; ModeEnv)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceNuCatchupᵀ : Set₁
WorldCoherentSourceNuCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {N V′ : Term} {A B B′ C : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  WfTy Δᴸ A →
  WfTy (suc Δᴸ) (⇑ᵗ A) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ₀))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} q →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν A N s} {V′ = V′} {ρ = ρ⁺} p
