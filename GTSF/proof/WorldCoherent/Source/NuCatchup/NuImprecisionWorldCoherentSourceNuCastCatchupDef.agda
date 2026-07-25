module proof.WorldCoherent.Source.NuCatchup.NuImprecisionWorldCoherentSourceNuCastCatchupDef where

-- File Charter:
--   * Defines coherent catch-up for source-only runtime `ν ★` allocation.
--   * Exposes the exact boundary participating in the source-instantiation
--     mutual proof rather than hiding it in the whole runtime record.
--   * Contains no implementation or permissive proof dependency.

open import Coercions using (Coercion; ModeEnv; instᵈ)
open import CastImprecisionShape using
  (_⊢ᶜ_⦂_; widening)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; NonVar; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_; ν)
open import ImprecisionComposition using
  (ImprecisionShape; _；_≋_; ⌊_⌋)
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; occurs; ★; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentSourceNuCastCatchupᵀ : Set₁
WorldCoherentSourceNuCastCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {N V′ : Term} {B B′ C : Ty} {s : Coercion}
    {s-shape : ImprecisionShape}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {occ : occurs zero C ≡ true}
    {q : ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ B′ ⊣ Δᴿ} →
  {{safe : NonVar C}} →
  StoreImpPrefix ρ₀ ρ⁺ →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    ((zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ (zero , ★) ∷ ⟰ᵗ (leftStoreⁱ ρ₀)
    ⊢ s ∶ C ⊑ ⇑ᵗ B →
  widening ⊢ᶜ s ⦂ s-shape →
  s-shape ； ⌊ p ⌋ ≋ ⌊ q ⌋ →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ₀ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Value V′ →
  No• V′ →
  WorldCoherentLeftCatchupIndexedResult
    {N = N} {V′ = V′} {ρ = ρ⁺} (ν safe occ q) →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν ★ N s} {V′ = V′} {ρ = ρ⁺} p
