module
  proof.WorldCoherent.Final.SourceNu.NuImprecisionWorldCoherentFinalSourceNuCatchupDef
  where

-- File Charter:
--   * Defines exact-world terminal catch-up for ordinary source-only `ν`.
--   * Keeps both possible inner universal indices visible through a generic
--     type-imprecision proof.
--   * Exposes allocation, reveal, terminal-value, and world invariants without
--     importing a recursive dispatcher or proof implementation.

open import Coercions using (Coercion; ModeEnv)
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (zero; suc)
open import Data.Product using (_,_)
open import ImprecisionWf using
  (ImpCtx; _ˣ⊑★; ⇑ᴸᵢ; _∣_⊢_⊑_⊣_)
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( CtxImpEntry
  ; LiftLeftCtxⁱ
  ; LiftLeftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  )
open import NuTerms using (No•; Term; Value; ν)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ; ⟰ᵗ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentFinalSourceNuCatchupᵀ : Set₁
WorldCoherentFinalSourceNuCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρ′ : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {L V′ : Term} {A B B′ C : Ty} {s : Coercion}
    {μ : ModeEnv} {p : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ C ⊑ B′ ⊣ Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  WfTy (suc Δᴸ) (⇑ᵗ A) →
  RevealConversion μ (suc Δᴸ)
    ((zero , ⇑ᵗ A) ∷ ⟰ᵗ (leftStoreⁱ ρ))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρ′ →
  LiftLeftCtxⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ)
    ([] {A = CtxImpEntry Φ Δᴸ Δᴿ})
    ([] {A = CtxImpEntry
      ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}) →
  Value L →
  No• L →
  Value V′ →
  No• V′ →
  Φ ∣ Δᴸ ∣ Δᴿ ∣ ρ ∣ []
    ⊢ᴺ L ⊑ V′ ⦂ `∀ C ⊑ B′ ∶ q →
  WorldCoherentLeftCatchupIndexedResult
    {N = ν A L s} {V′ = V′} {ρ = ρ} p
