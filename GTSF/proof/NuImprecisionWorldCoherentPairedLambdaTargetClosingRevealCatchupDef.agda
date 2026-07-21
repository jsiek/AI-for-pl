module
  proof.NuImprecisionWorldCoherentPairedLambdaTargetClosingRevealCatchupDef
  where

-- File Charter:
--   * Defines coherent target-binder closing through a source reveal after a
--     one-sided source allocation.
--   * Covers both inert structural reveals and active unseal cancellation
--     while retaining the target `Λ` value.
--   * Contains no implementation, administrative bullet step, recursive
--     dispatcher, or permissive option.

open import Coercions using (Coercion; ModeEnv)
open import Conversion using (RevealConversion)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑★
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; ⇑ᴸᵢ
  ; _∣_⊢_⊑_⊣_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using (No•; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; WfTy; `∀; ⇑ᵗ)
open import proof.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ : Set₁
WorldCoherentPairedLambdaTargetClosingRevealCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {A B C C′ : Ty} {s : Coercion}
    {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ B ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ C ⊑ C′ ⊣ suc Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
    zero (⇑ᵗ A) s C (⇑ᵗ B) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ C ⊑ C′ ∶ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ s ⟩}
    {V′ = Λ W′}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
    (⊑-source-liftνᵢ p)
