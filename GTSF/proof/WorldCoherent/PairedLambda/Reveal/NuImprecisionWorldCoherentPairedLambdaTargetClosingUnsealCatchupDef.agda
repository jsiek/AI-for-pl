module
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealCatchupDef
  where

-- File Charter:
--   * Defines fused source-unseal cancellation and target-binder closing
--     after one source-only allocation.
--   * Exposes the active reveal and paired variable-body relation without an
--     invalid intermediate relation to the unwrapped target body.
--   * Contains no implementation, postulate, or permissive option.

import Coercions as C
open import Coercions using (ModeEnv)
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
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( LiftLeftStoreⁱ
  ; LiftStoreⁱ
  ; StoreImp
  ; leftStoreⁱ
  ; store-left
  )
open import NuTerms using (No•; Term; Value; Λ_; _⟨_⟩)
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
open import Types using (Ty; TyCtx; WfTy; ＇_; `∀; ⇑ᵗ)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ : Set₁
WorldCoherentPairedLambdaTargetClosingUnsealCatchupᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {A C′ : Ty} {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ ＇ zero ⊑ C′ ⊣ suc Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  WfTy Δᴸ A →
  (h⇑A : WfTy (suc Δᴸ) (⇑ᵗ A)) →
  RevealConversion μ (suc Δᴸ)
    (leftStoreⁱ (store-left zero (⇑ᵗ A) h⇑A ∷ ρν))
    zero (⇑ᵗ A) (C.unseal zero (⇑ᵗ A))
    (＇ zero) (⇑ᵗ A) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ ＇ zero ⊑ C′ ∶ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ C.unseal zero (⇑ᵗ A) ⟩}
    {V′ = Λ W′}
    {ρ = store-left zero (⇑ᵗ A) h⇑A ∷ ρν}
    (⊑-source-liftνᵢ p)
