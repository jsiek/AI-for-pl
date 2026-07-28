module
  proof.WorldCoherent.PairedLambda.AllWiden.NuImprecisionWorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewDef
  where

-- File Charter:
--   * Defines structural universal-widening target closing after the source
--     polymorphic value has been classified by canonical forms.
--   * Retains the complete fused telescope and leaves the target body
--     unclassified because its type need not be universal.
--   * Contains no implementation, intermediate index, postulate, or
--     permissive option.

import Coercions as C
open import Coercions using (Coercion; ModeEnv; instᵈ)
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
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
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
open import TermTyping using (CastMode; SealModeStore★)
open import Types using (Ty; TyCtx; ★; `∀; ⇑ᵗ; wf★)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)
open import proof.DGG.Core.NuProgress using (AllView)


WorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewᵀ : Set₁
WorldCoherentPairedLambdaTargetClosingAllWidenCatchupSourceViewᵀ =
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
    {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      (suc Δᴸ) (suc Δᴿ)}
    {W W′ : Term} {D E C′ : Ty} {c : Coercion}
    {μ : ModeEnv}
    {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
    {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ `∀ E ⊑ C′ ⊣ suc Δᴿ} →
  WorldCoherent ρ →
  SourceNameExclusive Φ →
  StoreWf Δᴸ (leftStoreⁱ ρ) →
  CastMode μ →
  SealModeStore★ (instᵈ μ)
    (leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)) →
  instᵈ μ ∣ suc Δᴸ
    ∣ leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)
    ⊢ C.`∀ c ∶ `∀ E ⊑ ⇑ᵗ (`∀ D) →
  LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
  LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
  Value W →
  No• W →
  Value W′ →
  No• W′ →
  AllView W →
  ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
    ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
    ⊢ᴺ W ⊑ W′ ⦂ `∀ E ⊑ C′ ∶ r →
  WorldCoherentLeftCatchupIndexedResult
    {N = W ⟨ C.`∀ c ⟩}
    {V′ = Λ W′}
    {ρ = store-left zero ★ wf★ ∷ ρν}
    (⊑-source-liftνᵢ p)
