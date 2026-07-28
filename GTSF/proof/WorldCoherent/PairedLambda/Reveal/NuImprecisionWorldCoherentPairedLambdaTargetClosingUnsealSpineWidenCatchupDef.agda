module
  proof.WorldCoherent.PairedLambda.Reveal.NuImprecisionWorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupDef
  where

-- File Charter:
--   * Defines target-binder closing for the unseal-headed widening family
--     after one source-only dynamic allocation.
--   * Keeps the bare-unseal and strict-tail alternatives inline as the two
--     operations of one genuine semantic family.
--   * Contains no implementation, postulate, constructor view, or permissive
--     option.

import Coercions as C
open import Coercions using (Coercion; ModeEnv; instᵈ; _︔_)
open import Data.List using ([]; _∷_)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_)
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
open import Types using (Ty; TyCtx; TyVar; ★; ＇_; `∀; ⇑ᵗ; wf★)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using (⊑-source-liftνᵢ)
open import proof.NuCore.Relations.NuImprecisionContextExclusivityDef using
  (SourceNameExclusive)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherenceDef using
  (WorldCoherent)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentResultDef using
  (WorldCoherentLeftCatchupIndexedResult)


WorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupᵀ : Set₁
WorldCoherentPairedLambdaTargetClosingUnsealSpineWidenCatchupᵀ =
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
     {ρ : StoreImp Φ Δᴸ Δᴿ}
     {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
     {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
       (suc Δᴸ) (suc Δᴿ)}
     {W W′ : Term} {D C′ : Ty} {α : TyVar}
     {μ : ModeEnv}
     {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
     {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
       ∣ suc Δᴸ ⊢ ＇ α ⊑ C′ ⊣ suc Δᴿ} →
   WorldCoherent ρ →
   SourceNameExclusive Φ →
   StoreWf Δᴸ (leftStoreⁱ ρ) →
   CastMode μ →
   SealModeStore★ (instᵈ μ)
     (leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)) →
   instᵈ μ ∣ suc Δᴸ
     ∣ leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)
     ⊢ C.unseal α (⇑ᵗ (`∀ D))
       ∶ ＇ α ⊑ ⇑ᵗ (`∀ D) →
   LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
   LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
   Value W →
   No• W →
   Value W′ →
   No• W′ →
   ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
     ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
     ⊢ᴺ W ⊑ W′ ⦂ ＇ α ⊑ C′ ∶ r →
   WorldCoherentLeftCatchupIndexedResult
     {N = W ⟨ C.unseal α (⇑ᵗ (`∀ D)) ⟩}
     {V′ = Λ W′}
     {ρ = store-left zero ★ wf★ ∷ ρν}
     (⊑-source-liftνᵢ p))
  ×
  (∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
     {ρ : StoreImp Φ Δᴸ Δᴿ}
     {ρν : StoreImp ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) (suc Δᴸ) Δᴿ}
     {ρ∀ : StoreImp ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
       (suc Δᴸ) (suc Δᴿ)}
     {W W′ : Term} {D X C′ : Ty} {α : TyVar}
     {t : Coercion} {μ : ModeEnv}
     {p : Φ ∣ Δᴸ ⊢ `∀ D ⊑ `∀ C′ ⊣ Δᴿ}
     {r : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
       ∣ suc Δᴸ ⊢ ＇ α ⊑ C′ ⊣ suc Δᴿ} →
   WorldCoherent ρ →
   SourceNameExclusive Φ →
   StoreWf Δᴸ (leftStoreⁱ ρ) →
   CastMode μ →
   SealModeStore★ (instᵈ μ)
     (leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)) →
   instᵈ μ ∣ suc Δᴸ
     ∣ leftStoreⁱ (store-left zero ★ wf★ ∷ ρν)
     ⊢ C.unseal α X ︔ t ∶ ＇ α ⊑ ⇑ᵗ (`∀ D) →
   LiftLeftStoreⁱ ((zero ˣ⊑★) ∷ ⇑ᴸᵢ Φ) ρ ρν →
   LiftStoreⁱ ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ) ρ ρ∀ →
   Value W →
   No• W →
   Value W′ →
   No• W′ →
   ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
     ∣ suc Δᴸ ∣ suc Δᴿ ∣ ρ∀ ∣ []
     ⊢ᴺ W ⊑ W′ ⦂ ＇ α ⊑ C′ ∶ r →
   WorldCoherentLeftCatchupIndexedResult
     {N = W ⟨ C.unseal α X ︔ t ⟩}
     {V′ = Λ W′}
     {ρ = store-left zero ★ wf★ ∷ ρν}
     (⊑-source-liftνᵢ p))
