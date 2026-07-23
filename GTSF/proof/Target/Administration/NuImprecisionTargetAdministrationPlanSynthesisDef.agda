module proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef where

-- File Charter:
--   * Defines direct synthesis of cast-local target administration plans from
--     typed narrowing or widening evidence.
--   * Keeps sparse-store uniqueness premises explicit and changes no QTI
--     constructor while the synthesis route is being tested.
--   * Contains no implementation, simulation result, outcome carrier,
--     postulate, hole, permissive option, or compatibility wrapper.

open import Coercions using (Coercion; ModeEnv)
open import Data.Product using (proj₁)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using (SealModeStore★)
open import Types using (Ty; TyCtx)
open import proof.Target.Administration.NuImprecisionTargetAdministrationPlanDef using
  (TargetAdministrationPlan)


record TargetAdministrationPlanSynthesis : Set₁ where
  field
    targetNarrowingAdministrationPlan :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A B C : Ty} {c : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ C) →
      TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q

    targetWideningAdministrationPlan :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A B C : Ty} {c : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C) →
      TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q

open TargetAdministrationPlanSynthesis public
