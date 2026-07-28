module proof.Target.Administration.NuImprecisionTargetAdministrationPlanSynthesisDef where

-- File Charter:
--   * Defines direct synthesis of cast-local target administration plans from
--     typed narrowing or widening evidence.
--   * Accepts the exact cast shape and imprecision composition used by QTI,
--     distinguishing ordinary from identity-only widening.
--   * Keeps sparse-store uniqueness premises explicit.
--   * Contains no implementation, simulation result, outcome carrier,
--     postulate, hole, permissive option, or compatibility wrapper.

import CastImprecisionShape as CastShape
open import Coercions using (Coercion; ModeEnv; id-onlyᵈ)
open import Data.Product using (proj₁)
open import ImprecisionComposition using
  (ImprecisionShape; ⌊_⌋; _；_≋_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using
  ( _∣_∣_⊢_∶_⊒_
  ; _∣_∣_⊢_∶_⊑_
  )
open import NuStore using (StoreWf)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  ( StoreImp
  ; rightStoreⁱ
  )
open import QuotientedTermImprecision using (StoreImpPrefix)
open import TermTyping using
  (CastMode; SealModeStore★)
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
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      (c⊒ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊒ C) →
      CastShape.narrowing CastShape.⊢ᶜ c ⦂ s →
      ⌊ q ⌋ ； s ≋ ⌊ p ⌋ →
      TargetAdministrationPlan ρ₀ A (proj₁ c⊒) p q

    targetWideningAdministrationPlan :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A B C : Ty} {c : Coercion} {μ : ModeEnv}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      CastMode μ →
      SealModeStore★ μ (rightStoreⁱ ρ₀) →
      (c⊑ : μ ∣ Δᴿ ∣ rightStoreⁱ ρ₀ ⊢ c ∶ B ⊑ C) →
      CastShape.widening CastShape.⊢ᶜ c ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q

    targetIdWideningAdministrationPlan :
      ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
        {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
        {A B C : Ty} {c : Coercion}
        {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ}
        {q : Φ ∣ Δᴸ ⊢ A ⊑ C ⊣ Δᴿ}
        {s : ImprecisionShape} →
      StoreImpPrefix ρ₀ ρ⁺ →
      StoreWf Δᴿ (rightStoreⁱ ρ⁺) →
      SealModeStore★ id-onlyᵈ (rightStoreⁱ ρ₀) →
      (c⊑ : id-onlyᵈ ∣ Δᴿ ∣ rightStoreⁱ ρ₀
        ⊢ c ∶ B ⊑ C) →
      CastShape.widening CastShape.⊢ᶜ c ⦂ s →
      ⌊ p ⌋ ； s ≋ ⌊ q ⌋ →
      TargetAdministrationPlan ρ₀ A (proj₁ c⊑) p q

open TargetAdministrationPlanSynthesis public
