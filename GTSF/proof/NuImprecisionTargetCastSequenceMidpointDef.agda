module proof.NuImprecisionTargetCastSequenceMidpointDef where

-- File Charter:
--   * Defines the local midpoint evidence needed when a target cast reduces
--     by coercion sequencing.
--   * Retains the prescribed sequence midpoint without imposing global
--     right-context compatibility on the imprecision world.
--   * Contains no implementation or target-dispatcher dependency.

open import Agda.Builtin.Equality using (_≡_)
open import Coercions using
  ( Coercion
  ; ModeEnv
  ; _︔_
  ; _∣_∣_⊢_∶_=⇒_
  )
open import ImprecisionWf using (_∣_⊢_⊑_⊣_)
open import NuTermImprecision using
  ( StoreImp
  ; rightStoreⁱ
  )


TargetCastSequenceMidpointᵀ :
  ∀ {Φ Δᴸ Δᴿ A A′ B′} {μ : ModeEnv}
    (ρ : StoreImp Φ Δᴸ Δᴿ)
    (c′ : Coercion)
    (p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ)
    (q : Φ ∣ Δᴸ ⊢ A ⊑ B′ ⊣ Δᴿ) →
  Set
TargetCastSequenceMidpointᵀ
    {Φ = Φ} {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {A = A} {A′ = A′} {B′ = B′} {μ = μ}
    ρ c′ p q =
  ∀ {C′} {s t : Coercion} →
  c′ ≡ s ︔ t →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ s ∶ A′ =⇒ C′ →
  μ ∣ Δᴿ ∣ rightStoreⁱ ρ ⊢ t ∶ C′ =⇒ B′ →
  Φ ∣ Δᴸ ⊢ A ⊑ C′ ⊣ Δᴿ
