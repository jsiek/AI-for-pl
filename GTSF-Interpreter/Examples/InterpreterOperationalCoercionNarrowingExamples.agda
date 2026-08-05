module Examples.InterpreterOperationalCoercionNarrowingExamples where

-- File Charter:
--   * Regression-checks exact static-evidence recovery from paired actions.
--   * Checks ordinary and quotient operational evidence through nested
--     relational-store prefixes.
--   * Uses only symbolic static witnesses and no interpreter execution.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Coercions using (Coercion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing using
  ( CoercionAction
  ; OperationalCoercionNarrowing
  ; paired-coercion-action
  ; OperationalDownCoercionNarrowing
  ; OperationalUpCoercionNarrowing
  )
open import Narrowing.InterpreterOperationalCoercionNarrowing using
  ( paired-coercion-action-static
  ; operational-coercion-prefix
  ; operational-down-coercion-prefix
  ; operational-up-coercion-prefix
  )
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)

paired-action-retains-static-evidence :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ}
    (cast : PairedCast Φ Δᴸ Δᴿ ρ c c′ p q) →
  paired-coercion-action-static
    (paired-coercion-action cast) ≡ cast
paired-action-retains-static-evidence cast =
  refl

two-prefixes-retain-operational-indices :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ₁ ρ₂ : StoreImp Φ Δᴸ Δᴿ}
    {left right : CoercionAction}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ₁ →
  StoreImpPrefix ρ₁ ρ₂ →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right p q →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ₂
    left right p q
two-prefixes-retain-operational-indices prefix₀₁ prefix₁₂ action =
  operational-coercion-prefix prefix₁₂
    (operational-coercion-prefix prefix₀₁ action)

prefix-retains-down-indices :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {d d′ : Coercion} {C C′ D D′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ₀ d d′ p q →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ⁺ d d′ p q
prefix-retains-down-indices =
  operational-down-coercion-prefix

prefix-retains-up-indices :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {u u′ : Coercion} {D D′ A A′ : Ty}
    {q : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ₀ u u′ q p →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ⁺ u u′ q p
prefix-retains-up-indices =
  operational-up-coercion-prefix
