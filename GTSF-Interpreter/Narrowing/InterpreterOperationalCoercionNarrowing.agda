module Narrowing.InterpreterOperationalCoercionNarrowing where

-- File Charter:
--   * Public metatheory for indexed operational coercion narrowing.
--   * Exposes exact paired-cast recovery and relational-store-prefix
--     transport for ordinary, quotient-down, and quotient-up evidence.
--   * Delegates all reduction-free proofs to its private proof module.

open import Coercions using (Coercion)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionWf using (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterCoercionNarrowing using
  ( CoercionAction
  ; apply-coercion
  ; OperationalCoercionNarrowing
  ; ComponentCoercionNarrowing
  ; OperationalDownCoercionNarrowing
  ; OperationalUpCoercionNarrowing
  )
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using
  (PairedCast; StoreImpPrefix)
open import Types using (Ty; TyCtx)
import proof.InterpreterCoercionNarrowingProof as Proof

paired-coercion-action-static :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ}
    {c c′ : Coercion} {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) (apply-coercion c′) p q →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q
paired-coercion-action-static =
  Proof.paired-coercion-action-static

operational-coercion-prefix :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {left right : CoercionAction}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right p q →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ⁺
    left right p q
operational-coercion-prefix =
  Proof.operational-coercion-prefix

component-coercion-prefix :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ₀ ρ⁺ : StoreImp Φ Δᴸ Δᴿ}
    {left right : CoercionAction}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ B ⊑ B′ ⊣ Δᴿ} →
  StoreImpPrefix ρ₀ ρ⁺ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right p q →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ⁺
    left right p q
component-coercion-prefix =
  Proof.component-coercion-prefix

operational-down-coercion-prefix :
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
operational-down-coercion-prefix =
  Proof.operational-down-coercion-prefix

operational-up-coercion-prefix :
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
operational-up-coercion-prefix =
  Proof.operational-up-coercion-prefix
