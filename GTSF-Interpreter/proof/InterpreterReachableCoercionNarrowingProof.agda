module proof.InterpreterReachableCoercionNarrowingProof where

-- File Charter:
--   * Proves relational-store-prefix transport for reachable coercion plans.
--   * Rebuilds paired conversions directly, preserving their constructor.
--   * Uses only static weakening and contains no interpreter semantics.

open import Data.Nat.Properties using (≤-refl)

open import Conversion using
  (weaken-conceal-conversion; weaken-reveal-conversion)
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterOperationalCoercionNarrowing using
  (operational-coercion-prefix)
open import Narrowing.InterpreterReachableCoercionNarrowing
open import NarrowWiden using (narrow-weaken)
open import NuTermImprecision using (StoreCorresponds)
open import QuotientedTermImprecision using
  ( PairedConversion
  ; StoreImpPrefix
  ; paired-conceal
  ; paired-reveal
  )
open import proof.InterpreterCoercionNarrowingProof using
  (store-corresponds-prefix)
open import proof.InterpreterTermTypingWeakening using
  (seal-mode-store-weaken)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)


paired-conversion-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ c c′ A A′ B B′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  PairedConversion Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  PairedConversion Φ Δᴸ Δᴿ ρ⁺
    c c′ {A} {A′} {B} {B′} p q
paired-conversion-prefix prefix
    (paired-reveal corresponds source target) =
  paired-reveal
    (store-corresponds-prefix prefix corresponds)
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) source)
    (weaken-reveal-conversion
      (rightStoreⁱ-prefix-inclusion prefix) target)
paired-conversion-prefix prefix
    (paired-conceal corresponds source target) =
  paired-conceal
    (store-corresponds-prefix prefix corresponds)
    (weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) source)
    (weaken-conceal-conversion
      (rightStoreⁱ-prefix-inclusion prefix) target)


reachable-component-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ left right A A′ B B′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right {A} {A′} {B} {B′} p q →
  ReachableComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ⁺
    left right {A} {A′} {B} {B′} p q
reachable-component-prefix prefix
    (reachable-paired-conversion conversion) =
  reachable-paired-conversion
    (paired-conversion-prefix prefix conversion)
reachable-component-prefix prefix
    (reachable-left-operational action) =
  reachable-left-operational
    (operational-coercion-prefix prefix action)
reachable-component-prefix prefix
    (reachable-right-operational action) =
  reachable-right-operational
    (operational-coercion-prefix prefix action)
reachable-component-prefix prefix
    (reachable-right-static-narrowing seal target) =
  reachable-right-static-narrowing
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
