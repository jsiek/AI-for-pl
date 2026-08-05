module proof.InterpreterCoercionNarrowingProof where

-- File Charter:
--   * Provides inversion and relational-store-prefix transport for indexed
--     operational coercion evidence.
--   * Exposes the type narrowing carried by ground and tagged boundaries.
--   * Uses no interpreter or reduction semantics.

open import Data.List.Relation.Unary.Any using (there)
open import Data.Nat.Properties using (≤-refl)

open import Coercions using (id-onlyᵈ)
open import Conversion using
  ( weaken-conceal-conversion
  ; weaken-reveal-conversion
  )
open import Narrowing.InterpreterCoercionNarrowing using
  ( CoercionAction
  ; skip-coercion
  ; apply-coercion
  ; OperationalCoercionNarrowing
  ; ComponentCoercionNarrowing
  ; paired-coercion-action
  ; left-narrowing-action
  ; left-widening-action
  ; right-narrowing-action
  ; right-widening-action
  ; right-static-widening-action
  ; left-reveal-action
  ; left-conceal-action
  ; right-reveal-action
  ; right-conceal-action
  ; operational-component
  ; paired-narrowing-component
  ; paired-widening-component
  ; right-static-narrowing-component
  ; OperationalDownCoercionNarrowing
  ; paired-id-down-action
  ; paired-generalized-down-action
  ; OperationalUpCoercionNarrowing
  ; paired-quotient-up-action
  ; InterpreterGroundNarrowing
  ; ground-narrowing
  ; InterpreterTypeNarrowing
  ; LeftTaggedBoundary
  ; RightTaggedBoundary
  )
open import NarrowWiden using (narrow-weaken; widen-weaken)
open import NuTermImprecision using
  ( StoreCorresponds
  ; correspondence-linked
  ; correspondence-stored
  )
open import QuotientedTermImprecision using
  ( PairedCast
  ; QuotientWideningPair
  ; StoreImpPrefix
  ; paired-conceal
  ; paired-conversion
  ; paired-reveal
  ; paired-widening
  ; quotient-cast-widening
  ; quotient-id-widening
  )
open import Types
open import proof.InterpreterTermTypingWeakening using
  (seal-mode-store-weaken)
open import proof.NuImprecisionStorePrefix using
  (leftStoreⁱ-prefix-inclusion; rightStoreⁱ-prefix-inclusion)

store-corresponds-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ α A β B p} →
  (prefix : StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺) →
  StoreCorresponds ρ₀ α A β B p →
  StoreCorresponds ρ⁺ α A β B p
store-corresponds-prefix QuotientedTermImprecision.prefix-reflⁱ
    corresponds =
  corresponds
store-corresponds-prefix
    (QuotientedTermImprecision.prefix-∷ⁱ prefix) corresponds
    with store-corresponds-prefix prefix corresponds
store-corresponds-prefix
    (QuotientedTermImprecision.prefix-∷ⁱ prefix) corresponds
    | correspondence-stored entry∈ =
  correspondence-stored (there entry∈)
store-corresponds-prefix
    (QuotientedTermImprecision.prefix-∷ⁱ prefix) corresponds
    | correspondence-linked entry∈ =
  correspondence-linked (there entry∈)

paired-cast-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ c c′ A A′ B B′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  PairedCast Φ Δᴸ Δᴿ ρ₀
    c c′ {A} {A′} {B} {B′} p q →
  PairedCast Φ Δᴸ Δᴿ ρ⁺
    c c′ {A} {A′} {B} {B′} p q
paired-cast-prefix prefix
    (paired-conversion
      (paired-reveal corresponds source target)) =
  paired-conversion
    (paired-reveal
      (store-corresponds-prefix prefix corresponds)
      (weaken-reveal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (weaken-reveal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target))
paired-cast-prefix prefix
    (paired-conversion
      (paired-conceal corresponds source target)) =
  paired-conversion
    (paired-conceal
      (store-corresponds-prefix prefix corresponds)
      (weaken-conceal-conversion
        (leftStoreⁱ-prefix-inclusion prefix) source)
      (weaken-conceal-conversion
        (rightStoreⁱ-prefix-inclusion prefix) target))
paired-cast-prefix prefix
    (paired-widening
      mode seal source mode′ seal′ target compatible) =
  paired-widening
    mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    mode′
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal′)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
    compatible

quotient-widening-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ u u′ D D′ A A′} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  QuotientWideningPair Δᴸ Δᴿ ρ₀ u u′ D D′ A A′ →
  QuotientWideningPair Δᴸ Δᴿ ρ⁺ u u′ D D′ A A′
quotient-widening-prefix prefix
    (quotient-id-widening source target) =
  quotient-id-widening
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
quotient-widening-prefix prefix
    (quotient-cast-widening
      mode seal source mode′ seal′ target) =
  quotient-cast-widening
    mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    mode′
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal′)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)

paired-coercion-action-static :
  ∀ {Φ Δᴸ Δᴿ ρ c c′ A A′ B B′ p q} →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ
    (apply-coercion c) (apply-coercion c′)
    {A} {A′} {B} {B′} p q →
  PairedCast Φ Δᴸ Δᴿ ρ c c′ p q
paired-coercion-action-static
    (paired-coercion-action cast) =
  cast

operational-coercion-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ left right A A′ B B′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right {A} {A′} {B} {B′} p q →
  OperationalCoercionNarrowing Φ Δᴸ Δᴿ ρ⁺
    left right {A} {A′} {B} {B′} p q
operational-coercion-prefix prefix
    (paired-coercion-action cast) =
  paired-coercion-action (paired-cast-prefix prefix cast)
operational-coercion-prefix prefix
    (left-narrowing-action mode seal cast) =
  left-narrowing-action mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) cast)
operational-coercion-prefix prefix
    (left-widening-action mode seal cast) =
  left-widening-action mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) cast)
operational-coercion-prefix prefix
    (right-narrowing-action mode seal cast) =
  right-narrowing-action mode
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) cast)
operational-coercion-prefix prefix
    (right-widening-action mode seal cast) =
  right-widening-action mode
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) cast)
operational-coercion-prefix prefix
    (right-static-widening-action seal cast) =
  right-static-widening-action
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) cast)
operational-coercion-prefix prefix
    (left-reveal-action conversion) =
  left-reveal-action
    (weaken-reveal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) conversion)
operational-coercion-prefix prefix
    (left-conceal-action conversion) =
  left-conceal-action
    (weaken-conceal-conversion
      (leftStoreⁱ-prefix-inclusion prefix) conversion)
operational-coercion-prefix prefix
    (right-reveal-action conversion) =
  right-reveal-action
    (weaken-reveal-conversion
      (rightStoreⁱ-prefix-inclusion prefix) conversion)
operational-coercion-prefix prefix
    (right-conceal-action conversion) =
  right-conceal-action
    (weaken-conceal-conversion
      (rightStoreⁱ-prefix-inclusion prefix) conversion)

component-coercion-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ left right A A′ B B′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ₀
    left right {A} {A′} {B} {B′} p q →
  ComponentCoercionNarrowing Φ Δᴸ Δᴿ ρ⁺
    left right {A} {A′} {B} {B′} p q
component-coercion-prefix prefix
    (operational-component action) =
  operational-component
    (operational-coercion-prefix prefix action)
component-coercion-prefix prefix
    (paired-narrowing-component
      mode seal source mode′ seal′ target) =
  paired-narrowing-component
    mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    mode′
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal′)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
component-coercion-prefix prefix
    (paired-widening-component
      mode seal source mode′ seal′ target) =
  paired-widening-component
    mode
    (seal-mode-store-weaken
      (leftStoreⁱ-prefix-inclusion prefix) seal)
    (widen-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    mode′
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal′)
    (widen-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
component-coercion-prefix prefix
    (right-static-narrowing-component seal target) =
  right-static-narrowing-component
    (seal-mode-store-weaken
      (rightStoreⁱ-prefix-inclusion prefix) seal)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)

operational-down-coercion-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ d d′ C C′ D D′ p q} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ₀ d d′ {C} {C′} {D} {D′} p q →
  OperationalDownCoercionNarrowing
    Φ Δᴸ Δᴿ ρ⁺ d d′ {C} {C′} {D} {D′} p q
operational-down-coercion-prefix prefix
    (paired-id-down-action source target) =
  paired-id-down-action
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)
operational-down-coercion-prefix prefix
    (paired-generalized-down-action source target) =
  paired-generalized-down-action
    (narrow-weaken ≤-refl
      (leftStoreⁱ-prefix-inclusion prefix) source)
    (narrow-weaken ≤-refl
      (rightStoreⁱ-prefix-inclusion prefix) target)

operational-up-coercion-prefix :
  ∀ {Φ Δᴸ Δᴿ ρ₀ ρ⁺ u u′ D D′ A A′ q p} →
  StoreImpPrefix {Φ} {Δᴸ} {Δᴿ} ρ₀ ρ⁺ →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ₀ u u′ {D} {D′} {A} {A′} q p →
  OperationalUpCoercionNarrowing
    Φ Δᴸ Δᴿ ρ⁺ u u′ {D} {D′} {A} {A′} q p
operational-up-coercion-prefix prefix
    (paired-quotient-up-action widening) =
  paired-quotient-up-action
    (quotient-widening-prefix prefix widening)

ground-narrowing-type :
  ∀ {G H} {gG : Ground G} {gH : Ground H} →
  InterpreterGroundNarrowing gG gH →
  InterpreterTypeNarrowing G H
ground-narrowing-type (ground-narrowing G~H) =
  G~H

left-tagged-boundary-type :
  ∀ {G} {gG : Ground G} →
  LeftTaggedBoundary gG →
  InterpreterTypeNarrowing G ★
left-tagged-boundary-type boundary =
  boundary

right-tagged-boundary-type :
  ∀ {G} {gG : Ground G} →
  RightTaggedBoundary gG →
  InterpreterTypeNarrowing ★ G
right-tagged-boundary-type boundary =
  boundary
