module InterpreterAdequacy.proof.TraceMeasure where

-- File Charter:
--   * Provides the list-length inequalities used by the well-founded
--     completeness driver.
--   * Shows that every phase before or after a distinguished reduction step
--     is strictly smaller than the enclosing terminating trace.
--   * Contains no term, interpreter, typing, or reduction reasoning.

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (_<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)

open import NuReduction using (StoreChange)

suffix-length≤ :
  ∀ (prefix suffix : List StoreChange) →
  length suffix ≤ length (prefix ++ suffix)
suffix-length≤ [] suffix = ≤-refl
suffix-length≤ (_ ∷ prefix) suffix =
  ≤-trans (suffix-length≤ prefix suffix)
    (n≤1+n (length (prefix ++ suffix)))

prefix-length≤ :
  ∀ (prefix suffix : List StoreChange) →
  length prefix ≤ length (prefix ++ suffix)
prefix-length≤ [] suffix = z≤n
prefix-length≤ (_ ∷ prefix) suffix =
  s≤s (prefix-length≤ prefix suffix)

middle-length≤ :
  ∀ (prefix middle suffix : List StoreChange) →
  length middle ≤ length (prefix ++ (middle ++ suffix))
middle-length≤ prefix middle suffix =
  ≤-trans (prefix-length≤ middle suffix)
    (suffix-length≤ prefix (middle ++ suffix))

prefix-before-step-shorter :
  ∀ (prefix suffix : List StoreChange) change →
  length prefix < length (prefix ++ (change ∷ suffix))
prefix-before-step-shorter [] suffix change = s≤s z≤n
prefix-before-step-shorter (_ ∷ prefix) suffix change =
  s≤s (prefix-before-step-shorter prefix suffix change)

middle-before-step-shorter :
  ∀ (prefix middle suffix : List StoreChange) change →
  length middle < length (prefix ++ (middle ++ (change ∷ suffix)))
middle-before-step-shorter prefix middle suffix change =
  ≤-trans (prefix-before-step-shorter middle suffix change)
    (suffix-length≤ prefix (middle ++ (change ∷ suffix)))

residual-after-step-shorter :
  ∀ (prefix suffix : List StoreChange) change →
  length suffix < length (prefix ++ (change ∷ suffix))
residual-after-step-shorter [] suffix change = s≤s ≤-refl
residual-after-step-shorter (_ ∷ prefix) suffix change =
  ≤-trans (residual-after-step-shorter prefix suffix change)
    (n≤1+n (length (prefix ++ (change ∷ suffix))))

left-before-right-step-shorter :
  ∀ (left right suffix : List StoreChange) change →
  length left < length (left ++ (right ++ (change ∷ suffix)))
left-before-right-step-shorter [] [] suffix change = s≤s z≤n
left-before-right-step-shorter [] (_ ∷ right) suffix change =
  s≤s z≤n
left-before-right-step-shorter (_ ∷ left) right suffix change =
  s≤s (left-before-right-step-shorter left right suffix change)

residual-after-two-prefixes-shorter :
  ∀ (left right suffix : List StoreChange) change →
  length suffix < length (left ++ (right ++ (change ∷ suffix)))
residual-after-two-prefixes-shorter [] [] suffix change = s≤s ≤-refl
residual-after-two-prefixes-shorter [] (_ ∷ right) suffix change =
  ≤-trans (residual-after-two-prefixes-shorter [] right suffix change)
    (n≤1+n (length (right ++ (change ∷ suffix))))
residual-after-two-prefixes-shorter (_ ∷ left) right suffix change =
  ≤-trans
    (residual-after-two-prefixes-shorter left right suffix change)
    (n≤1+n (length (left ++ (right ++ (change ∷ suffix)))))
