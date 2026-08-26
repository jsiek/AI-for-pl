module proof.DGG.OneStep where

-- File Charter:
--   * Provides small checked wrappers around Eval's executable one-step and
--     value classifiers.
--   * Records the successor type context, store change, next term, and
--     reduction witness for a computed step.
--   * Used by DGG examples and probes that replay executable reduction traces.

open import Data.Bool using (Bool; false; true)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (TyStore)
open import CastTerms using (Term; Value)
open import Reduction
open import Eval using (Step; step-result)

record OneStep {Δ : TyCtx} (Σ : TyStore Δ) (M : Term Δ) : Set where
  constructor one-step
  field
    Δ′ : TyCtx
    change : StoreChange Δ Δ′
    next : Term Δ′
    reduction : M —→[ change ] next

open OneStep public

hasStep? : ∀ {Δ} {M : Term Δ} → Maybe (Step M) → Bool
hasStep? (just _) = true
hasStep? nothing = false

from-just-step : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → (s : Maybe (Step M))
  → hasStep? s ≡ true
  → OneStep Σ M
from-just-step (just (step-result χ N M→N)) refl =
  one-step _ χ N M→N
from-just-step nothing ()

store-after : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → (s : OneStep Σ M)
  → TyStore (Δ′ s)
store-after {Σ = Σ} s = change s ▷ˢ Σ

hasValue? : ∀ {Δ} {M : Term Δ} → Maybe (Value M) → Bool
hasValue? (just _) = true
hasValue? nothing = false

from-just-value : ∀ {Δ} {M : Term Δ}
  → (v : Maybe (Value M))
  → hasValue? v ≡ true
  → Value M
from-just-value (just v) refl = v
from-just-value nothing ()
