module LR-narrow.Computation where

-- File Charter:
--   * Defines bounded observations of evaluations in distinct LR endpoints.
--   * Permits the precise computation to blame after an imprecise return.
--   * Joins successful endpoint returns in one three-context future world.
--   * Packages target-only store changes and completed target phases.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _∸_; _≤_; _<_)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import CastTerms using (Term; Value; blame)
open import Reduction using
  (StoreChanges; _—↠[_]_; applyStores; applyTerms)
import Eval as E
open import Interpreter
open import LR-narrow.World

IndexedValueRelation : ∀ {Δᴾ Δᴵ Δᶜ}
  → World Δᴾ Δᴵ Δᶜ
  → Set₂
IndexedValueRelation W = ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
  → (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
  → Future W W′
  → ℕ
  → Term Δᴵ′
  → Term Δᴾ′
  → Set₁

data PairedReturns {Δᴾ Δᴵ Δᶜ}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    (W : World Δᴾ Δᴵ Δᶜ) (R : IndexedValueRelation W) (k : ℕ) :
    E.EvalResult Mᴵ → E.EvalResult Mᴾ → Set₁ where
  paired-returns : ∀ {resultᴵ : E.EvalResult Mᴵ}
      {resultᴾ : E.EvalResult Mᴾ} {Δᶜ′}
    → (W′ : World (E.Δ′ resultᴾ) (E.Δ′ resultᴵ) Δᶜ′)
    → (W≼W′ : Future W W′)
    → impreciseStore (core W′) ≡
        E.changes resultᴵ ▶ˢ impreciseStore (core W)
    → preciseStore (core W′) ≡
        E.changes resultᴾ ▶ˢ preciseStore (core W)
    → (∀ M → E.changes resultᴵ ▶ᵀ M ≡
        liftImpreciseTerm W≼W′ M)
    → (∀ M → E.changes resultᴾ ▶ᵀ M ≡
        liftPreciseTerm W≼W′ M)
    → R W′ W≼W′ k (E.term resultᴵ) (E.term resultᴾ)
    → PairedReturns W R k resultᴵ resultᴾ

BlamesFrom : ∀ {Δ}
  → TyStore Δ
  → ℕ
  → (M : Term Δ)
  → Set
BlamesFrom {Δ} Σ gas M =
  Σ[ Δ′ ∈ TyCtx ]
  Σ[ changes ∈ StoreChanges Δ Δ′ ]
  Σ[ trace ∈ M —↠[ changes ] blame ]
    interpretFrom Σ gas M ≡ blamed changes trace

record ComputationsRelated {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (R : IndexedValueRelation W) (k : ℕ)
    (Mᴵ : Term Δᴵ) (Mᴾ : Term Δᴾ) : Set₁ where
  field
    forward-return : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
      → n < k
      → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
      →
        (Σ[ m ∈ ℕ ]
         Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
           (interpretFrom (preciseStore (core W)) m Mᴾ ≡ returned resultᴾ)
           × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
        ⊎
        (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)

    backward-return : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
      → n < k
      → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ]
        Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
          (interpretFrom (impreciseStore (core W)) m Mᴵ
            ≡ returned resultᴵ)
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ

    forward-blame : ∀ {n}
      → n < k
      → BlamesFrom (impreciseStore (core W)) n Mᴵ
      → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ

open ComputationsRelated public

------------------------------------------------------------------------
-- Target-only store changes as future-world extensions
------------------------------------------------------------------------

record TargetChangesFuture {Δᴾ Δᴵ Δᶜ Δᴵ′}
    (W : World Δᴾ Δᴵ Δᶜ)
    (changes : StoreChanges Δᴵ Δᴵ′) : Set₁ where
  constructor target-future
  field
    centerCtx : TyCtx
    targetWorld : World Δᴾ Δᴵ′ centerCtx
    targetFuture : Future W targetWorld
    targetStoreAction : impreciseStore (core targetWorld) ≡
      changes ▶ˢ impreciseStore (core W)
    preciseStoreUnchanged : preciseStore (core targetWorld) ≡
      preciseStore (core W)
    targetTermAction : ∀ M → changes ▶ᵀ M ≡
      liftImpreciseTerm targetFuture M
    preciseTermUnchanged : ∀ M →
      liftPreciseTerm targetFuture M ≡ M

open TargetChangesFuture public

record TargetComputationPhase {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (R : IndexedValueRelation W) (k : ℕ)
    (Mᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set₁ where
  field
    -- The imprecise side terminates, whenever the index allows an
    -- observation at all.
    targetReturn : 0 < k
      → Σ[ gas ∈ ℕ ] Σ[ result ∈ E.EvalResult Mᴵ ]
          interpretFrom (impreciseStore (core W)) gas Mᴵ
            ≡ returned result

    targetReturnedRelated : ∀ {gas} {result : E.EvalResult Mᴵ}
      → 0 < k
      → interpretFrom (impreciseStore (core W)) gas Mᴵ ≡ returned result
      → (j : ℕ)
      → j ≤ k
      → Σ[ phase ∈ TargetChangesFuture W (E.changes result) ]
          R (targetWorld phase) (targetFuture phase) j
            (E.term result)
            (liftPreciseTerm (targetFuture phase) Vᴾ)

    targetBlameImpossible : ∀ {gas}
      → gas < k
      → BlamesFrom (impreciseStore (core W)) gas Mᴵ
      → ⊥

open TargetComputationPhase public
