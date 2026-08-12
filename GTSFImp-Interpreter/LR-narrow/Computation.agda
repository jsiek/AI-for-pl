module LR-narrow.Computation where

-- File Charter:
--   * Defines bounded observations of evaluations in distinct LR endpoints.
--   * Permits the precise computation to blame after an imprecise return.
--   * Joins successful endpoint returns in one three-context future world.

open import Data.Nat using (ℕ; _∸_; _≤_)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import CastTerms using (Term; Value; blame)
open import Reduction using (StoreChanges; _—↠[_]_; applyStores)
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
  paired-returns : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {changesᴵ : StoreChanges Δᴵ Δᴵ′}
      {changesᴾ : StoreChanges Δᴾ Δᴾ′}
      {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
      {Mᴵ↞Vᴵ : Mᴵ —↠[ changesᴵ ] Vᴵ}
      {Mᴾ↞Vᴾ : Mᴾ —↠[ changesᴾ ] Vᴾ}
      {vVᴵ : Value Vᴵ} {vVᴾ : Value Vᴾ}
    → (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
    → (W≼W′ : Future W W′)
    → impreciseStore (core W′) ≡
        changesᴵ ▶ˢ impreciseStore (core W)
    → preciseStore (core W′) ≡ changesᴾ ▶ˢ preciseStore (core W)
    → R W′ W≼W′ k Vᴵ Vᴾ
    → PairedReturns W R k
        (E.result Δᴵ′ changesᴵ Vᴵ Mᴵ↞Vᴵ vVᴵ)
        (E.result Δᴾ′ changesᴾ Vᴾ Mᴾ↞Vᴾ vVᴾ)

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
      → n ≤ k
      → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
      →
        (Σ[ m ∈ ℕ ]
         Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
           (interpretFrom (preciseStore (core W)) m Mᴾ ≡ returned resultᴾ)
           × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
        ⊎
        (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)

    backward-return : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
      → n ≤ k
      → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ]
        Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
          (interpretFrom (impreciseStore (core W)) m Mᴵ
            ≡ returned resultᴵ)
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ

    forward-blame : ∀ {n}
      → n ≤ k
      → BlamesFrom (impreciseStore (core W)) n Mᴵ
      → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ

open ComputationsRelated public
