module LR.Computation where

-- File Charter:
--   * Defines bounded observations of pairs of GTSFImp evaluations.
--   * Permits the more-precise computation to blame after an imprecise return.
--   * Requires successful paired returns to induce one paired future world.

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
open import LR.World

IndexedValueRelation : ∀ {Δ} → World Δ → Set₂
IndexedValueRelation W = ∀ {Δ′} (W′ : World Δ′)
  → Future W W′
  → ℕ
  → Term Δ′
  → Term Δ′
  → Set₁

data PairedReturns {Δ : TyCtx} {Mᴵ Mᴾ : Term Δ}
    (W : World Δ) (R : IndexedValueRelation W) (k : ℕ) :
    E.EvalResult Mᴵ → E.EvalResult Mᴾ → Set₁ where
  paired-returns : ∀ {Δ′}
      {changesᴵ changesᴾ : StoreChanges Δ Δ′}
      {Vᴵ Vᴾ : Term Δ′}
      {Mᴵ↞Vᴵ : Mᴵ —↠[ changesᴵ ] Vᴵ}
      {Mᴾ↞Vᴾ : Mᴾ —↠[ changesᴾ ] Vᴾ}
      {vVᴵ : Value Vᴵ} {vVᴾ : Value Vᴾ}
    → (W′ : World Δ′)
    → (W≼W′ : Future W W′)
    → impreciseStore W′ ≡ changesᴵ ▶ˢ impreciseStore W
    → preciseStore W′ ≡ changesᴾ ▶ˢ preciseStore W
    → R W′ W≼W′ k Vᴵ Vᴾ
    → PairedReturns W R k
        (E.result Δ′ changesᴵ Vᴵ Mᴵ↞Vᴵ vVᴵ)
        (E.result Δ′ changesᴾ Vᴾ Mᴾ↞Vᴾ vVᴾ)

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

record ComputationsRelated {Δ : TyCtx}
    (W : World Δ) (R : IndexedValueRelation W) (k : ℕ)
    (Mᴵ Mᴾ : Term Δ) : Set₁ where
  field
    forward-return : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
      → n ≤ k
      → interpretFrom (impreciseStore W) n Mᴵ ≡ returned resultᴵ
      →
        (Σ[ m ∈ ℕ ]
         Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
           (interpretFrom (preciseStore W) m Mᴾ ≡ returned resultᴾ) ×
           PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
        ⊎
        (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore W) m Mᴾ)

    backward-return : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
      → n ≤ k
      → interpretFrom (preciseStore W) n Mᴾ ≡ returned resultᴾ
      → Σ[ m ∈ ℕ ]
        Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
          (interpretFrom (impreciseStore W) m Mᴵ ≡ returned resultᴵ) ×
          PairedReturns W R (k ∸ n) resultᴵ resultᴾ

    forward-blame : ∀ {n}
      → n ≤ k
      → BlamesFrom (impreciseStore W) n Mᴵ
      → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore W) m Mᴾ

open ComputationsRelated public
