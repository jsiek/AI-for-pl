module proof.LR-narrow.TargetEvaluation where

-- File Charter:
--   * Realizes target-only store changes as imprecise future-world paths.
--   * Proves the store and term actions required by paired LR returns.
--   * Converts completed target phases against values to LR computations.
--   * Keeps the structural recursion on StoreChanges out of the public API.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; zero; _∸_; _≤_)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym; trans)

open import Types
open import CastTerms using (Term; Value; ⇑ᵗᵐ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTerms; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.ImmediateReturn using (value-return)

target-changes-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (changes : StoreChanges Δᴵ Δᴵ′)
  → TargetChangesFuture W changes
target-changes-future W [] =
  target-future _ W future-refl refl refl (λ M → refl) (λ M → refl)
target-changes-future W (keep ∷ changes)
    with target-changes-future W changes
target-changes-future W (keep ∷ changes)
    | target-future Δᶜ′ W′ W≼W′ store-eq precise-store-eq
        term-eq precise-term-eq =
  target-future Δᶜ′ W′ W≼W′ store-eq precise-store-eq
    term-eq precise-term-eq
target-changes-future W (bind A ∷ changes)
    with target-changes-future (impreciseBindWorld W A) changes
target-changes-future W (bind A ∷ changes)
    | target-future Δᶜ′ W′ W₁≼W′ store-eq precise-store-eq
        term-eq precise-term-eq =
  target-future Δᶜ′ W′ W≼W′ store-eq precise-store-eq
    target-term-eq precise-term-eq′
  where
  W≼W₁ = future-imprecise future-refl
  W≼W′ = future-trans W≼W₁ W₁≼W′

  target-term-eq : ∀ M → (bind A ∷ changes) ▶ᵀ M ≡
      liftImpreciseTerm W≼W′ M
  target-term-eq M = trans (term-eq (⇑ᵗᵐ M))
    (sym (liftImpreciseTerm-trans W≼W₁ W₁≼W′ M))

  precise-term-eq′ : ∀ M → liftPreciseTerm W≼W′ M ≡ M
  precise-term-eq′ M = trans
    (liftPreciseTerm-trans W≼W₁ W₁≼W′ M)
    (precise-term-eq M)

target-phase-computations-related : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → TargetComputationPhase W R k Mᴵ Vᴾ
  → ComputationsRelated W R k Mᴵ Vᴾ
target-phase-computations-related {W = W} {R = R} {k = k}
    {Mᴵ = Mᴵ} {Vᴾ = Vᴾ} vVᴾ phase = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = target-forward-blame
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Vᴾ ]
          interpretFrom (preciseStore (core W)) m Vᴾ ≡ returned resultᴾ
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ)
  forward {n = n} {resultᴵ = resultᴵ} n≤k returnᴵ
      with value-return {Σ = preciseStore (core W)} zero vVᴾ
         | targetReturnedRelated phase {gas = n} {result = resultᴵ}
             returnᴵ (k ∸ n) (m∸n≤m k n)
  forward {n = n} {resultᴵ = resultᴵ} n≤k returnᴵ
      | vVᴾ′ , returnᴾ | target-future Δᶜ′ W′ W≼W′ storeᴵ
          storeᴾ termsᴵ termsᴾ , related =
    inj₁ (zero , E.result _ [] Vᴾ ↠-refl vVᴾ′ , returnᴾ ,
      paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ
        (λ M → sym (termsᴾ M))
        (subst (λ V → R W′ W≼W′ (k ∸ n) (E.term resultᴵ) V)
          (termsᴾ Vᴾ) related))

  backward : ∀ {n} {resultᴾ : E.EvalResult Vᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n Vᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ ≡ returned resultᴵ
        × PairedReturns W R (k ∸ n) resultᴵ resultᴾ
  backward {n = n} {resultᴾ = resultᴾ} n≤k returnᴾ
      with value-return {Σ = preciseStore (core W)} n vVᴾ
         | targetReturn phase
  backward {n = n} {resultᴾ = resultᴾ} n≤k returnᴾ
      | vVᴾ′ , value-returnᴾ | m , resultᴵ , returnᴵ
      with trans (sym value-returnᴾ) returnᴾ
         | targetReturnedRelated phase {gas = m} {result = resultᴵ}
             returnᴵ (k ∸ n) (m∸n≤m k n)
  backward {n = n} {resultᴾ = resultᴾ} n≤k returnᴾ
      | vVᴾ′ , value-returnᴾ | m , resultᴵ , returnᴵ
      | refl | target-future Δᶜ′ W′ W≼W′ storeᴵ storeᴾ
          termsᴵ termsᴾ , related =
    m , resultᴵ , returnᴵ ,
    paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ
      (λ M → sym (termsᴾ M))
      (subst (λ V → R W′ W≼W′ (k ∸ n) (E.term resultᴵ) V)
        (termsᴾ Vᴾ) related)

  target-forward-blame : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ
  target-forward-blame n≤k blaming =
    ⊥-elim (targetBlameImpossible phase n≤k blaming)
