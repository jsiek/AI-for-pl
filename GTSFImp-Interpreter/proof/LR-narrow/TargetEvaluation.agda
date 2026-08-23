module proof.LR-narrow.TargetEvaluation where

-- File Charter:
--   * Realizes target-only store changes as imprecise future-world paths.
--   * Proves the store and term actions required by paired LR returns.
--   * Converts completed target phases against values to LR computations.
--   * Keeps the structural recursion on StoreChanges out of the public API.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (m∸n≤m; n≤1+n; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; trans; cong)

open import Types
open import CastTerms using (Term; Value; blame; ⇑ᵗᵐ)
open import Reduction using (StoreChange; applyTerm; _—→[_]_)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTerms; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.ImmediateReturn using (value-return)
open import proof.LR-narrow.BindStepExpansion using
  (step-return; step-blame; step-return-expand; step-return-invert;
   step-blame-invert)

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

target-step-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → (change : StoreChange Δᴵ Δᴵ′)
  → TargetChangesFuture W (change ∷ [])
target-step-future W change = target-changes-future W (change ∷ [])

target-changes-future-prepend : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′ Δᴵ′′}
    {W : World Δᴾ Δᴵ Δᶜ} {change : StoreChange Δᴵ Δᴵ′}
    {changes : StoreChanges Δᴵ′ Δᴵ′′}
  → (first : TargetChangesFuture W (change ∷ []))
  → TargetChangesFuture (targetWorld first) changes
  → TargetChangesFuture W (change ∷ changes)
target-changes-future-prepend {change = change} {changes = changes}
    (target-future Δᶜ₁ W₁ W≼W₁ store₁ precise-store₁
      term₁ precise-term₁)
    (target-future Δᶜ₂ W₂ W₁≼W₂ store₂ precise-store₂
      term₂ precise-term₂) =
  target-future Δᶜ₂ W₂ W≼W₂ store precise-store
    term precise-term
  where
  W≼W₂ = future-trans W≼W₁ W₁≼W₂

  store = trans store₂ (cong (applyStores changes) store₁)

  precise-store = trans precise-store₂ precise-store₁

  term : ∀ M → _ ≡ liftImpreciseTerm W≼W₂ M
  term M = trans (term₂ (change ▷ᵀ M))
    (trans (cong (liftImpreciseTerm W₁≼W₂) (term₁ M))
      (sym (liftImpreciseTerm-trans W≼W₁ W₁≼W₂ M)))

  precise-term : ∀ M → liftPreciseTerm W≼W₂ M ≡ M
  precise-term M = trans
    (liftPreciseTerm-trans W≼W₁ W₁≼W₂ M)
    (trans (cong (liftPreciseTerm W₁≼W₂) (precise-term₁ M))
      (precise-term₂ M))

target-step-phase-expand : ∀ {Δᴾ Δᴵ Δᶜ Δᴵ′}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Nᴵ : Term Δᴵ′}
    {Vᴾ : Term Δᴾ} {change : StoreChange Δᴵ Δᴵ′}
  → Mᴵ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → (step : Mᴵ —→[ change ] Nᴵ)
  → E.step? (impreciseStore (core W)) Mᴵ ≡
      just (E.step-result change Nᴵ step)
  → let first = target-step-future W change
    in TargetComputationPhase (targetWorld first)
      (λ W′ W₁≼W′ →
        R W′ (future-trans (targetFuture first) W₁≼W′))
      k Nᴵ (liftPreciseTerm (targetFuture first) Vᴾ)
  → TargetComputationPhase W R k Mᴵ Vᴾ
target-step-phase-expand {W = W} {R = R} {k = k} {Mᴵ = Mᴵ}
    {Nᴵ = Nᴵ} {Vᴾ = Vᴾ} {change = change}
    Mᴵ≠blame value-eq step step-eq next = record
  { targetReturn = return
  ; targetReturnedRelated = λ {gas} {result} result-eq j j≤k →
      returned-related {gas = gas} {result = result} result-eq j j≤k
  ; targetBlameImpossible = λ {gas} gas≤k blame-result →
      blame-impossible {gas = gas} gas≤k blame-result
  }
  where
  first = target-step-future W change
  W≼W₁ = targetFuture first

  return : Σ[ gas ∈ ℕ ] Σ[ result ∈ E.EvalResult Mᴵ ]
      interpretFrom (impreciseStore (core W)) gas Mᴵ ≡ returned result
  return with targetReturn next
  return | gas , result , result-eq =
    suc gas , _ , step-return-expand {Σ = impreciseStore (core W)}
      {gas = gas} Mᴵ≠blame value-eq step step-eq
      (trans (cong (λ Σ → interpretFrom Σ gas Nᴵ)
        (sym (targetStoreAction first))) result-eq)

  returned-related : ∀ {gas} {result : E.EvalResult Mᴵ}
    → interpretFrom (impreciseStore (core W)) gas Mᴵ ≡ returned result
    → (j : ℕ)
    → j ≤ k
    → Σ[ phase ∈ TargetChangesFuture W (E.changes result) ]
        R (targetWorld phase) (targetFuture phase) j
          (E.term result) (liftPreciseTerm (targetFuture phase) Vᴾ)
  returned-related {gas = zero} result-eq j j≤k
      with step-return-invert {Σ = impreciseStore (core W)} {n = zero}
        Mᴵ≠blame value-eq step step-eq result-eq
  returned-related {gas = zero} result-eq j j≤k | ()
  returned-related {gas = suc gas} result-eq j j≤k
      with step-return-invert {Σ = impreciseStore (core W)}
        {n = suc gas} Mᴵ≠blame value-eq step step-eq result-eq
  returned-related {gas = suc gas} result-eq j j≤k
      | step-return next-result next-return refl
      with targetReturnedRelated next {gas = gas} {result = next-result}
        (trans (cong (λ Σ → interpretFrom Σ gas Nᴵ)
          (targetStoreAction first)) next-return) j j≤k
  returned-related {gas = suc gas} result-eq j j≤k
      | step-return next-result next-return refl
      | later , related =
    target-changes-future-prepend first later ,
    subst
      (λ V → R (targetWorld later)
        (future-trans W≼W₁ (targetFuture later)) j
        (E.term next-result) V)
      (sym (liftPreciseTerm-trans W≼W₁ (targetFuture later) Vᴾ))
      related

  blame-impossible : ∀ {gas}
    → gas ≤ k
    → BlamesFrom (impreciseStore (core W)) gas Mᴵ
    → ⊥
  blame-impossible {gas = zero} gas≤k blame-result
      with step-blame-invert {Σ = impreciseStore (core W)} {n = zero}
        Mᴵ≠blame value-eq step step-eq blame-result
  blame-impossible {gas = zero} gas≤k blame-result | ()
  blame-impossible {gas = suc gas} gas≤k blame-result
      with step-blame-invert {Σ = impreciseStore (core W)}
        {n = suc gas} Mᴵ≠blame value-eq step step-eq blame-result
  blame-impossible {gas = suc gas} gas≤k blame-result
      | step-blame next-blame =
    targetBlameImpossible next {gas = gas}
      (≤-trans (n≤1+n gas) gas≤k)
      (subst (λ Σ → BlamesFrom Σ gas Nᴵ)
        (sym (targetStoreAction first)) next-blame)

related-target-value-phase : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → (∀ j → j ≤ k → R W future-refl j Vᴵ Vᴾ)
  → TargetComputationPhase W R k Vᴵ Vᴾ
related-target-value-phase {W = W} {R = R} {k = k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} vVᴵ related = record
  { targetReturn = immediate-return
  ; targetReturnedRelated = λ {gas} {result} return-result j j≤k →
      returned-related {gas = gas} {result = result} return-result j j≤k
  ; targetBlameImpossible = λ {gas} gas≤k blame-result →
      blame-impossible {gas = gas} gas≤k blame-result
  }
  where
  immediate-return : Σ[ gas ∈ ℕ ] Σ[ result ∈ E.EvalResult Vᴵ ]
      interpretFrom (impreciseStore (core W)) gas Vᴵ ≡ returned result
  immediate-return = zero , E.result _ [] Vᴵ ↠-refl vVᴵ′ , returnᴵ
    where
    value-returned = value-return
      {Σ = impreciseStore (core W)} zero vVᴵ
    vVᴵ′ = proj₁ value-returned
    returnᴵ = proj₂ value-returned

  returned-related : ∀ {gas : ℕ} {result : E.EvalResult Vᴵ}
    → interpretFrom (impreciseStore (core W)) gas Vᴵ ≡ returned result
    → (j : ℕ)
    → j ≤ k
    → Σ[ phase ∈ TargetChangesFuture W (E.changes result) ]
        R (targetWorld phase) (targetFuture phase) j
          (E.term result)
          (liftPreciseTerm (targetFuture phase) Vᴾ)
  returned-related {gas = gas} return-result j j≤k
      with value-return {Σ = impreciseStore (core W)} gas vVᴵ
  returned-related {gas = gas} return-result j j≤k
      | vVᴵ′ , return-value with trans (sym return-value) return-result
  returned-related {gas = gas} return-result j j≤k
      | vVᴵ′ , return-value | refl =
    target-future _ W future-refl refl refl
      (λ M → refl) (λ M → refl) , related j j≤k

  blame-impossible : ∀ {gas : ℕ}
    → gas ≤ k
    → BlamesFrom (impreciseStore (core W)) gas Vᴵ
    → ⊥
  blame-impossible {gas = gas} gas≤k
      (Δ′ , changes , trace , blame-result)
      with value-return {Σ = impreciseStore (core W)} gas vVᴵ
  blame-impossible {gas = gas} gas≤k
      (Δ′ , changes , trace , blame-result)
      | vVᴵ′ , return-value
      with trans (sym return-value) blame-result
  blame-impossible {gas = gas} gas≤k
      (Δ′ , changes , trace , blame-result)
      | vVᴵ′ , return-value | ()

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
