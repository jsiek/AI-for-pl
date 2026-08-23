module proof.LR-narrow.TargetEvaluation where

-- File Charter:
--   * Realizes target-only store changes as imprecise future-world paths.
--   * Proves the store and term actions required by paired LR returns.
--   * Converts target phases to LR computations and back at precise values.
--   * Keeps the structural recursion on StoreChanges out of the public API.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties using (+-comm; m∸n≤m; n≤1+n; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; subst; sym; trans; cong)

open import Types
open import TyStore using (TyStore)
import Imprecision as I
open import CastTerms using
  (Term; Value; `_ ; ƛ_; _·_; Λ_; _⦂∀_[_]; $; _⊕[_]_; _⟨_⟩;
   _↑_; _↓_; blame; ⇑ᵗᵐ)
open import Reduction using
  (StoreChange; applyStore; applyTerm; _—→[_]_)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTerms; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ImmediateReturn using (value-return)
open import proof.LR-narrow.Application using
  (eval-nonblame; eval-from-nonblame; eval-from-return;
   value-return-exact)
open import proof.LR-narrow.BindStepExpansion using
  (step-return; step-blame; step-return-expand; step-return-invert;
   step-blame-invert)
import proof.LR-narrow.Closure as ClosureProof

mutual
  eval-terminal-suc : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
      {M : Term Δ} {outcome : E.EvalOutcome M}
    → E.evalFrom Σ gas M ≡ just outcome
    → E.evalFrom Σ (suc gas) M ≡ just outcome
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = ` x} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = ƛ N} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = L · M} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = Λ N} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = L ⦂∀ B [ A ]} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = $ κ} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = L ⊕[ op ] M} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = M ⟨ c ⟩} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = M ↑ c} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {Σ = Σ} {gas = gas} {M = M ↓ c} =
    eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} (λ ())
  eval-terminal-suc {gas = zero} {M = blame} result-eq
      with result-eq
  eval-terminal-suc {gas = zero} {M = blame} result-eq | refl = refl
  eval-terminal-suc {gas = suc gas} {M = blame} result-eq
      with result-eq
  eval-terminal-suc {gas = suc gas} {M = blame} result-eq | refl = refl

  eval-terminal-suc-nonblame : ∀ {Δ}
      {Σ : TyStore Δ} {gas : ℕ}
      {M : Term Δ} {outcome : E.EvalOutcome M}
    → M ≢ blame
    → E.evalFrom Σ gas M ≡ just outcome
    → E.evalFrom Σ (suc gas) M ≡ just outcome
  eval-terminal-suc-nonblame {Σ = Σ} {gas = gas} {M = M}
      M≠blame result-eq =
    trans (eval-from-nonblame {Σ = Σ} {gas = suc gas} M≠blame)
      (eval-nonblame-terminal-suc {Σ = Σ} {gas = gas} {M = M}
        M≠blame (trans
          (sym (eval-from-nonblame {Σ = Σ} {gas = gas} M≠blame))
          result-eq))

  eval-nonblame-terminal-suc : ∀ {Δ}
      {Σ : TyStore Δ} {gas : ℕ}
      {M : Term Δ} {outcome : E.EvalOutcome M}
    → M ≢ blame
    → eval-nonblame Σ gas M ≡ just outcome
    → eval-nonblame Σ (suc gas) M ≡ just outcome
  eval-nonblame-terminal-suc {gas = zero} {M = M}
      M≠blame result-eq with E.value? M
  eval-nonblame-terminal-suc {gas = zero} M≠blame result-eq
      | just vM = result-eq
  eval-nonblame-terminal-suc {gas = zero} M≠blame result-eq
      | nothing with result-eq
  eval-nonblame-terminal-suc {gas = zero} M≠blame result-eq
      | nothing | ()
  eval-nonblame-terminal-suc {Σ = Σ} {gas = suc gas} {M = M}
      M≠blame result-eq with E.value? M
  eval-nonblame-terminal-suc {gas = suc gas} M≠blame result-eq
      | just vM = result-eq
  eval-nonblame-terminal-suc {Σ = Σ} {gas = suc gas} {M = M}
      M≠blame result-eq | nothing with E.step? Σ M
  eval-nonblame-terminal-suc {gas = suc gas} M≠blame result-eq
      | nothing | nothing with result-eq
  eval-nonblame-terminal-suc {gas = suc gas} M≠blame result-eq
      | nothing | nothing | ()
  eval-nonblame-terminal-suc {Σ = Σ} {gas = suc gas} {M = M}
      M≠blame result-eq
      | nothing | just (E.step-result change N step)
      with E.evalFrom (applyStore change Σ) gas N in next-eq
  eval-nonblame-terminal-suc {gas = suc gas} M≠blame result-eq
      | nothing | just (E.step-result change N step)
      | nothing with result-eq
  eval-nonblame-terminal-suc {gas = suc gas} M≠blame result-eq
      | nothing | just (E.step-result change N step)
      | nothing | ()
  eval-nonblame-terminal-suc {Σ = Σ} {gas = suc gas} {M = M}
      M≠blame result-eq
      | nothing | just (E.step-result change N step)
      | just next-outcome
      rewrite eval-terminal-suc {Σ = applyStore change Σ} {gas = gas}
        {M = N} {outcome = next-outcome} next-eq = result-eq

eval-terminal-plus : ∀ {Δ} {Σ : TyStore Δ} {gas extra : ℕ}
    {M : Term Δ} {outcome : E.EvalOutcome M}
  → E.evalFrom Σ gas M ≡ just outcome
  → E.evalFrom Σ (extra + gas) M ≡ just outcome
eval-terminal-plus {extra = zero} result-eq = result-eq
eval-terminal-plus {Σ = Σ} {gas = gas} {extra = suc extra}
    {M = M} {outcome = outcome} result-eq =
  eval-terminal-suc {Σ = Σ} {gas = extra + gas}
    {M = M} {outcome = outcome}
    (eval-terminal-plus {Σ = Σ} {gas = gas} {extra = extra}
      {M = M} {outcome = outcome} result-eq)

eval-terminal-unique : ∀ {Δ} {Σ : TyStore Δ}
    {leftGas rightGas : ℕ} {M : Term Δ}
    {left right : E.EvalOutcome M}
  → E.evalFrom Σ leftGas M ≡ just left
  → E.evalFrom Σ rightGas M ≡ just right
  → left ≡ right
eval-terminal-unique {Σ = Σ} {leftGas = leftGas} {rightGas = rightGas}
    {M = M} {left = left} {right = right}
    left-eq right-eq with trans (sym left-common) right-common
  where
  left-common : E.evalFrom Σ (leftGas + rightGas) M ≡ just left
  left-common = subst
    (λ gas → E.evalFrom Σ gas M ≡ just left)
    (+-comm rightGas leftGas)
    (eval-terminal-plus {Σ = Σ} {gas = leftGas} {extra = rightGas}
      {M = M} {outcome = left} left-eq)

  right-common : E.evalFrom Σ (leftGas + rightGas) M ≡ just right
  right-common = eval-terminal-plus {Σ = Σ} {gas = rightGas}
    {extra = leftGas} {M = M} {outcome = right} right-eq
eval-terminal-unique left-eq right-eq | refl = refl

return-result-unique : ∀ {Δ} {Σ : TyStore Δ}
    {leftGas rightGas : ℕ} {M : Term Δ}
    {left right : E.EvalResult M}
  → interpretFrom Σ leftGas M ≡ returned left
  → interpretFrom Σ rightGas M ≡ returned right
  → left ≡ right
return-result-unique {Σ = Σ} {leftGas = leftGas}
    {rightGas = rightGas} {M = M} left-eq right-eq
    with eval-terminal-unique {Σ = Σ} {leftGas = leftGas}
      {rightGas = rightGas}
      (eval-from-return {Σ = Σ} {gas = leftGas} {M = M} left-eq)
      (eval-from-return {Σ = Σ} {gas = rightGas} {M = M} right-eq)
return-result-unique left-eq right-eq | refl = refl

computations-related-target-phase : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {W≼W′ : Future W W′} {j : ℕ} {Uᴵ : Term Δᴵ′}
      {Uᴾ : Term Δᴾ′}
    → j ≤ k
    → R W′ W≼W′ k Uᴵ Uᴾ
    → R W′ W≼W′ j Uᴵ Uᴾ)
  → ComputationsRelated W R k Mᴵ Vᴾ
  → TargetComputationPhase W R k Mᴵ Vᴾ
computations-related-target-phase {W = W} {R = R} {k = k}
    {Mᴵ = Mᴵ} {Vᴾ = Vᴾ} vVᴾ downward related = record
  { targetReturn = target-return
  ; targetReturnedRelated = λ {gas} {result} result-eq j j≤k →
      returned-related {gas = gas} {result = result} result-eq j j≤k
  ; targetBlameImpossible = λ {gas} gas≤k blame-result →
      blame-impossible {gas = gas} gas≤k blame-result
  }
  where
  precise-result = E.result _ [] Vᴾ ↠-refl vVᴾ

  precise-return = value-return-exact
    {Σ = preciseStore (core W)} zero vVᴾ

  canonical = backward-return related z≤n precise-return

  target-return : Σ[ gas ∈ ℕ ] Σ[ result ∈ E.EvalResult Mᴵ ]
      interpretFrom (impreciseStore (core W)) gas Mᴵ ≡ returned result
  target-return with canonical
  target-return | gas , result , result-eq , paired =
    gas , result , result-eq

  paired-returned-related : ∀ {result : E.EvalResult Mᴵ}
    → PairedReturns W R k result precise-result
    → (j : ℕ)
    → j ≤ k
    → Σ[ phase ∈ TargetChangesFuture W (E.changes result) ]
        R (targetWorld phase) (targetFuture phase) j
          (E.term result) (liftPreciseTerm (targetFuture phase) Vᴾ)
  paired-returned-related
      (paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ termsᴾ at-k)
      j j≤k =
    target-future _ W′ W≼W′ storeᴵ storeᴾ termsᴵ
      (λ M → sym (termsᴾ M)) ,
    subst (λ U → R W′ W≼W′ j _ U) (termsᴾ Vᴾ)
      (downward j≤k at-k)

  returned-related : ∀ {gas} {result : E.EvalResult Mᴵ}
    → interpretFrom (impreciseStore (core W)) gas Mᴵ ≡ returned result
    → (j : ℕ)
    → j ≤ k
    → Σ[ phase ∈ TargetChangesFuture W (E.changes result) ]
        R (targetWorld phase) (targetFuture phase) j
          (E.term result) (liftPreciseTerm (targetFuture phase) Vᴾ)
  returned-related result-eq j j≤k with canonical
  returned-related {gas = gas} {result = result} result-eq j j≤k
      | canonical-gas , canonical-result , canonical-return , paired
      with return-result-unique
        {Σ = impreciseStore (core W)} {leftGas = gas}
        {rightGas = canonical-gas} {M = Mᴵ}
        {left = result} {right = canonical-result}
        result-eq canonical-return
  returned-related {gas = gas} {result = result} result-eq j j≤k
      | canonical-gas , canonical-result , canonical-return , paired
      | refl = paired-returned-related paired j j≤k

  blame-impossible : ∀ {gas}
    → gas ≤ k
    → BlamesFrom (impreciseStore (core W)) gas Mᴵ
    → ⊥
  blame-impossible gas≤k blame-result
      with forward-blame related gas≤k blame-result
  blame-impossible gas≤k blame-result
      | precise-gas , Δ′ , changes , trace , precise-blame
      with trans
        (sym (value-return-exact {Σ = preciseStore (core W)}
          precise-gas vVᴾ))
        precise-blame
  blame-impossible gas≤k blame-result
      | precise-gas , Δ′ , changes , trace , precise-blame | ()

future-value-computations-target-phase : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Vᴾ
  → TargetComputationPhase W (FutureValueRelation p) k Mᴵ Vᴾ
future-value-computations-target-phase vVᴾ =
  computations-related-target-phase vVᴾ
    ClosureProof.value-imprecision-downward-to

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
