module proof.LR-narrow.StepExpansion where

-- File Charter:
--   * Expands related computations across matching pure reduction steps.
--   * Inverts evaluator returns and blame at a known non-value redex.
--   * Keeps store-changing allocation steps outside this generic layer.

open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc; _∸_; _≤_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import proof.LR-narrow.Application using
  (prepend-result; prepend-blame; prepend-eval-outcome;
   eval-from-nonblame; eval-from-return; eval-from-blame;
   return-from-eval; blame-from-eval; paired-returns-reindex)
open import proof.LR-narrow.BetaExpansion using
  (interpreter-outcome; interpret-from-eval)

prepend-step-interpreter-outcome : ∀ {Δ} {M N : Term Δ}
  → M —→ N
  → Outcome N
  → Outcome M
prepend-step-interpreter-outcome step timed = timed
prepend-step-interpreter-outcome step (returned result) =
  returned (prepend-result (pure-step step) result)
prepend-step-interpreter-outcome step (blamed changes trace) =
  blamed (keep ∷ changes)
    (prepend-blame (pure-step step) changes trace)

interpreter-prepend-step-map : ∀ {Δ} {M N : Term Δ}
  → (step : M —→ N)
  → (outcome : Maybe.Maybe (E.EvalOutcome N))
  → interpreter-outcome
      (Maybe.map (prepend-eval-outcome (pure-step step)) outcome)
      ≡ prepend-step-interpreter-outcome step
          (interpreter-outcome outcome)
interpreter-prepend-step-map step nothing = refl
interpreter-prepend-step-map step (just (E.returned result)) = refl
interpreter-prepend-step-map step (just (E.blamed changes trace)) = refl

pure-step-eval-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M N : Term Δ}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → E.step? Σ M ≡ just (E.step-result keep N (pure-step step))
  → E.evalFrom Σ (suc gas) M ≡
      Maybe.map (prepend-eval-outcome (pure-step step))
        (E.evalFrom Σ gas N)
pure-step-eval-from {Σ = Σ} {gas = gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    with E.evalFrom Σ gas N in next-eq
pure-step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq | nothing
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl
pure-step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq | just (E.returned result)
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl
pure-step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq
    | just (E.blamed changes trace)
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl

pure-step-interpret-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M N : Term Δ}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → E.step? Σ M ≡ just (E.step-result keep N (pure-step step))
  → interpretFrom Σ (suc gas) M ≡
      prepend-step-interpreter-outcome step (interpretFrom Σ gas N)
pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
    M≢blame value-eq step step-eq =
  trans (interpret-from-eval {Σ = Σ} {gas = suc gas} {M = M})
    (trans (cong interpreter-outcome
      (pure-step-eval-from {Σ = Σ} {gas = gas} {M = M} {N = N}
        M≢blame value-eq step step-eq))
      (trans (interpreter-prepend-step-map step
        (E.evalFrom Σ gas N))
        (cong (prepend-step-interpreter-outcome step)
          (sym (interpret-from-eval {Σ = Σ} {gas = gas} {M = N})))))

pure-step-return-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M N : Term Δ} {result : E.EvalResult N}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → (step-eq : E.step? Σ M ≡
      just (E.step-result keep N (pure-step step)))
  → interpretFrom Σ gas N ≡ returned result
  → interpretFrom Σ (suc gas) M ≡
      returned (prepend-result (pure-step step) result)
pure-step-return-expand {Σ = Σ} {gas = gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq =
  trans (pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M}
      {N = N} M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) result-eq)

nonvalue-zero-timed : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → M ≢ blame
  → E.value? M ≡ nothing
  → interpretFrom Σ Data.Nat.zero M ≡ timed
nonvalue-zero-timed {Σ = Σ} {M = M} M≢blame value-eq
    with E.evalFrom Σ Data.Nat.zero M in eval-eq
nonvalue-zero-timed M≢blame value-eq | nothing = refl
nonvalue-zero-timed {Σ = Σ} {M = M} M≢blame value-eq
    | just outcome
    with trans (sym (eval-from-nonblame {Σ = Σ}
      {gas = Data.Nat.zero} M≢blame)) eval-eq
nonvalue-zero-timed M≢blame value-eq | just outcome | normalized-eq
    rewrite value-eq with normalized-eq
nonvalue-zero-timed M≢blame value-eq | just outcome | normalized-eq | ()

data PureStepReturn {Δ : TyCtx} (Σ : TyStore Δ)
    {M N : Term Δ} (step : M —→ N) (result : E.EvalResult M) :
    ℕ → Set where
  pure-step-return : ∀ {gas} (next-result : E.EvalResult N)
    → interpretFrom Σ gas N ≡ returned next-result
    → result ≡ prepend-result (pure-step step) next-result
    → PureStepReturn Σ step result (suc gas)

data PureStepBlame {Δ : TyCtx} (Σ : TyStore Δ)
    {M N : Term Δ} (step : M —→ N) : ℕ → Set where
  pure-step-blame : ∀ {gas}
    → BlamesFrom Σ gas N
    → PureStepBlame Σ step (suc gas)

pure-step-return-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {M N : Term Δ} {result : E.EvalResult M}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → (step-eq : E.step? Σ M ≡
      just (E.step-result keep N (pure-step step)))
  → interpretFrom Σ n M ≡ returned result
  → PureStepReturn Σ step result n
pure-step-return-invert {Σ = Σ} {n = Data.Nat.zero} {M = M}
    M≢blame value-eq step step-eq result-eq
    with trans (sym (nonvalue-zero-timed {Σ = Σ} {M = M}
      M≢blame value-eq)) result-eq
pure-step-return-invert M≢blame value-eq step step-eq result-eq | ()
pure-step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq
    with E.evalFrom Σ gas N in next-eq
pure-step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq | nothing
    with trans (sym whole-timed) result-eq
    where
    next-timed : interpretFrom Σ gas N ≡ timed
    next-timed = trans
      (interpret-from-eval {Σ = Σ} {gas = gas} {M = N})
      (cong interpreter-outcome next-eq)

    whole-timed : interpretFrom Σ (suc gas) M ≡ timed
    whole-timed = trans
      (pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M}
        {N = N} M≢blame value-eq step step-eq)
      (cong (prepend-step-interpreter-outcome step) next-timed)
pure-step-return-invert M≢blame value-eq step step-eq result-eq
    | nothing | ()
pure-step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq
    | just (E.returned next-result)
    with trans (sym exact-return) result-eq
    where
    exact-return : interpretFrom Σ (suc gas) M ≡
      returned (prepend-result (pure-step step) next-result)
    exact-return = pure-step-return-expand {Σ = Σ} {gas = gas}
      {M = M} {N = N} M≢blame value-eq step step-eq
      (return-from-eval {Σ = Σ} {gas = gas} {M = N} next-eq)
pure-step-return-invert {Σ = Σ} {n = suc gas} {N = N}
    M≢blame value-eq step step-eq result-eq
    | just (E.returned next-result) | refl =
  pure-step-return next-result
    (return-from-eval {Σ = Σ} {gas = gas} {M = N} next-eq) refl
pure-step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    with blame-from-eval {Σ = Σ} {gas = gas} {M = N} next-eq
pure-step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    | Δ′ , changes′ , trace′ , next-blame-eq
    with trans (sym blame-eq) result-eq
    where
    blame-eq : interpretFrom Σ (suc gas) M ≡
      blamed (keep ∷ changes′)
        (prepend-blame (pure-step step) changes′ trace′)
    blame-eq = trans
      (pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M}
        {N = N} M≢blame value-eq step step-eq)
      (cong (prepend-step-interpreter-outcome step) next-blame-eq)
pure-step-return-invert M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    | Δ′ , changes′ , trace′ , next-blame-eq | ()

pure-step-blame-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M N : Term Δ}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → (step-eq : E.step? Σ M ≡
      just (E.step-result keep N (pure-step step)))
  → BlamesFrom Σ gas N
  → BlamesFrom Σ (suc gas) M
pure-step-blame-expand {Σ = Σ} {gas = gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq) =
  Δ′ , keep ∷ changes , prepend-blame (pure-step step) changes trace ,
  trans (pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M}
      {N = N} M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) result-eq)

pure-step-blame-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {M N : Term Δ}
  → (M≢blame : M ≢ blame)
  → (value-eq : E.value? M ≡ nothing)
  → (step : M —→ N)
  → (step-eq : E.step? Σ M ≡
      just (E.step-result keep N (pure-step step)))
  → BlamesFrom Σ n M
  → PureStepBlame Σ step n
pure-step-blame-invert {Σ = Σ} {n = Data.Nat.zero} {M = M}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    with trans (sym (nonvalue-zero-timed {Σ = Σ} {M = M}
      M≢blame value-eq)) result-eq
pure-step-blame-invert M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq) | ()
pure-step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    with E.evalFrom Σ gas N in next-eq
pure-step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    | nothing
    with trans (sym whole-timed) result-eq
    where
    next-timed : interpretFrom Σ gas N ≡ timed
    next-timed = trans
      (interpret-from-eval {Σ = Σ} {gas = gas} {M = N})
      (cong interpreter-outcome next-eq)

    whole-timed : interpretFrom Σ (suc gas) M ≡ timed
    whole-timed = trans
      (pure-step-interpret-from {Σ = Σ} {gas = gas} {M = M}
        {N = N} M≢blame value-eq step step-eq)
      (cong (prepend-step-interpreter-outcome step) next-timed)
pure-step-blame-invert M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    | nothing | ()
pure-step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    | just (E.returned result)
    with trans (sym exact-return) result-eq
    where
    exact-return : interpretFrom Σ (suc gas) M ≡
      returned (prepend-result (pure-step step) result)
    exact-return = pure-step-return-expand {Σ = Σ} {gas = gas}
      {M = M} {N = N} M≢blame value-eq step step-eq
      (return-from-eval {Σ = Σ} {gas = gas} {M = N} next-eq)
pure-step-blame-invert M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    | just (E.returned result) | ()
pure-step-blame-invert {Σ = Σ} {n = suc gas} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    | just (E.blamed next-changes next-trace) =
  pure-step-blame
    (blame-from-eval {Σ = Σ} {gas = gas} {M = N} next-eq)

paired-returns-pure-step : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
    {stepᴵ : Mᴵ —→ Nᴵ} {stepᴾ : Mᴾ —→ Nᴾ}
    {resultᴵ : E.EvalResult Nᴵ} {resultᴾ : E.EvalResult Nᴾ}
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W R k
      (prepend-result (pure-step stepᴵ) resultᴵ)
      (prepend-result (pure-step stepᴾ) resultᴾ)
paired-returns-pure-step
    (paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ termsᴾ related) =
  paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ termsᴾ related

related-pure-step-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
  → (Mᴵ≢blame : Mᴵ ≢ blame)
  → (Mᴾ≢blame : Mᴾ ≢ blame)
  → (value-eqᴵ : E.value? Mᴵ ≡ nothing)
  → (value-eqᴾ : E.value? Mᴾ ≡ nothing)
  → (stepᴵ : Mᴵ —→ Nᴵ)
  → (stepᴾ : Mᴾ —→ Nᴾ)
  → E.step? (impreciseStore (core W)) Mᴵ ≡
      just (E.step-result keep Nᴵ (pure-step stepᴵ))
  → E.step? (preciseStore (core W)) Mᴾ ≡
      just (E.step-result keep Nᴾ (pure-step stepᴾ))
  → ComputationsRelated W R k Nᴵ Nᴾ
  → ComputationsRelated W R (suc k) Mᴵ Mᴾ
related-pure-step-expand {W = W} {R = R} {k = k}
    {Mᴵ = Mᴵ} {Nᴵ = Nᴵ} {Mᴾ = Mᴾ} {Nᴾ = Nᴾ}
    Mᴵ≢blame Mᴾ≢blame value-eqᴵ value-eqᴾ stepᴵ stepᴾ
    step-eqᴵ step-eqᴾ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ suc k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W R (suc k ∸ n) resultᴵ resultᴾ)
       ⊎ (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = Data.Nat.zero} n≤sk result-eq
      with pure-step-return-invert
        {Σ = impreciseStore (core W)} {n = Data.Nat.zero}
        {M = Mᴵ} {N = Nᴵ} Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ
        result-eq
  forward {n = Data.Nat.zero} n≤sk result-eq | ()
  forward {n = suc n} n≤sk result-eq
      with pure-step-return-invert
        {Σ = impreciseStore (core W)} {n = suc n}
        {M = Mᴵ} {N = Nᴵ} Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ
        result-eq
  forward {n = suc n} n≤sk result-eq
      | pure-step-return resultᴵ′ returnᴵ resultᴵ-eq
      with forward-return related (≤-pred n≤sk) returnᴵ
  forward {n = suc n} n≤sk result-eq
      | pure-step-return resultᴵ′ returnᴵ resultᴵ-eq
      | inj₁ (m , resultᴾ′ , returnᴾ , paired) =
    inj₁ (suc m , prepend-result (pure-step stepᴾ) resultᴾ′ ,
      pure-step-return-expand {Σ = preciseStore (core W)} {gas = m}
        {M = Mᴾ} {N = Nᴾ} Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ
        returnᴾ , paired-returns-reindex resultᴵ-eq refl
          (paired-returns-pure-step paired))
  forward {n = suc n} n≤sk result-eq
      | pure-step-return resultᴵ′ returnᴵ resultᴵ-eq
      | inj₂ (m , blamingᴾ) =
    inj₂ (suc m , pure-step-blame-expand
      {Σ = preciseStore (core W)} {gas = m} {M = Mᴾ} {N = Nᴾ}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ blamingᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n ≤ suc k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W R (suc k ∸ n) resultᴵ resultᴾ
  backward {n = Data.Nat.zero} n≤sk result-eq
      with pure-step-return-invert
        {Σ = preciseStore (core W)} {n = Data.Nat.zero}
        {M = Mᴾ} {N = Nᴾ} Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ
        result-eq
  backward {n = Data.Nat.zero} n≤sk result-eq | ()
  backward {n = suc n} n≤sk result-eq
      with pure-step-return-invert
        {Σ = preciseStore (core W)} {n = suc n}
        {M = Mᴾ} {N = Nᴾ} Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ
        result-eq
  backward {n = suc n} n≤sk result-eq
      | pure-step-return resultᴾ′ returnᴾ resultᴾ-eq
      with backward-return related (≤-pred n≤sk) returnᴾ
  backward {n = suc n} n≤sk result-eq
      | pure-step-return resultᴾ′ returnᴾ resultᴾ-eq
      | m , resultᴵ′ , returnᴵ , paired =
    suc m , prepend-result (pure-step stepᴵ) resultᴵ′ ,
    pure-step-return-expand {Σ = impreciseStore (core W)} {gas = m}
      {M = Mᴵ} {N = Nᴵ} Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ
      returnᴵ , paired-returns-reindex refl resultᴾ-eq
        (paired-returns-pure-step paired)

  blame-forward : ∀ {n}
    → n ≤ suc k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = Data.Nat.zero} n≤sk blamingᴵ
      with pure-step-blame-invert
        {Σ = impreciseStore (core W)} {n = Data.Nat.zero}
        {M = Mᴵ} {N = Nᴵ} Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ
        blamingᴵ
  blame-forward {n = Data.Nat.zero} n≤sk blamingᴵ | ()
  blame-forward {n = suc n} n≤sk blamingᴵ
      with pure-step-blame-invert
        {Σ = impreciseStore (core W)} {n = suc n}
        {M = Mᴵ} {N = Nᴵ} Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ
        blamingᴵ
  blame-forward {n = suc n} n≤sk blamingᴵ
      | pure-step-blame blamingᴵ′
      with forward-blame related (≤-pred n≤sk) blamingᴵ′
  blame-forward {n = suc n} n≤sk blamingᴵ
      | pure-step-blame blamingᴵ′ | m , blamingᴾ′ =
    suc m , pure-step-blame-expand {Σ = preciseStore (core W)}
      {gas = m} {M = Mᴾ} {N = Nᴾ} Mᴾ≢blame value-eqᴾ stepᴾ
      step-eqᴾ blamingᴾ′
