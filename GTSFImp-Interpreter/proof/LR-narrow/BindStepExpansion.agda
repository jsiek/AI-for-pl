module proof.LR-narrow.BindStepExpansion where

-- File Charter:
--   * Expands related computations across matching allocation steps.
--   * Records that returned worlds factor through the paired binding.
--   * Abstracts over the redex shape used by universal and cast proofs.

open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.Application using
  (prepend-result; prepend-blame; prepend-eval-outcome;
   eval-from-nonblame; return-from-eval; blame-from-eval;
   paired-returns-reindex)
open import proof.LR-narrow.BetaExpansion using
  (interpreter-outcome; interpret-from-eval)
open import proof.LR-narrow.StepExpansion using (nonvalue-zero-timed)
import proof.LR-narrow.Closure as ClosureProof

paired-bind-step : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → Future W (pairedBindWorld W Rᴾ Rᴵ r)
paired-bind-step W r = future-paired future-refl r

prepend-step-interpreter-outcome : ∀ {Δ Δ′}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → M —→[ χ ] N
  → Outcome N
  → Outcome M
prepend-step-interpreter-outcome step timed = timed
prepend-step-interpreter-outcome step (returned result) =
  returned (prepend-result step result)
prepend-step-interpreter-outcome step (blamed changes trace) =
  blamed (_ ∷ changes) (prepend-blame step changes trace)

interpreter-prepend-step-map : ∀ {Δ Δ′}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → (step : M —→[ χ ] N)
  → (outcome : Maybe.Maybe (E.EvalOutcome N))
  → interpreter-outcome (Maybe.map (prepend-eval-outcome step) outcome)
      ≡ prepend-step-interpreter-outcome step (interpreter-outcome outcome)
interpreter-prepend-step-map step nothing = refl
interpreter-prepend-step-map step (just (E.returned result)) = refl
interpreter-prepend-step-map step (just (E.blamed changes trace)) = refl

step-eval-from : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → E.evalFrom Σ (suc gas) M ≡
      Maybe.map (prepend-eval-outcome step)
        (E.evalFrom (applyStore χ Σ) gas N)
step-eval-from {Σ = Σ} {gas = gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq
    with E.evalFrom (applyStore χ Σ) gas N in next-eq
step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq | nothing
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl
step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq | just (E.returned result)
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl
step-eval-from {Σ = Σ} {gas = gas} {M = M}
    M≢blame value-eq step step-eq | just (E.blamed changes trace)
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
          | value-eq | step-eq | next-eq = refl

step-interpret-from : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → interpretFrom Σ (suc gas) M ≡
      prepend-step-interpreter-outcome step
        (interpretFrom (applyStore χ Σ) gas N)
step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq =
  trans (interpret-from-eval {Σ = Σ} {gas = suc gas} {M = M})
    (trans (cong interpreter-outcome
      (step-eval-from {Σ = Σ} {gas = gas} {M = M} {N = N}
        M≢blame value-eq step step-eq))
      (trans (interpreter-prepend-step-map step
        (E.evalFrom (applyStore χ Σ) gas N))
        (cong (prepend-step-interpreter-outcome step)
          (sym (interpret-from-eval {Σ = applyStore χ Σ}
            {gas = gas} {M = N})))))

step-return-expand : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
    {result : E.EvalResult N}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → interpretFrom (applyStore χ Σ) gas N ≡ returned result
  → interpretFrom Σ (suc gas) M ≡
      returned (prepend-result step result)
step-return-expand {Σ = Σ} {gas = gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq =
  trans (step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
      {χ = χ}
      M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) result-eq)

data StepReturn {Δ Δ′ : TyCtx} (Σ : TyStore Δ)
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
    (step : M —→[ χ ] N) (result : E.EvalResult M) : ℕ → Set where
  step-return : ∀ {gas} (next-result : E.EvalResult N)
    → interpretFrom (applyStore χ Σ) gas N ≡ returned next-result
    → result ≡ prepend-result step next-result
    → StepReturn Σ step result (suc gas)

data StepBlame {Δ Δ′ : TyCtx} (Σ : TyStore Δ)
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
    (step : M —→[ χ ] N) : ℕ → Set where
  step-blame : ∀ {gas}
    → BlamesFrom (applyStore χ Σ) gas N
    → StepBlame Σ step (suc gas)

step-return-invert : ∀ {Δ Δ′} {Σ : TyStore Δ} {n : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
    {result : E.EvalResult M}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → (step-eq : E.step? Σ M ≡ just (E.step-result χ N step))
  → interpretFrom Σ n M ≡ returned result
  → StepReturn Σ step result n
step-return-invert {Σ = Σ} {n = zero} {M = M}
    M≢blame value-eq step step-eq result-eq
    with trans (sym (nonvalue-zero-timed {Σ = Σ} {M = M}
      M≢blame value-eq)) result-eq
step-return-invert M≢blame value-eq step step-eq result-eq | ()
step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq
    with E.evalFrom (applyStore χ Σ) gas N in next-eq
step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq | nothing
    with trans (sym whole-timed) result-eq
  where
  next-timed = trans
    (interpret-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N})
    (cong interpreter-outcome next-eq)
  whole-timed = trans
    (step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
      {χ = χ}
      M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) next-timed)
step-return-invert M≢blame value-eq step step-eq result-eq
    | nothing | ()
step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq
    | just (E.returned next-result)
    with trans (sym exact-return) result-eq
  where
  exact-return = step-return-expand {Σ = Σ} {gas = gas}
    {M = M} {N = N} {χ = χ} M≢blame value-eq step step-eq
    (return-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N}
      next-eq)
step-return-invert {Σ = Σ} {n = suc gas} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq
    | just (E.returned next-result) | refl =
  step-return next-result
    (return-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N}
      next-eq) refl
step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    with blame-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N}
      next-eq
step-return-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    | Δ′ , changes′ , trace′ , next-blame-eq
    with trans (sym blame-eq) result-eq
  where
  blame-eq = trans
    (step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
      {χ = χ}
      M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) next-blame-eq)
step-return-invert M≢blame value-eq step step-eq result-eq
    | just (E.blamed changes trace)
    | Δ′ , changes′ , trace′ , next-blame-eq | ()

step-blame-expand : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → BlamesFrom (applyStore χ Σ) gas N
  → BlamesFrom Σ (suc gas) M
step-blame-expand {Σ = Σ} {gas = gas} {M = M} {N = N}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq) =
  Δ′ , _ ∷ changes , prepend-blame step changes trace ,
  trans (step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
      M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) result-eq)

step-blame-invert : ∀ {Δ Δ′} {Σ : TyStore Δ} {n : ℕ}
    {M : Term Δ} {N : Term Δ′} {χ : StoreChange Δ Δ′}
  → M ≢ blame
  → E.value? M ≡ nothing
  → (step : M —→[ χ ] N)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → BlamesFrom Σ n M
  → StepBlame Σ step n
step-blame-invert {Σ = Σ} {n = zero} {M = M}
    M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq)
    with trans (sym (nonvalue-zero-timed {Σ = Σ} {M = M}
      M≢blame value-eq)) result-eq
step-blame-invert M≢blame value-eq step step-eq
    (Δ′ , changes , trace , result-eq) | ()
step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq blameWitness
    with E.evalFrom (applyStore χ Σ) gas N in next-eq
step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq blameWitness | nothing
    with trans (sym whole-timed) (Data.Product.proj₂
      (Data.Product.proj₂ (Data.Product.proj₂ blameWitness)))
  where
  next-timed = trans
    (interpret-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N})
    (cong interpreter-outcome next-eq)
  whole-timed = trans
    (step-interpret-from {Σ = Σ} {gas = gas} {M = M} {N = N}
      {χ = χ}
      M≢blame value-eq step step-eq)
    (cong (prepend-step-interpreter-outcome step) next-timed)
step-blame-invert M≢blame value-eq step step-eq blameWitness
    | nothing | ()
step-blame-invert {Σ = Σ} {n = suc gas} {M = M} {N = N} {χ = χ}
    M≢blame value-eq step step-eq blameWitness
    | just (E.returned result)
    with trans (sym exact-return) (Data.Product.proj₂
      (Data.Product.proj₂ (Data.Product.proj₂ blameWitness)))
  where
  exact-return = step-return-expand {Σ = Σ} {gas = gas}
    {M = M} {N = N} {χ = χ} M≢blame value-eq step step-eq
    (return-from-eval {Σ = applyStore χ Σ} {gas = gas} {M = N}
      next-eq)
step-blame-invert M≢blame value-eq step step-eq blameWitness
    | just (E.returned result) | ()
step-blame-invert {Σ = Σ} {n = suc gas} {N = N} {χ = χ}
    M≢blame value-eq step step-eq blameWitness
    | just (E.blamed changes trace) =
  step-blame (blame-from-eval {Σ = applyStore χ Σ} {gas = gas}
    {M = N} next-eq)

paired-returns-bind-step : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {Mᴵ : Term Δᴵ} {Nᴵ : Term (suc Δᴵ)}
    {Mᴾ : Term Δᴾ} {Nᴾ : Term (suc Δᴾ)}
    {stepᴵ : Mᴵ —→[ bind Rᴵ ] Nᴵ}
    {stepᴾ : Mᴾ —→[ bind Rᴾ ] Nᴾ}
    {resultᴵ : E.EvalResult Nᴵ} {resultᴾ : E.EvalResult Nᴾ}
    {k : ℕ}
  → PairedReturns (pairedBindWorld W Rᴾ Rᴵ r)
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W r) p))
      k resultᴵ resultᴾ
  → PairedReturns W
      (PostBindValueRelation (paired-bind-step W r) p) k
      (prepend-result stepᴵ resultᴵ) (prepend-result stepᴾ resultᴾ)
paired-returns-bind-step {W = W} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {r = r} {stepᴵ = stepᴵ} {stepᴾ = stepᴾ}
    {resultᴵ = resultᴵ} {resultᴾ = resultᴾ}
    (paired-returns W′ bound≼W′ storeᴵ storeᴾ termsᴵ termsᴾ related) =
  paired-returns W′ W≼W′ storeᴵ storeᴾ termsᴵ′ termsᴾ′
    (bound≼W′ , refl , final-related)
  where
  step = paired-bind-step W r
  W≼W′ = future-trans step bound≼W′

  termsᴵ′ : ∀ M
    → E.changes (prepend-result stepᴵ resultᴵ) ▶ᵀ M
      ≡ liftImpreciseTerm W≼W′ M
  termsᴵ′ M = trans (termsᴵ (⇑ᵗᵐ M))
    (sym (liftImpreciseTerm-trans step bound≼W′ M))

  termsᴾ′ : ∀ M
    → E.changes (prepend-result stepᴾ resultᴾ) ▶ᵀ M
      ≡ liftPreciseTerm W≼W′ M
  termsᴾ′ M = trans (termsᴾ (⇑ᵗᵐ M))
    (sym (liftPreciseTerm-trans step bound≼W′ M))

  composite = liftCenterImprecision W≼W′ _
  sequential = liftCenterImprecision bound≼W′
    (liftCenterImprecision step _)
  final-related = ClosureProof.value-imprecision-reindex
    composite sequential
    (liftCenterTy-trans step bound≼W′ _)
    (liftCenterTy-trans step bound≼W′ _) related

related-paired-bind-step-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {Aᴾ Aᴵ : Ty Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Nᴵ : Term (suc Δᴵ)}
    {Mᴾ : Term Δᴾ} {Nᴾ : Term (suc Δᴾ)}
  → Mᴵ ≢ blame
  → Mᴾ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → E.value? Mᴾ ≡ nothing
  → (stepᴵ : Mᴵ —→[ bind Rᴵ ] Nᴵ)
  → (stepᴾ : Mᴾ —→[ bind Rᴾ ] Nᴾ)
  → E.step? (impreciseStore (core W)) Mᴵ ≡
      just (E.step-result (bind Rᴵ) Nᴵ stepᴵ)
  → E.step? (preciseStore (core W)) Mᴾ ≡
      just (E.step-result (bind Rᴾ) Nᴾ stepᴾ)
  → ComputationsRelated (pairedBindWorld W Rᴾ Rᴵ r)
      (FutureValueRelation
        (liftCenterImprecision (paired-bind-step W r) p)) k
      Nᴵ Nᴾ
  → ComputationsRelated W
      (PostBindValueRelation (paired-bind-step W r) p)
      (suc k) Mᴵ Mᴾ
related-paired-bind-step-expand {W = W} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {r = r} {p = p} {k = k}
    {Mᴵ = Mᴵ} {Nᴵ = Nᴵ} {Mᴾ = Mᴾ} {Nᴾ = Nᴾ}
    Mᴵ≢blame Mᴾ≢blame value-eqᴵ value-eqᴾ stepᴵ stepᴾ
    step-eqᴵ step-eqᴾ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  bound = pairedBindWorld W Rᴾ Rᴵ r

  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n ≤ suc k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
        interpretFrom (preciseStore (core W)) m Mᴾ ≡ returned resultᴾ
        × PairedReturns W
          (PostBindValueRelation (paired-bind-step W r) p)
          (suc k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = n} n≤sk result-eq
      with step-return-invert
        {Σ = impreciseStore (core W)} {n = n}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ result-eq
  forward {n = suc n} n≤sk result-eq
      | step-return resultᴵ′ returnᴵ resultᴵ-eq
      with forward-return related (≤-pred n≤sk) returnᴵ
  forward {n = suc n} n≤sk result-eq
      | step-return resultᴵ′ returnᴵ resultᴵ-eq
      | inj₁ (m , resultᴾ′ , returnᴾ , paired) =
    inj₁ (suc m , prepend-result stepᴾ resultᴾ′ ,
      step-return-expand {Σ = preciseStore (core W)} {gas = m}
        {M = Mᴾ} {N = Nᴾ} {χ = bind Rᴾ}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ ,
      paired-returns-reindex resultᴵ-eq refl
        (paired-returns-bind-step {r = r} paired))
  forward {n = suc n} n≤sk result-eq
      | step-return resultᴵ′ returnᴵ resultᴵ-eq
      | inj₂ (m , blameᴾ) =
    inj₂ (suc m , step-blame-expand {Σ = preciseStore (core W)}
      {gas = m} {M = Mᴾ} {N = Nᴾ} {χ = bind Rᴾ}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ blameᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n ≤ suc k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ ≡ returned resultᴵ
        × PairedReturns W
          (PostBindValueRelation (paired-bind-step W r) p)
          (suc k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤sk result-eq
      with step-return-invert
        {Σ = preciseStore (core W)} {n = n}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ result-eq
  backward {n = suc n} n≤sk result-eq
      | step-return resultᴾ′ returnᴾ resultᴾ-eq
      with backward-return related (≤-pred n≤sk) returnᴾ
  backward {n = suc n} n≤sk result-eq
      | step-return resultᴾ′ returnᴾ resultᴾ-eq
      | m , resultᴵ′ , returnᴵ , paired =
    suc m , prepend-result stepᴵ resultᴵ′ ,
    step-return-expand {Σ = impreciseStore (core W)} {gas = m}
      {M = Mᴵ} {N = Nᴵ} {χ = bind Rᴵ}
      Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ ,
    paired-returns-reindex refl resultᴾ-eq
      (paired-returns-bind-step {r = r} paired)

  blame-forward : ∀ {n}
    → n ≤ suc k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = n} n≤sk blameᴵ
      with step-blame-invert {Σ = impreciseStore (core W)} {n = n}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ blameᴵ
  blame-forward {n = suc n} n≤sk blameᴵ
      | step-blame contract-blameᴵ
      with forward-blame related (≤-pred n≤sk) contract-blameᴵ
  blame-forward {n = suc n} n≤sk blameᴵ
      | step-blame contract-blameᴵ | m , contract-blameᴾ =
    suc m , step-blame-expand {Σ = preciseStore (core W)}
      {gas = m} {M = Mᴾ} {N = Nᴾ} {χ = bind Rᴾ}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ contract-blameᴾ
