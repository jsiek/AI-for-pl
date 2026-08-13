module proof.LR-narrow.BetaExpansion where

-- File Charter:
--   * Relates evaluation of a beta redex to evaluation of its contractum.
--   * Lifts related computations across one matching beta step.
--   * Accounts explicitly for the single unit of fuel and LR index consumed.

open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)

value-no-step : ∀ {Δ Δ′} {χ : StoreChange Δ Δ′}
    {V : Term Δ} {N : Term Δ′}
  → Value V
  → V —→[ χ ] N
  → ⊥
value-no-step (ƛ N) (pure-step ())
value-no-step (Λ vV) (pure-step ())
value-no-step ($ k) (pure-step ())
value-no-step (vV 《 inj 》) (pure-step (ground x x₁)) = x₁ refl
value-no-step (() 《 fun 》) (pure-step blame-⟨⟩)
value-no-step (() 《 all 》) (pure-step blame-⟨⟩)
value-no-step (() 《 genᵥ A≢★ x 》) (pure-step blame-⟨⟩)
value-no-step (vV 《 x 》) (ξ-⟨⟩ step x₁) = value-no-step vV step
value-no-step (() ↑ fun) (pure-step blame-reveal)
value-no-step (() ↑ all) (pure-step blame-reveal)
value-no-step (vV ↑ x) (ξ-reveal step x₁) = value-no-step vV step
value-no-step (() ↓ seal) (pure-step blame-conceal)
value-no-step (() ↓ fun) (pure-step blame-conceal)
value-no-step (() ↓ all) (pure-step blame-conceal)
value-no-step (vV ↓ x) (ξ-conceal step x₁) = value-no-step vV step

value-step-none : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → Value V
  → E.step? Σ V ≡ nothing
value-step-none {Δ} {Σ} {V} vV with E.step? Σ V
value-step-none vV | nothing = refl
value-step-none vV | just (E.step-result χ N step) =
  ⊥-elim (value-no-step vV step)

beta-app-value-final-question : ∀ {Δ} {N V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.app-value-final? (ƛ N) V ≡
        just (E.step-result keep (N [ V ]) (pure-step (β vV)))
beta-app-value-final-question (ƛ M) = (ƛ M) , refl
beta-app-value-final-question (Λ vV)
    with value-question-complete (Λ vV)
beta-app-value-final-question (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
beta-app-value-final-question ($ κ) = ($ κ) , refl
beta-app-value-final-question (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
beta-app-value-final-question (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
beta-app-value-final-question (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
beta-app-value-final-question (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
beta-app-value-final-question (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
beta-app-value-final-question (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

beta-app-final-question : ∀ {Δ} {N V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.app-final? (ƛ N) V ≡
        just (E.step-result keep (N [ V ]) (pure-step (β vV)))
beta-app-final-question vV = beta-app-value-final-question vV

beta-step-question : ∀ {Δ} {Σ : TyStore Δ} {N V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.step? Σ ((ƛ N) · V) ≡
        just (E.step-result keep (N [ V ]) (pure-step (β vV)))
beta-step-question {Δ} {Σ} {N} {V} vV
    with E.step? Σ V | value-step-none {Δ} {Σ} {V} vV
       | beta-app-final-question vV
beta-step-question {Δ} {Σ} {N} {V} vV
    | nothing | step-eq | vV′ , app-eq
    = vV′ , app-eq
beta-step-question {Δ} {Σ} {N} {V} vV
    | just step | () | app-complete

prepend-beta-result : ∀ {Δ} {N V : Term Δ}
  → Value V
  → E.EvalResult (N [ V ])
  → E.EvalResult ((ƛ N) · V)
prepend-beta-result vV (E.result Δ′ changes U trace vU) =
  E.result Δ′ (keep ∷ changes) U
    (↠-step (pure-step (β vV)) trace) vU

prepend-beta-blame : ∀ {Δ Δ′} {N V : Term Δ}
  → Value V
  → (changes : StoreChanges Δ Δ′)
  → N [ V ] —↠[ changes ] blame
  → (ƛ N) · V —↠[ keep ∷ changes ] blame
prepend-beta-blame vV changes trace =
  ↠-step (pure-step (β vV)) trace

prepend-beta-outcome : ∀ {Δ} {N V : Term Δ}
  → Value V
  → E.EvalOutcome (N [ V ])
  → E.EvalOutcome ((ƛ N) · V)
prepend-beta-outcome vV (E.returned eval-result) =
  E.returned (prepend-beta-result vV eval-result)
prepend-beta-outcome vV (E.blamed changes trace) =
  E.blamed (keep ∷ changes) (prepend-beta-blame vV changes trace)

beta-eval-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {N V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.evalFrom Σ (suc gas) ((ƛ N) · V) ≡
        Maybe.map (prepend-beta-outcome vV)
          (E.evalFrom Σ gas (N [ V ]))
beta-eval-from {Δ} {Σ} {gas} {N} {V} vV
    with beta-step-question {Δ} {Σ} {N} {V} vV
beta-eval-from {Δ} {Σ} {gas} {N} {V} vV | vV′ , step-eq
    rewrite step-eq with E.evalFrom Σ gas (N [ V ])
beta-eval-from vV | vV′ , step-eq | nothing = vV′ , refl
beta-eval-from vV
    | vV′ , step-eq | just (E.returned eval-result) = vV′ , refl
beta-eval-from vV
    | vV′ , step-eq | just (E.blamed changes trace) = vV′ , refl

prepend-beta-interpreter-outcome : ∀ {Δ} {N V : Term Δ}
  → Value V
  → Outcome (N [ V ])
  → Outcome ((ƛ N) · V)
prepend-beta-interpreter-outcome vV timed = timed
prepend-beta-interpreter-outcome vV (returned eval-result) =
  returned (prepend-beta-result vV eval-result)
prepend-beta-interpreter-outcome vV (blamed changes trace) =
  blamed (keep ∷ changes) (prepend-beta-blame vV changes trace)

interpreter-outcome : ∀ {Δ} {M : Term Δ}
  → Maybe.Maybe (E.EvalOutcome M)
  → Outcome M
interpreter-outcome nothing = timed
interpreter-outcome (just (E.returned eval-result)) =
  returned eval-result
interpreter-outcome (just (E.blamed changes trace)) =
  blamed changes trace

interpret-from-eval : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ}
  → interpretFrom Σ gas M ≡ interpreter-outcome (E.evalFrom Σ gas M)
interpret-from-eval {Σ = Σ} {gas} {M} with E.evalFrom Σ gas M
interpret-from-eval | nothing = refl
interpret-from-eval | just (E.returned eval-result) = refl
interpret-from-eval | just (E.blamed changes trace) = refl

interpreter-prepend-map : ∀ {Δ} {N V : Term Δ}
  → (vV : Value V)
  → (outcome : Maybe.Maybe (E.EvalOutcome (N [ V ])))
  → interpreter-outcome
      (Maybe.map (prepend-beta-outcome {Δ} {N} {V} vV) outcome)
      ≡ prepend-beta-interpreter-outcome {Δ} {N} {V} vV
          (interpreter-outcome outcome)
interpreter-prepend-map {Δ} {N} {V} vV nothing = refl
interpreter-prepend-map {Δ} {N} {V} vV
    (just (E.returned eval-result)) = refl
interpreter-prepend-map {Δ} {N} {V} vV
    (just (E.blamed changes trace)) = refl

beta-interpret-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {N V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ]
      interpretFrom Σ (suc gas) ((ƛ N) · V) ≡
        prepend-beta-interpreter-outcome vV
          (interpretFrom Σ gas (N [ V ]))
beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV
    with beta-eval-from {Δ} {Σ} {gas} {N} {V} vV
beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV | vV′ , eval-eq =
  vV′ , trans
    (interpret-from-eval {Δ} {Σ} {suc gas} {((ƛ N) · V)})
    (trans (cong (interpreter-outcome {M = (ƛ N) · V}) eval-eq)
      (trans (interpreter-prepend-map {Δ} {N} {V} vV′
               (E.evalFrom Σ gas (N [ V ])))
        (cong (prepend-beta-interpreter-outcome {Δ} {N} {V} vV′)
          (sym (interpret-from-eval {Δ} {Σ} {gas} {(N [ V ])})))))

beta-return-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {N V : Term Δ} {contract-result : E.EvalResult (N [ V ])}
  → (vV : Value V)
  → interpretFrom Σ gas (N [ V ]) ≡ returned contract-result
  → Σ[ vV′ ∈ Value V ]
      interpretFrom Σ (suc gas) ((ƛ N) · V) ≡
        returned (prepend-beta-result vV′ contract-result)
beta-return-expand {Δ} {Σ} {gas} {N} {V} vV contract-eq
    with beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV
beta-return-expand {Δ} {Σ} {gas} {N} {V} vV contract-eq
    | vV′ , beta-eq =
  vV′ , trans beta-eq
    (cong (prepend-beta-interpreter-outcome {Δ} {N} {V} vV′)
      contract-eq)

beta-return-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {N V : Term Δ} {redex-result : E.EvalResult ((ƛ N) · V)}
  → (vV : Value V)
  → interpretFrom Σ n ((ƛ N) · V) ≡ returned redex-result
  → Σ[ gas ∈ ℕ ]
      n ≡ suc gas ×
      Σ[ vV′ ∈ Value V ]
      Σ[ contract-result ∈ E.EvalResult (N [ V ]) ]
        interpretFrom Σ gas (N [ V ]) ≡ returned contract-result
        × redex-result ≡ prepend-beta-result vV′ contract-result
beta-return-invert {n = zero} vV ()
beta-return-invert {Δ} {Σ} {n = suc gas} {N} {V} vV redex-eq
    with interpretFrom Σ gas (N [ V ]) in contract-eq
       | beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV
beta-return-invert vV redex-eq | timed | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
beta-return-invert vV redex-eq | timed | vV′ , beta-eq | ()
beta-return-invert vV redex-eq | returned contract-result
    | vV′ , beta-eq with trans (sym beta-eq) redex-eq
beta-return-invert vV redex-eq | returned contract-result
    | vV′ , beta-eq | refl =
  _ , refl , vV′ , contract-result , contract-eq , refl
beta-return-invert vV redex-eq | blamed changes trace | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
beta-return-invert vV redex-eq
    | blamed changes trace | vV′ , beta-eq | ()

beta-blame-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {N V : Term Δ}
  → (vV : Value V)
  → BlamesFrom Σ gas (N [ V ])
  → BlamesFrom Σ (suc gas) ((ƛ N) · V)
beta-blame-expand {Δ} {Σ} {gas} {N} {V} vV
    (Δ′ , changes , trace , contract-eq)
    with beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV
beta-blame-expand {Δ} {Σ} {gas} {N} {V} vV
    (Δ′ , changes , trace , contract-eq) | vV′ , beta-eq =
  Δ′ , keep ∷ changes , prepend-beta-blame vV′ changes trace ,
  trans beta-eq
    (cong (prepend-beta-interpreter-outcome {Δ} {N} {V} vV′)
      contract-eq)

beta-blame-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {N V : Term Δ}
  → Value V
  → BlamesFrom Σ n ((ƛ N) · V)
  → Σ[ gas ∈ ℕ ] n ≡ suc gas × BlamesFrom Σ gas (N [ V ])
beta-blame-invert {n = zero} vV (Δ′ , changes , trace , ())
beta-blame-invert {Δ} {Σ} {n = suc gas} {N} {V} vV
    (Δ′ , changes , trace , redex-eq)
    with interpretFrom Σ gas (N [ V ]) in contract-eq
       | beta-interpret-from {Δ} {Σ} {gas} {N} {V} vV
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | timed | vV′ , beta-eq with trans (sym beta-eq) redex-eq
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | timed | vV′ , beta-eq | ()
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | returned contract-result | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | returned contract-result | vV′ , beta-eq | ()
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | blamed contract-changes contract-trace | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | blamed contract-changes contract-trace | vV′ , beta-eq | refl =
  _ , refl , _ , contract-changes , contract-trace , contract-eq

paired-returns-beta : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Nᴵ Vᴵ : Term Δᴵ} {Nᴾ Vᴾ : Term Δᴾ}
    {resultᴵ : E.EvalResult (Nᴵ [ Vᴵ ])}
    {resultᴾ : E.EvalResult (Nᴾ [ Vᴾ ])}
  → (vVᴵ : Value Vᴵ)
  → (vVᴾ : Value Vᴾ)
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W R k
      (prepend-beta-result {Δᴵ} {Nᴵ} {Vᴵ} vVᴵ resultᴵ)
      (prepend-beta-result {Δᴾ} {Nᴾ} {Vᴾ} vVᴾ resultᴾ)
paired-returns-beta {Δᴾ} {Δᴵ} {Δᶜ} {W} {R} {k}
    {Nᴵ} {Vᴵ} {Nᴾ} {Vᴾ} vVᴵ vVᴾ
    (paired-returns W′ W≼W′ imprecise-eq precise-eq related) =
  paired-returns W′ W≼W′ imprecise-eq precise-eq related

related-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Nᴵ Vᴵ : Term Δᴵ} {Nᴾ Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → Value Vᴾ
  → ComputationsRelated W R k (Nᴵ [ Vᴵ ]) (Nᴾ [ Vᴾ ])
  → ComputationsRelated W R (suc k)
      ((ƛ Nᴵ) · Vᴵ) ((ƛ Nᴾ) · Vᴾ)
related-beta-expand {Δᴾ} {Δᴵ} {Δᶜ} {W = W} {R} {k}
    {Nᴵ} {Vᴵ} {Nᴾ} {Vᴾ}
    vVᴵ vVᴾ contract-related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forwardBlame
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult ((ƛ Nᴵ) · Vᴵ)}
    → n ≤ suc k
    → interpretFrom (impreciseStore (core W)) n ((ƛ Nᴵ) · Vᴵ)
        ≡ returned resultᴵ
    →
      (Σ[ m ∈ ℕ ]
       Σ[ resultᴾ ∈ E.EvalResult ((ƛ Nᴾ) · Vᴾ) ]
         interpretFrom (preciseStore (core W)) m ((ƛ Nᴾ) · Vᴾ)
           ≡ returned resultᴾ
         × PairedReturns W R (suc k ∸ n) resultᴵ resultᴾ)
      ⊎
      (Σ[ m ∈ ℕ ]
        BlamesFrom (preciseStore (core W)) m ((ƛ Nᴾ) · Vᴾ))
  forward {n} n≤sk result-eq
      with beta-return-invert {Δᴵ} {impreciseStore (core W)} {n}
        {Nᴵ} {Vᴵ} vVᴵ result-eq
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      with forward-return contract-related (≤-pred n≤sk) contract-eqᴵ
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₁ (m , contract-resultᴾ , contract-eqᴾ , paired)
      with beta-return-expand {Δᴾ} {preciseStore (core W)} {m}
        {Nᴾ} {Vᴾ} vVᴾ contract-eqᴾ
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₁ (m , contract-resultᴾ , contract-eqᴾ , paired)
      | vVᴾ′ , redex-eqᴾ =
    inj₁ (suc m , prepend-beta-result vVᴾ′ contract-resultᴾ ,
      redex-eqᴾ , paired-returns-beta {Nᴵ = Nᴵ} {Vᴵ}
        {Nᴾ} {Vᴾ} vVᴵ′ vVᴾ′ paired)
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₂ (m , contract-blameᴾ) =
    inj₂ (suc m , beta-blame-expand {Δᴾ} {preciseStore (core W)} {m}
      {Nᴾ} {Vᴾ} vVᴾ contract-blameᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult ((ƛ Nᴾ) · Vᴾ)}
    → n ≤ suc k
    → interpretFrom (preciseStore (core W)) n ((ƛ Nᴾ) · Vᴾ)
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ]
      Σ[ resultᴵ ∈ E.EvalResult ((ƛ Nᴵ) · Vᴵ) ]
        interpretFrom (impreciseStore (core W)) m ((ƛ Nᴵ) · Vᴵ)
          ≡ returned resultᴵ
        × PairedReturns W R (suc k ∸ n) resultᴵ resultᴾ
  backward {n} n≤sk result-eq
      with beta-return-invert {Δᴾ} {preciseStore (core W)} {n}
        {Nᴾ} {Vᴾ} vVᴾ result-eq
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      with backward-return contract-related (≤-pred n≤sk) contract-eqᴾ
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      | m , contract-resultᴵ , contract-eqᴵ , paired
      with beta-return-expand {Δᴵ} {impreciseStore (core W)} {m}
        {Nᴵ} {Vᴵ} vVᴵ contract-eqᴵ
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      | m , contract-resultᴵ , contract-eqᴵ , paired
      | vVᴵ′ , redex-eqᴵ =
    suc m , prepend-beta-result vVᴵ′ contract-resultᴵ , redex-eqᴵ ,
    paired-returns-beta {Nᴵ = Nᴵ} {Vᴵ} {Nᴾ} {Vᴾ}
      vVᴵ′ vVᴾ′ paired

  forwardBlame : ∀ {n}
    → n ≤ suc k
    → BlamesFrom (impreciseStore (core W)) n ((ƛ Nᴵ) · Vᴵ)
    → Σ[ m ∈ ℕ ]
        BlamesFrom (preciseStore (core W)) m ((ƛ Nᴾ) · Vᴾ)
  forwardBlame {n} n≤sk redex-blameᴵ
      with beta-blame-invert {Δᴵ} {impreciseStore (core W)} {n}
        {Nᴵ} {Vᴵ} vVᴵ redex-blameᴵ
  forwardBlame {n} n≤sk redex-blameᴵ
      | gas , refl , contract-blameᴵ
      with forward-blame contract-related (≤-pred n≤sk) contract-blameᴵ
  forwardBlame {n} n≤sk redex-blameᴵ
      | gas , refl , contract-blameᴵ | m , contract-blameᴾ =
    suc m , beta-blame-expand {Δᴾ} {preciseStore (core W)} {m}
      {Nᴾ} {Vᴾ} vVᴾ contract-blameᴾ
