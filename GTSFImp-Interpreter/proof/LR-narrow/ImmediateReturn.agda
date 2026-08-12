module proof.LR-narrow.ImmediateReturn where

-- File Charter:
--   * Proves that evaluator values return immediately at every fuel index.
--   * Lifts pointwise related values to related computations.
--   * Contains the evaluator-specific inversion used by variable and constant
--     compatibility.

open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (m∸n≤m)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Types
open import TyStore
open import CastTerms
import Consistency
import Conversion
open import Reduction using ([]; ↠-refl)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation

inert-question-complete : ∀ {Δ} {μ : Consistency.Env∼ Δ}
    {A B : Ty Δ} {c : μ Consistency.⊢ A ∼ B}
  → Inert c
  → Σ[ inert ∈ Inert c ] E.inert? c ≡ just inert
inert-question-complete
    (inj {G = ★ ⇒ ★} ⦃ Gᵍ = ★⇒★ ⦄) = _ , refl
inert-question-complete (inj {G = ‵ ι} ⦃ Gᵍ = ‵ .ι ⦄) = _ , refl
inert-question-complete (inj {G = ＇ X} ⦃ Gᵍ = ＇ .X ⦄) = _ , refl
inert-question-complete (inj {G = `∀ ★} ⦃ Gᵍ = ∀★ ⦄) = _ , refl
inert-question-complete fun = _ , refl
inert-question-complete all = _ , refl
inert-question-complete (genᵥ A≠★ safe) = _ , refl

reveal-question-complete : ∀ {Δ A B} {c : Conversion.Conv↑ Δ A B}
  → RevealValue c
  → Σ[ reveal ∈ RevealValue c ] E.revealValue? c ≡ just reveal
reveal-question-complete fun = _ , refl
reveal-question-complete all = _ , refl

conceal-question-complete : ∀ {Δ A B} {c : Conversion.Conv↓ Δ A B}
  → ConcealValue c
  → Σ[ conceal ∈ ConcealValue c ] E.concealValue? c ≡ just conceal
conceal-question-complete seal = _ , refl
conceal-question-complete fun = _ , refl
conceal-question-complete all = _ , refl

value-question-complete : ∀ {Δ} {V : Term Δ}
  → Value V
  → Σ[ vV ∈ Value V ] E.value? V ≡ just vV
value-question-complete (ƛ N) = _ , refl
value-question-complete (Λ vV)
    with value-question-complete vV
value-question-complete (Λ vV) | vV′ , eq rewrite eq = _ , refl
value-question-complete ($ κ) = _ , refl
value-question-complete (vV 《 inert 》)
    with value-question-complete vV | inert-question-complete inert
value-question-complete (vV 《 inert 》)
    | vV′ , value-eq | inert′ , inert-eq
    rewrite value-eq | inert-eq = _ , refl
value-question-complete (vV ↑ reveal)
    with value-question-complete vV | reveal-question-complete reveal
value-question-complete (vV ↑ reveal)
    | vV′ , value-eq | reveal′ , reveal-eq
    rewrite value-eq | reveal-eq = _ , refl
value-question-complete (vV ↓ conceal)
    with value-question-complete vV | conceal-question-complete conceal
value-question-complete (vV ↓ conceal)
    | vV′ , value-eq | conceal′ , conceal-eq
    rewrite value-eq | conceal-eq = _ , refl

value-eval : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → (gas : ℕ)
  → Value V
  → Σ[ vV ∈ Value V ]
      E.evalFrom Σ gas V
        ≡ just (E.returned (E.result Δ [] V ↠-refl vV))
value-eval zero (ƛ N) = (ƛ N) , refl
value-eval zero (Λ vM) with value-question-complete vM
value-eval zero (Λ vM) | vM′ , eq rewrite eq = (Λ vM′) , refl
value-eval zero ($ κ) = ($ κ) , refl
value-eval zero (vM 《 inert 》)
    with value-question-complete vM | inert-question-complete inert
value-eval zero (vM 《 inert 》) | vM′ , value-eq | inert′ , inert-eq
    rewrite value-eq | inert-eq = (vM′ 《 inert′ 》) , refl
value-eval zero (vM ↑ reveal)
    with value-question-complete vM | reveal-question-complete reveal
value-eval zero (vM ↑ reveal) | vM′ , value-eq | reveal′ , reveal-eq
    rewrite value-eq | reveal-eq = (vM′ ↑ reveal′) , refl
value-eval zero (vM ↓ conceal)
    with value-question-complete vM | conceal-question-complete conceal
value-eval zero (vM ↓ conceal) | vM′ , value-eq | conceal′ , conceal-eq
    rewrite value-eq | conceal-eq = (vM′ ↓ conceal′) , refl
value-eval (suc gas) (ƛ N) = (ƛ N) , refl
value-eval (suc gas) (Λ vM) with value-question-complete vM
value-eval (suc gas) (Λ vM) | vM′ , eq rewrite eq = (Λ vM′) , refl
value-eval (suc gas) ($ κ) = ($ κ) , refl
value-eval (suc gas) (vM 《 inert 》)
    with value-question-complete vM | inert-question-complete inert
value-eval (suc gas) (vM 《 inert 》)
    | vM′ , value-eq | inert′ , inert-eq
    rewrite value-eq | inert-eq = (vM′ 《 inert′ 》) , refl
value-eval (suc gas) (vM ↑ reveal)
    with value-question-complete vM | reveal-question-complete reveal
value-eval (suc gas) (vM ↑ reveal)
    | vM′ , value-eq | reveal′ , reveal-eq
    rewrite value-eq | reveal-eq = (vM′ ↑ reveal′) , refl
value-eval (suc gas) (vM ↓ conceal)
    with value-question-complete vM | conceal-question-complete conceal
value-eval (suc gas) (vM ↓ conceal)
    | vM′ , value-eq | conceal′ , conceal-eq
    rewrite value-eq | conceal-eq = (vM′ ↓ conceal′) , refl

value-return : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
  → (gas : ℕ)
  → Value V
  → Σ[ vV ∈ Value V ]
      interpretFrom Σ gas V
        ≡ returned (E.result Δ [] V ↠-refl vV)
value-return {Σ = Σ} gas vV with value-eval {Σ = Σ} gas vV
value-return {Σ = Σ} gas vV | vV′ , eq rewrite eq = vV′ , refl

related-values-return : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → Value Vᴵ
  → Value Vᴾ
  → (∀ j → j ≤ k → R W future-refl j Vᴵ Vᴾ)
  → ComputationsRelated W R k Vᴵ Vᴾ
related-values-return {W = W} {R = R} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    vVᴵ vVᴾ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-impossible
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Vᴵ}
    → n ≤ k
    → interpretFrom (impreciseStore (core W)) n Vᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Vᴾ ]
          (interpretFrom (preciseStore (core W)) m Vᴾ
            ≡ returned resultᴾ)
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
      ⊎
      (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ)
  forward {n = n} n≤k result-eq
      with value-return {Σ = impreciseStore (core W)} n vVᴵ
         | value-return {Σ = preciseStore (core W)} zero vVᴾ
  forward {n = n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return
      with trans (sym imprecise-return) result-eq
  forward {n = n} n≤k result-eq
      | vVᴵ′ , imprecise-return | vVᴾ′ , precise-return | refl =
    inj₁ (zero , E.result _ [] Vᴾ ↠-refl vVᴾ′ , precise-return ,
      paired-returns W future-refl refl refl
        (related (k ∸ n) (m∸n≤m k n)))

  backward : ∀ {n} {resultᴾ : E.EvalResult Vᴾ}
    → n ≤ k
    → interpretFrom (preciseStore (core W)) n Vᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Vᴵ ]
        (interpretFrom (impreciseStore (core W)) m Vᴵ
          ≡ returned resultᴵ)
        × PairedReturns W R (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k result-eq
      with value-return {Σ = preciseStore (core W)} n vVᴾ
         | value-return {Σ = impreciseStore (core W)} zero vVᴵ
  backward {n = n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return
      with trans (sym precise-return) result-eq
  backward {n = n} n≤k result-eq
      | vVᴾ′ , precise-return | vVᴵ′ , imprecise-return | refl =
    zero , E.result _ [] Vᴵ ↠-refl vVᴵ′ , imprecise-return ,
    paired-returns W future-refl refl refl
      (related (k ∸ n) (m∸n≤m k n))

  blame-impossible : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W)) n Vᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Vᴾ
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , result-eq)
      with value-return {Σ = impreciseStore (core W)} n vVᴵ
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , result-eq)
      | vVᴵ′ , imprecise-return
      with trans (sym imprecise-return) result-eq
  blame-impossible {n = n} n≤k
      (Δ′ , changes , trace , result-eq)
      | vVᴵ′ , imprecise-return | ()
