module proof.LR-narrow.RevealSteps where

-- File Charter:
--   * Evaluator facts for reveal and conceal redexes on values: identity
--     conversions step away, an unseal cancels a matching seal, function
--     conversions are values and redistribute over application, and
--     universal conversions are values.
--   * Supplies the `value?` and `step?` equations consumed by the step
--     expansion lemmas of the logical relation.

open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Data.Nat using (suc)
open import Data.Fin.Properties using (_≟_)
open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _↦↓_; `∀↑_; `∀↓_; id↑; id↓)
open import Reduction
import Eval as E
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)

------------------------------------------------------------------------
-- Identity conversions
------------------------------------------------------------------------

reveal-id-value-none : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → Value V
  → E.value? (V ↑ id↑ A) ≡ nothing
reveal-id-value-none A vV with value-question-complete vV
reveal-id-value-none A vV | vV′ , value-eq rewrite value-eq = refl

conceal-id-value-none : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → Value V
  → E.value? (V ↓ id↓ A) ≡ nothing
conceal-id-value-none A vV with value-question-complete vV
conceal-id-value-none A vV | vV′ , value-eq rewrite value-eq = refl

-- Case analysis on the value constructors makes the final-step
-- dispatchers reduce past their blame clauses.

reveal-final-id-question : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.reveal-final? V (id↑ A) ≡
        just (E.step-result keep V (pure-step (id-reveal vV′)))
reveal-final-id-question A (ƛ N) = (ƛ N) , refl
reveal-final-id-question A (Λ vV)
    with value-question-complete (Λ vV)
reveal-final-id-question A (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
reveal-final-id-question A ($ κ) = ($ κ) , refl
reveal-final-id-question A (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
reveal-final-id-question A (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
reveal-final-id-question A (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
reveal-final-id-question A (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
reveal-final-id-question A (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
reveal-final-id-question A (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

conceal-final-id-question : ∀ {Δ} {V : Term Δ} (A : Ty Δ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.conceal-final? V (id↓ A) ≡
        just (E.step-result keep V (pure-step (id-conceal vV′)))
conceal-final-id-question A (ƛ N) = (ƛ N) , refl
conceal-final-id-question A (Λ vV)
    with value-question-complete (Λ vV)
conceal-final-id-question A (Λ vV) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
conceal-final-id-question A ($ κ) = ($ κ) , refl
conceal-final-id-question A (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
conceal-final-id-question A (vV 《 inert 》) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
conceal-final-id-question A (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
conceal-final-id-question A (vV ↑ reveal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl
conceal-final-id-question A (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
conceal-final-id-question A (vV ↓ conceal) | vV′ , value-eq
    rewrite value-eq = vV′ , refl

reveal-id-step-question : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    (A : Ty Δ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V ↑ id↑ A) ≡
        just (E.step-result keep V (pure-step (id-reveal vV′)))
reveal-id-step-question {Σ = Σ} {V = V} A vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
       | reveal-final-id-question A vV
reveal-id-step-question A vV
    | nothing | step-eq | vV′ , final-eq = vV′ , final-eq
reveal-id-step-question A vV | just step | () | _

conceal-id-step-question : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    (A : Ty Δ)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V ↓ id↓ A) ≡
        just (E.step-result keep V (pure-step (id-conceal vV′)))
conceal-id-step-question {Σ = Σ} {V = V} A vV
    with E.step? Σ V | value-step-none {Σ = Σ} vV
       | conceal-final-id-question A vV
conceal-id-step-question A vV
    | nothing | step-eq | vV′ , final-eq = vV′ , final-eq
conceal-id-step-question A vV | just step | () | _

------------------------------------------------------------------------
-- Sealing and unsealing
------------------------------------------------------------------------

sealed-value : ∀ {Δ} {U : Term Δ} (X : TyVar Δ) (R : Ty Δ)
  → (vU : Value U)
  → Σ[ vU′ ∈ Value U ]
      E.value? (U ↓ seal X R) ≡ just (vU′ ↓ seal)
sealed-value X R vU with value-question-complete vU
sealed-value X R vU | vU′ , value-eq rewrite value-eq = vU′ , refl

unseal-value-none : ∀ {Δ} {U : Term Δ} (X : TyVar Δ) (R : Ty Δ)
  → Value U
  → E.value? ((U ↓ seal X R) ↑ unseal X R) ≡ nothing
unseal-value-none X R vU with value-question-complete vU
unseal-value-none X R vU | vU′ , value-eq rewrite value-eq = refl

unseal-final-question : ∀ {Δ} {U : Term Δ}
    (X : TyVar Δ) (R : Ty Δ)
  → (vU : Value U)
  → Σ[ vU′ ∈ Value U ]
      E.reveal-final? (U ↓ seal X R) (unseal X R) ≡
        just (E.step-result keep U (pure-step (conceal-reveal vU′)))
unseal-final-question X R vU with sealed-value X R vU
unseal-final-question X R vU | vU′ , value-eq
    rewrite value-eq with X ≟ X
unseal-final-question X R vU | vU′ , value-eq | yes refl
    with R ≟Ty R
unseal-final-question X R vU | vU′ , value-eq | yes refl | yes refl =
  vU′ , refl
unseal-final-question X R vU | vU′ , value-eq | yes refl | no R≢R
    with R≢R refl
unseal-final-question X R vU | vU′ , value-eq | yes refl | no R≢R | ()
unseal-final-question X R vU | vU′ , value-eq | no X≢X with X≢X refl
unseal-final-question X R vU | vU′ , value-eq | no X≢X | ()

unseal-step-question : ∀ {Δ} {Σ : TyStore Δ} {U : Term Δ}
    (X : TyVar Δ) (R : Ty Δ)
  → (vU : Value U)
  → Σ[ vU′ ∈ Value U ]
      E.step? Σ ((U ↓ seal X R) ↑ unseal X R) ≡
        just (E.step-result keep U (pure-step (conceal-reveal vU′)))
unseal-step-question {Σ = Σ} {U = U} X R vU
    with E.step? Σ (U ↓ seal X R)
       | value-step-none {Σ = Σ} {V = U ↓ seal X R} (vU ↓ seal)
       | unseal-final-question X R vU
unseal-step-question X R vU
    | nothing | step-eq | vU′ , final-eq = vU′ , final-eq
unseal-step-question X R vU | just step | () | _

------------------------------------------------------------------------
-- Function conversions
------------------------------------------------------------------------

reveal-fun-value : ∀ {Δ} {V : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↓ Δ A′ A) (d : Conv↑ Δ B B′)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.value? (V ↑ (c ↦↑ d)) ≡ just (vV′ ↑ fun)
reveal-fun-value c d vV with value-question-complete vV
reveal-fun-value c d vV | vV′ , value-eq rewrite value-eq = vV′ , refl

conceal-fun-value : ∀ {Δ} {V : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↑ Δ A′ A) (d : Conv↓ Δ B B′)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.value? (V ↓ (c ↦↓ d)) ≡ just (vV′ ↓ fun)
conceal-fun-value c d vV with value-question-complete vV
conceal-fun-value c d vV | vV′ , value-eq rewrite value-eq = vV′ , refl

reveal-fun-app-value-none : ∀ {Δ} {V U : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↓ Δ A′ A) (d : Conv↑ Δ B B′)
  → E.value? ((V ↑ (c ↦↑ d)) · U) ≡ nothing
reveal-fun-app-value-none c d = refl

conceal-fun-app-value-none : ∀ {Δ} {V U : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↑ Δ A′ A) (d : Conv↓ Δ B B′)
  → E.value? ((V ↓ (c ↦↓ d)) · U) ≡ nothing
conceal-fun-app-value-none c d = refl

-- The argument's value constructor makes `app-value-final?` reduce past
-- its blame clause.

app-value-final-redex : ∀ {Δ} {L U : Term Δ}
  → (vL : Value L) (vU : Value U)
  → Σ[ vU′ ∈ Value U ]
      E.app-value-final? vL U ≡ E.app-redex? vL vU′
app-value-final-redex vL (ƛ N) = (ƛ N) , refl
app-value-final-redex vL (Λ vU)
    with value-question-complete (Λ vU)
app-value-final-redex vL (Λ vU) | vU′ , value-eq
    rewrite value-eq = vU′ , refl
app-value-final-redex vL ($ κ) = ($ κ) , refl
app-value-final-redex vL (vU 《 inert 》)
    with value-question-complete (vU 《 inert 》)
app-value-final-redex vL (vU 《 inert 》) | vU′ , value-eq
    rewrite value-eq = vU′ , refl
app-value-final-redex vL (vU ↑ reveal)
    with value-question-complete (vU ↑ reveal)
app-value-final-redex vL (vU ↑ reveal) | vU′ , value-eq
    rewrite value-eq = vU′ , refl
app-value-final-redex vL (vU ↓ conceal)
    with value-question-complete (vU ↓ conceal)
app-value-final-redex vL (vU ↓ conceal) | vU′ , value-eq
    rewrite value-eq = vU′ , refl

reveal-fun-app-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V U : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↓ Δ A′ A) (d : Conv↑ Δ B B′)
  → (vV : Value V) (vU : Value U)
  → Σ[ vV′ ∈ Value V ] Σ[ vU′ ∈ Value U ]
      E.step? Σ ((V ↑ (c ↦↑ d)) · U) ≡
        just (E.step-result keep ((V · (U ↓ c)) ↑ d)
          (pure-step (β-reveal-⇒ vV′ vU′)))
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    with E.step? Σ (V ↑ (c ↦↑ d))
       | value-step-none {Σ = Σ} {V = V ↑ (c ↦↑ d)} (vV ↑ fun)
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | just _ | ()
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _
    with E.step? Σ U | value-step-none {Σ = Σ} vU
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | just _ | ()
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | nothing | _
    with reveal-fun-value c d vV
reveal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | nothing | _ | vV′ , eqV
    rewrite eqV with app-value-final-redex (vV′ ↑ fun) vU
reveal-fun-app-step-question c d vV vU
    | nothing | _ | nothing | _ | vV′ , eqV | vU′ , final-eq =
  vV′ , vU′ , final-eq

conceal-fun-app-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V U : Term Δ} {A A′ B B′ : Ty Δ}
    (c : Conv↑ Δ A′ A) (d : Conv↓ Δ B B′)
  → (vV : Value V) (vU : Value U)
  → Σ[ vV′ ∈ Value V ] Σ[ vU′ ∈ Value U ]
      E.step? Σ ((V ↓ (c ↦↓ d)) · U) ≡
        just (E.step-result keep ((V · (U ↑ c)) ↓ d)
          (pure-step (β-conceal-⇒ vV′ vU′)))
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    with E.step? Σ (V ↓ (c ↦↓ d))
       | value-step-none {Σ = Σ} {V = V ↓ (c ↦↓ d)} (vV ↓ fun)
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | just _ | ()
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _
    with E.step? Σ U | value-step-none {Σ = Σ} vU
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | just _ | ()
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | nothing | _
    with conceal-fun-value c d vV
conceal-fun-app-step-question {Σ = Σ} {V = V} {U = U} c d vV vU
    | nothing | _ | nothing | _ | vV′ , eqV
    rewrite eqV with app-value-final-redex (vV′ ↓ fun) vU
conceal-fun-app-step-question c d vV vU
    | nothing | _ | nothing | _ | vV′ , eqV | vU′ , final-eq =
  vV′ , vU′ , final-eq

------------------------------------------------------------------------
-- Universal conversions
------------------------------------------------------------------------

reveal-all-value : ∀ {Δ} {V : Term Δ} {A B : Ty (suc Δ)}
    (c : Conv↑ (suc Δ) A B)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.value? (V ↑ `∀↑ c) ≡ just (vV′ ↑ all)
reveal-all-value c vV with value-question-complete vV
reveal-all-value c vV | vV′ , value-eq rewrite value-eq = vV′ , refl

conceal-all-value : ∀ {Δ} {V : Term Δ} {A B : Ty (suc Δ)}
    (c : Conv↓ (suc Δ) A B)
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.value? (V ↓ `∀↓ c) ≡ just (vV′ ↓ all)
conceal-all-value c vV with value-question-complete vV
conceal-all-value c vV | vV′ , value-eq rewrite value-eq = vV′ , refl
