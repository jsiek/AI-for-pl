module proof.LR-narrow.TypeBetaExpansion where

-- File Charter:
--   * Expands related computations across matching type-beta allocation steps.
--   * Prefixes evaluator results and blame traces with the two bind steps.
--   * Reassembles the post-allocation LR world into the pre-step observation.

open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_)
open import Data.Nat.Properties using (≤-pred)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import TyStore
open import Conversion using (〖_,_↑_〗)
open import CastTerms
import Imprecision as I
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)

empty-paired-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
  → SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Fin.zero
empty-paired-atom W Aᴾ Aᴵ =
  semantic-atom Fin.zero Fin.zero refl refl
    (λ k Vᴵ Vᴾ → ⊥) (λ ()) (λ ())

paired-step : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    (p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ)
    (fresh : SemanticAtom (pairedBindCore (core W) Aᴾ Aᴵ) Fin.zero)
  → Future W (pairedBindWorld W Aᴾ Aᴵ fresh)
paired-step W p fresh = future-paired (future-refl {W = W}) p fresh

type-beta-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.step? Σ ((Λ V) ⦂∀ B [ A ]) ≡
        just (E.step-result (bind A)
          (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) (β-Λ vV))
type-beta-step-question {Σ = Σ} {A} {B} {V} vV
    with value-question-complete vV
type-beta-step-question {Σ = Σ} {A} {B} {V} vV
    | vV′ , value-eq rewrite value-eq = vV′ , refl

prepend-type-beta-result : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)}
  → Value V
  → E.EvalResult (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
  → E.EvalResult ((Λ V) ⦂∀ B [ A ])
prepend-type-beta-result vV (E.result Δ′ changes U trace vU) =
  E.result Δ′ (bind _ ∷ changes) U
    (↠-step (β-Λ vV) trace) vU

prepend-type-beta-blame : ∀ {Δ Δ′} {A : Ty Δ}
    {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → (changes : StoreChanges (suc Δ) Δ′)
  → V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗 —↠[ changes ] blame
  → (Λ V) ⦂∀ B [ A ] —↠[ bind A ∷ changes ] blame
prepend-type-beta-blame vV changes trace = ↠-step (β-Λ vV) trace

prepend-type-beta-outcome : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)}
  → Value V
  → E.EvalOutcome (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
  → E.EvalOutcome ((Λ V) ⦂∀ B [ A ])
prepend-type-beta-outcome vV (E.returned eval-result) =
  E.returned (prepend-type-beta-result vV eval-result)
prepend-type-beta-outcome vV (E.blamed changes trace) =
  E.blamed (bind _ ∷ changes)
    (prepend-type-beta-blame vV changes trace)

prepend-type-beta-interpreter-outcome : ∀ {Δ} {A : Ty Δ}
    {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → Outcome (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
  → Outcome ((Λ V) ⦂∀ B [ A ])
prepend-type-beta-interpreter-outcome vV timed = timed
prepend-type-beta-interpreter-outcome vV (returned eval-result) =
  returned (prepend-type-beta-result vV eval-result)
prepend-type-beta-interpreter-outcome vV (blamed changes trace) =
  blamed (bind _ ∷ changes) (prepend-type-beta-blame vV changes trace)

interpreter-outcome : ∀ {Δ} {M : Term Δ}
  → Maybe.Maybe (E.EvalOutcome M)
  → Outcome M
interpreter-outcome nothing = timed
interpreter-outcome (just (E.returned eval-result)) = returned eval-result
interpreter-outcome (just (E.blamed changes trace)) =
  blamed changes trace

interpret-from-eval : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ}
  → interpretFrom Σ gas M ≡ interpreter-outcome (E.evalFrom Σ gas M)
interpret-from-eval {Σ = Σ} {gas} {M} with E.evalFrom Σ gas M
interpret-from-eval | nothing = refl
interpret-from-eval | just (E.returned eval-result) = refl
interpret-from-eval | just (E.blamed changes trace) = refl

type-beta-eval-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → Σ[ vV ∈ Value V ]
      E.evalFrom Σ (suc gas) ((Λ V) ⦂∀ B [ A ]) ≡
        Maybe.map (prepend-type-beta-outcome vV)
          (E.evalFrom (store-bind Σ A) gas
            (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗))
type-beta-eval-from {Σ = Σ} {gas} {A} {B} {V} vV
    with type-beta-step-question {Σ = Σ} {A} {B} {V} vV
type-beta-eval-from {Σ = Σ} {gas} {A} {B} {V} vV
    | vV′ , step-eq rewrite step-eq
    with E.evalFrom (store-bind Σ A) gas
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
type-beta-eval-from vV | vV′ , step-eq | nothing = vV′ , refl
type-beta-eval-from vV | vV′ , step-eq
    | just (E.returned eval-result) = vV′ , refl
type-beta-eval-from vV | vV′ , step-eq
    | just (E.blamed changes trace) = vV′ , refl

interpreter-prepend-map : ∀ {Δ} {A : Ty Δ} {B : Ty (suc Δ)}
    {V : Term (suc Δ)}
  → (vV : Value V)
  → (outcome : Maybe.Maybe
      (E.EvalOutcome (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)))
  → interpreter-outcome
      (Maybe.map (prepend-type-beta-outcome vV) outcome)
      ≡ prepend-type-beta-interpreter-outcome vV
          (interpreter-outcome outcome)
interpreter-prepend-map vV nothing = refl
interpreter-prepend-map vV (just (E.returned eval-result)) = refl
interpreter-prepend-map vV (just (E.blamed changes trace)) = refl

type-beta-interpret-from : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → Σ[ vV ∈ Value V ]
      interpretFrom Σ (suc gas) ((Λ V) ⦂∀ B [ A ]) ≡
        prepend-type-beta-interpreter-outcome vV
          (interpretFrom (store-bind Σ A) gas
            (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗))
type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
    with type-beta-eval-from {Σ = Σ} {gas} {A} {B} {V} vV
type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
    | vV′ , eval-eq = vV′ , trans
      (interpret-from-eval {Σ = Σ} {suc gas}
        {((Λ V) ⦂∀ B [ A ])})
      (trans (cong interpreter-outcome eval-eq)
        (trans (interpreter-prepend-map vV′
          (E.evalFrom (store-bind Σ A) gas
            (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)))
          (cong (prepend-type-beta-interpreter-outcome vV′)
            (sym (interpret-from-eval {Σ = store-bind Σ A} {gas}
              {(V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)})))))

type-beta-return-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
    {contract-result : E.EvalResult
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)}
  → (vV : Value V)
  → interpretFrom (store-bind Σ A) gas
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ≡ returned contract-result
  → Σ[ vV′ ∈ Value V ]
      interpretFrom Σ (suc gas) ((Λ V) ⦂∀ B [ A ]) ≡
        returned (prepend-type-beta-result vV′ contract-result)
type-beta-return-expand {Σ = Σ} {gas} {A} {B} {V} vV contract-eq
    with type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
type-beta-return-expand vV contract-eq | vV′ , beta-eq =
  vV′ , trans beta-eq
    (cong (prepend-type-beta-interpreter-outcome vV′) contract-eq)

type-beta-return-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
    {redex-result : E.EvalResult ((Λ V) ⦂∀ B [ A ])}
  → (vV : Value V)
  → interpretFrom Σ n ((Λ V) ⦂∀ B [ A ]) ≡ returned redex-result
  → Σ[ gas ∈ ℕ ] n ≡ suc gas ×
      Σ[ vV′ ∈ Value V ]
      Σ[ contract-result ∈ E.EvalResult
        (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ]
        interpretFrom (store-bind Σ A) gas
          (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) ≡ returned contract-result
        × redex-result ≡ prepend-type-beta-result vV′ contract-result
type-beta-return-invert {n = zero} vV ()
type-beta-return-invert {Σ = Σ} {n = suc gas} {A} {B} {V}
    vV redex-eq
    with interpretFrom (store-bind Σ A) gas
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) in contract-eq
       | type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
type-beta-return-invert vV redex-eq
    | timed | vV′ , beta-eq with trans (sym beta-eq) redex-eq
type-beta-return-invert vV redex-eq
    | timed | vV′ , beta-eq | ()
type-beta-return-invert vV redex-eq
    | returned contract-result | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
type-beta-return-invert vV redex-eq
    | returned contract-result | vV′ , beta-eq | refl =
  _ , refl , vV′ , contract-result , contract-eq , refl
type-beta-return-invert vV redex-eq
    | blamed changes trace | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
type-beta-return-invert vV redex-eq
    | blamed changes trace | vV′ , beta-eq | ()

type-beta-blame-expand : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → (vV : Value V)
  → BlamesFrom (store-bind Σ A) gas
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
  → BlamesFrom Σ (suc gas) ((Λ V) ⦂∀ B [ A ])
type-beta-blame-expand {Σ = Σ} {gas} {A} {B} {V} vV
    (Δ′ , changes , trace , contract-eq)
    with type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
type-beta-blame-expand vV (Δ′ , changes , trace , contract-eq)
    | vV′ , beta-eq =
  Δ′ , bind _ ∷ changes , prepend-type-beta-blame vV′ changes trace ,
  trans beta-eq
    (cong (prepend-type-beta-interpreter-outcome vV′) contract-eq)

type-beta-blame-invert : ∀ {Δ} {Σ : TyStore Δ} {n : ℕ}
    {A : Ty Δ} {B : Ty (suc Δ)} {V : Term (suc Δ)}
  → Value V
  → BlamesFrom Σ n ((Λ V) ⦂∀ B [ A ])
  → Σ[ gas ∈ ℕ ] n ≡ suc gas ×
      BlamesFrom (store-bind Σ A) gas
        (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗)
type-beta-blame-invert {n = zero} vV (Δ′ , changes , trace , ())
type-beta-blame-invert {Σ = Σ} {n = suc gas} {A} {B} {V} vV
    (Δ′ , changes , trace , redex-eq)
    with interpretFrom (store-bind Σ A) gas
      (V ↑ 〖 Fin.zero , ⇑ᵗ A ↑ B 〗) in contract-eq
       | type-beta-interpret-from {Σ = Σ} {gas} {A} {B} {V} vV
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | timed | vV′ , beta-eq with trans (sym beta-eq) redex-eq
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | timed | vV′ , beta-eq | ()
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | returned eval-result | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | returned eval-result | vV′ , beta-eq | ()
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | blamed contract-changes contract-trace | vV′ , beta-eq
    with trans (sym beta-eq) redex-eq
type-beta-blame-invert vV (Δ′ , changes , trace , redex-eq)
    | blamed contract-changes contract-trace | vV′ , beta-eq | refl =
  _ , refl , _ , contract-changes , contract-trace , contract-eq

paired-returns-type-beta : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {fresh : SemanticAtom (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)} {k : ℕ}
    {resultᴵ : E.EvalResult
      (Vᴵ ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ Bᴵ 〗)}
    {resultᴾ : E.EvalResult
      (Vᴾ ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴾ 〗)}
  → (vVᴵ : Value Vᴵ)
  → (vVᴾ : Value Vᴾ)
  → PairedReturns (pairedBindWorld W Rᴾ Rᴵ fresh)
      (FutureValueRelation
        (liftCenterImprecision (paired-step W r fresh) p))
      k resultᴵ resultᴾ
  → PairedReturns W (FutureValueRelation p) k
      (prepend-type-beta-result vVᴵ resultᴵ)
      (prepend-type-beta-result vVᴾ resultᴾ)
paired-returns-type-beta {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {W = W} {p = p}
    {Rᴾ} {Rᴵ} {r} {fresh}
    {Bᴾ} {Bᴵ} {Vᴾ} {Vᴵ} {resultᴵ = resultᴵ}
    {resultᴾ = resultᴾ} vVᴵ vVᴾ
    (paired-returns W′ bound≼W′ imprecise-store precise-store
      imprecise-terms precise-terms related) =
  paired-returns W′ W≼W′ imprecise-store precise-store
    imprecise-terms′ precise-terms′ related′
  where
  step = paired-step W r fresh
  W≼W′ = future-trans step bound≼W′

  imprecise-terms′ : ∀ M →
      E.changes (prepend-type-beta-result
        {A = Rᴵ} {B = Bᴵ} {V = Vᴵ} vVᴵ resultᴵ) ▶ᵀ M
      ≡ liftImpreciseTerm W≼W′ M
  imprecise-terms′ M = trans
    (imprecise-terms (⇑ᵗᵐ M))
    (sym (liftImpreciseTerm-trans step bound≼W′ M))

  precise-terms′ : ∀ M →
      E.changes (prepend-type-beta-result
        {A = Rᴾ} {B = Bᴾ} {V = Vᴾ} vVᴾ resultᴾ) ▶ᵀ M
      ≡ liftPreciseTerm W≼W′ M
  precise-terms′ M = trans
    (precise-terms (⇑ᵗᵐ M))
    (sym (liftPreciseTerm-trans step bound≼W′ M))

  related′ = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision W≼W′ p)
    (liftCenterImprecision bound≼W′
      (liftCenterImprecision step p))
    (liftCenterTy-trans step bound≼W′ Aᴾ)
    (liftCenterTy-trans step bound≼W′ Aᴵ) related

related-type-beta-expand : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {fresh : SemanticAtom (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)} {k : ℕ}
  → Value Vᴵ
  → Value Vᴾ
  → ComputationsRelated (pairedBindWorld W Rᴾ Rᴵ fresh)
      (FutureValueRelation
        (liftCenterImprecision (paired-step W r fresh) p)) k
      (Vᴵ ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴾ 〗)
  → ComputationsRelated W (FutureValueRelation p) (suc k)
      ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])
related-type-beta-expand {W = W} {p = p} {Rᴾ} {Rᴵ} {r} {fresh}
    {Bᴾ} {Bᴵ} {Vᴾ} {Vᴵ} {k} vVᴵ vVᴾ contract-related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = forwardBlame
  }
  where
  bound = pairedBindWorld W Rᴾ Rᴵ fresh

  forward : ∀ {n} {resultᴵ : E.EvalResult
      ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ])}
    → n ≤ suc k
    → interpretFrom (impreciseStore (core W)) n
        ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult
          ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ]) ]
        interpretFrom (preciseStore (core W)) m
          ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ]) ≡ returned resultᴾ
        × PairedReturns W (FutureValueRelation p)
          (suc k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ]))
  forward {n} n≤sk result-eq
      with type-beta-return-invert
        {Σ = impreciseStore (core W)} {n} {Rᴵ} {Bᴵ} {Vᴵ}
        vVᴵ result-eq
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      with forward-return contract-related (≤-pred n≤sk) contract-eqᴵ
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₁ (m , contract-resultᴾ , contract-eqᴾ , paired)
      with type-beta-return-expand
        {Σ = preciseStore (core W)} {m} {Rᴾ} {Bᴾ} {Vᴾ}
        vVᴾ contract-eqᴾ
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₁ (m , contract-resultᴾ , contract-eqᴾ , paired)
      | vVᴾ′ , redex-eqᴾ =
    inj₁ (suc m , prepend-type-beta-result vVᴾ′ contract-resultᴾ ,
      redex-eqᴾ , paired-returns-type-beta
        {r = r} {fresh = fresh} vVᴵ′ vVᴾ′ paired)
  forward {n} n≤sk result-eq
      | gas , refl , vVᴵ′ , contract-resultᴵ , contract-eqᴵ , refl
      | inj₂ (m , contract-blameᴾ) =
    inj₂ (suc m , type-beta-blame-expand
      {Σ = preciseStore (core W)} {m} {Rᴾ} {Bᴾ} {Vᴾ}
      vVᴾ contract-blameᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult
      ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])}
    → n ≤ suc k
    → interpretFrom (preciseStore (core W)) n
        ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ]) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult
        ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ]
      interpretFrom (impreciseStore (core W)) m
        ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ]) ≡ returned resultᴵ
      × PairedReturns W (FutureValueRelation p)
        (suc k ∸ n) resultᴵ resultᴾ
  backward {n} n≤sk result-eq
      with type-beta-return-invert
        {Σ = preciseStore (core W)} {n} {Rᴾ} {Bᴾ} {Vᴾ}
        vVᴾ result-eq
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      with backward-return contract-related (≤-pred n≤sk) contract-eqᴾ
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      | m , contract-resultᴵ , contract-eqᴵ , paired
      with type-beta-return-expand
        {Σ = impreciseStore (core W)} {m} {Rᴵ} {Bᴵ} {Vᴵ}
        vVᴵ contract-eqᴵ
  backward {n} n≤sk result-eq
      | gas , refl , vVᴾ′ , contract-resultᴾ , contract-eqᴾ , refl
      | m , contract-resultᴵ , contract-eqᴵ , paired
      | vVᴵ′ , redex-eqᴵ =
    suc m , prepend-type-beta-result vVᴵ′ contract-resultᴵ ,
    redex-eqᴵ , paired-returns-type-beta
      {r = r} {fresh = fresh} vVᴵ′ vVᴾ′ paired

  forwardBlame : ∀ {n}
    → n ≤ suc k
    → BlamesFrom (impreciseStore (core W)) n
        ((Λ Vᴵ) ⦂∀ Bᴵ [ Rᴵ ])
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m
        ((Λ Vᴾ) ⦂∀ Bᴾ [ Rᴾ ])
  forwardBlame {n} n≤sk redex-blameᴵ
      with type-beta-blame-invert
        {Σ = impreciseStore (core W)} {n} {Rᴵ} {Bᴵ} {Vᴵ}
        vVᴵ redex-blameᴵ
  forwardBlame {n} n≤sk redex-blameᴵ
      | gas , refl , contract-blameᴵ
      with forward-blame contract-related (≤-pred n≤sk) contract-blameᴵ
  forwardBlame {n} n≤sk redex-blameᴵ
      | gas , refl , contract-blameᴵ | m , contract-blameᴾ =
    suc m , type-beta-blame-expand
      {Σ = preciseStore (core W)} {m} {Rᴾ} {Bᴾ} {Vᴾ}
      vVᴾ contract-blameᴾ
