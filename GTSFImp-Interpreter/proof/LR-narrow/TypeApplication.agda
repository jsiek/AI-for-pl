module proof.LR-narrow.TypeApplication where

-- File Charter:
--   * Proves compatibility of structural CTI type application.
--   * Decomposes a type-application run into operator and instantiation
--     phases and composes the worlds returned by those phases.
--   * Uses the universal LR observation before its matching allocation.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m∸n≤m)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Consistency
open import proof.TypeInTermSubst using
  (toRename-keep-eq; toRename-wk-eq; renameᵗ-wk-eq; rename-openᵗ)
import Eval as E
open import Interpreter
import Imprecision as I
import proof.Imprecision as PI
import proof.ImprecisionConsistency as IC
open import proof.ImprecisionConsistency using
  (renameᵗ-injective; toRenameᵗ-injective; ty-all-injective)
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.Atoms
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.UniversalInstantiation
open import proof.LR-narrow.BetaExpansion using
  (interpreter-outcome; interpret-from-eval; value-step-none)
open import proof.LR-narrow.Application using
  (_++ˢ_; apply-stores-++; apply-terms-++; append-trace;
   prepend-result; eval-from-return; eval-from-blame; prepend-return;
   prepend-blamed; blame-view; BlameView; is-blame; not-blame;
   blame-from-eval;
   value-return-exact; eval-from-nonblame; eval-prepend-return;
   eval-prepend-blamed; return-store-reindex;
   blame-store-reindex; value-terms-reindex; value-index-reindex;
   paired-returns-reindex; compiled-component-future; drop-left-≤;
   first-of-two≤; subtract-phases)
import proof.LR-narrow.Closure as ClosureProof

------------------------------------------------------------------------
-- Syntax and world lifting
------------------------------------------------------------------------

toRename-keep-wk-eq : ∀ {Δ} (X : TyVar (suc Δ))
  → Consistency.toRenameᵗ
      (Consistency.keep Consistency.wk↪ᵗ) X ≡ extᵗ Fin.suc X
toRename-keep-wk-eq Fin.zero = refl
toRename-keep-wk-eq (Fin.suc X) = cong Fin.suc (toRename-wk-eq X)

lift-imprecise-type-application : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (L : Term Δᴵ₀)
    (B : Ty (suc Δᴵ₀)) (A : Ty Δᴵ₀)
  → liftImpreciseTerm W₀≼W₁ (L ⦂∀ B [ A ]) ≡
      liftImpreciseTerm W₀≼W₁ L
        ⦂∀ liftImpreciseBody W₀≼W₁ B
        [ liftImpreciseTy W₀≼W₁ A ]
lift-imprecise-type-application future-refl L B A = refl
lift-imprecise-type-application
    (future-paired W₀≼W₁ related fresh) L B A
    rewrite lift-imprecise-type-application W₀≼W₁ L B A =
  cong₂ (λ C R → ⇑ᵗᵐ (liftImpreciseTerm W₀≼W₁ L)
    ⦂∀ C [ R ])
    (renameᵗ-cong (liftImpreciseBody W₀≼W₁ B)
      toRename-keep-wk-eq)
    (renameᵗ-wk-eq (liftImpreciseTy W₀≼W₁ A))
lift-imprecise-type-application (future-precise W₀≼W₁ fresh) L B A =
  lift-imprecise-type-application W₀≼W₁ L B A
lift-imprecise-type-application
    (future-imprecise W₀≼W₁) L B A
    rewrite lift-imprecise-type-application W₀≼W₁ L B A =
  cong₂ (λ C R → ⇑ᵗᵐ (liftImpreciseTerm W₀≼W₁ L)
    ⦂∀ C [ R ])
    (renameᵗ-cong (liftImpreciseBody W₀≼W₁ B)
      toRename-keep-wk-eq)
    (renameᵗ-wk-eq (liftImpreciseTy W₀≼W₁ A))

lift-precise-type-application : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (L : Term Δᴾ₀)
    (B : Ty (suc Δᴾ₀)) (A : Ty Δᴾ₀)
  → liftPreciseTerm W₀≼W₁ (L ⦂∀ B [ A ]) ≡
      liftPreciseTerm W₀≼W₁ L
        ⦂∀ liftPreciseBody W₀≼W₁ B
        [ liftPreciseTy W₀≼W₁ A ]
lift-precise-type-application future-refl L B A = refl
lift-precise-type-application
    (future-paired W₀≼W₁ related fresh) L B A
    rewrite lift-precise-type-application W₀≼W₁ L B A =
  cong₂ (λ C R → ⇑ᵗᵐ (liftPreciseTerm W₀≼W₁ L)
    ⦂∀ C [ R ])
    (renameᵗ-cong (liftPreciseBody W₀≼W₁ B)
      toRename-keep-wk-eq)
    (renameᵗ-wk-eq (liftPreciseTy W₀≼W₁ A))
lift-precise-type-application
    (future-precise W₀≼W₁ fresh) L B A
    rewrite lift-precise-type-application W₀≼W₁ L B A =
  cong₂ (λ C R → ⇑ᵗᵐ (liftPreciseTerm W₀≼W₁ L)
    ⦂∀ C [ R ])
    (renameᵗ-cong (liftPreciseBody W₀≼W₁ B)
      toRename-keep-wk-eq)
    (renameᵗ-wk-eq (liftPreciseTy W₀≼W₁ A))
lift-precise-type-application (future-imprecise W₀≼W₁) L B A =
  lift-precise-type-application W₀≼W₁ L B A

lift-imprecise-open : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁)
    (B : Ty (suc Δᴵ₀)) (A : Ty Δᴵ₀)
  → liftImpreciseTy W₀≼W₁ (B [ A ]ᵗ) ≡
      liftImpreciseBody W₀≼W₁ B
        [ liftImpreciseTy W₀≼W₁ A ]ᵗ
lift-imprecise-open future-refl B A = refl
lift-imprecise-open (future-paired W₀≼W₁ related fresh) B A =
  trans (cong (renameᵗ Fin.suc)
    (lift-imprecise-open W₀≼W₁ B A))
    (rename-openᵗ Fin.suc
      (liftImpreciseBody W₀≼W₁ B)
      (liftImpreciseTy W₀≼W₁ A))
lift-imprecise-open (future-precise W₀≼W₁ fresh) B A =
  lift-imprecise-open W₀≼W₁ B A
lift-imprecise-open (future-imprecise W₀≼W₁) B A =
  trans (cong (renameᵗ Fin.suc)
    (lift-imprecise-open W₀≼W₁ B A))
    (rename-openᵗ Fin.suc
      (liftImpreciseBody W₀≼W₁ B)
      (liftImpreciseTy W₀≼W₁ A))

lift-precise-open : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁)
    (B : Ty (suc Δᴾ₀)) (A : Ty Δᴾ₀)
  → liftPreciseTy W₀≼W₁ (B [ A ]ᵗ) ≡
      liftPreciseBody W₀≼W₁ B [ liftPreciseTy W₀≼W₁ A ]ᵗ
lift-precise-open future-refl B A = refl
lift-precise-open (future-paired W₀≼W₁ related fresh) B A =
  trans (cong (renameᵗ Fin.suc)
    (lift-precise-open W₀≼W₁ B A))
    (rename-openᵗ Fin.suc
      (liftPreciseBody W₀≼W₁ B)
      (liftPreciseTy W₀≼W₁ A))
lift-precise-open (future-precise W₀≼W₁ fresh) B A =
  trans (cong (renameᵗ Fin.suc)
    (lift-precise-open W₀≼W₁ B A))
    (rename-openᵗ Fin.suc
      (liftPreciseBody W₀≼W₁ B)
      (liftPreciseTy W₀≼W₁ A))
lift-precise-open (future-imprecise W₀≼W₁) B A =
  lift-precise-open W₀≼W₁ B A

------------------------------------------------------------------------
-- Evaluator phase packages
------------------------------------------------------------------------

returned-injective : ∀ {Δ} {M : Term Δ}
    {r s : E.EvalResult M}
  → returned r ≡ returned s
  → r ≡ s
returned-injective refl = refl

applyBodies : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → Ty (suc Δ)
  → Ty (suc Δ′)
applyBodies [] B = B
applyBodies (χ ∷ χs) B = applyBodies χs (χ ▷ᵇ B)

apply-term-type-application : ∀ {Δ Δ′}
    (χ : StoreChange Δ Δ′) (L : Term Δ)
    (B : Ty (suc Δ)) (A : Ty Δ)
  → χ ▷ᵀ (L ⦂∀ B [ A ]) ≡
      (χ ▷ᵀ L) ⦂∀ χ ▷ᵇ B [ χ ▷ᵗ A ]
apply-term-type-application keep L B A = refl
apply-term-type-application (bind R) L B A =
  cong₂ (λ C S → ⇑ᵗᵐ L ⦂∀ C [ S ])
    (renameᵗ-cong B toRename-keep-wk-eq)
    (renameᵗ-wk-eq A)

apply-terms-type-application : ∀ {Δ Δ′}
    (χs : StoreChanges Δ Δ′) (L : Term Δ)
    (B : Ty (suc Δ)) (A : Ty Δ)
  → χs ▶ᵀ (L ⦂∀ B [ A ]) ≡
      (χs ▶ᵀ L) ⦂∀ applyBodies χs B [ χs ▶ᵗ A ]
apply-terms-type-application [] L B A = refl
apply-terms-type-application (χ ∷ χs) L B A =
  trans
    (cong (applyTerms χs) (apply-term-type-application χ L B A))
    (apply-terms-type-application χs
      (χ ▷ᵀ L) (χ ▷ᵇ B) (χ ▷ᵗ A))

type-application-function-trace : ∀ {Δ₀ Δ₁}
    {L : Term Δ₀} {V : Term Δ₁}
    {B : Ty (suc Δ₀)} {A : Ty Δ₀}
    {χs : StoreChanges Δ₀ Δ₁}
  → L —↠[ χs ] V
  → L ⦂∀ B [ A ] —↠[ χs ]
      V ⦂∀ applyBodies χs B [ χs ▶ᵗ A ]
type-application-function-trace ↠-refl = ↠-refl
type-application-function-trace
    (↠-step {χ = χ} L→N N↠V) =
  ↠-step (ξ-• L→N refl refl)
    (type-application-function-trace N↠V)

sequence-type-application-result : ∀ {Δ₀}
    {L : Term Δ₀} {B : Ty (suc Δ₀)} {A : Ty Δ₀}
  → (functionResult : E.EvalResult L)
  → E.EvalResult
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ])
  → E.EvalResult (L ⦂∀ B [ A ])
sequence-type-application-result
    (E.result Δ₁ χs V L↠V vV)
    (E.result Δ₂ ψs Z call↠Z vZ) =
  E.result Δ₂ (χs ++ˢ ψs) Z
    (append-trace (type-application-function-trace L↠V) call↠Z)
    vZ

record TypeApplicationReturnPhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (L : Term Δ)
    (B : Ty (suc Δ)) (A : Ty Δ)
    (wholeResult : E.EvalResult (L ⦂∀ B [ A ])) : Set where
  constructor type-return-phases
  field
    functionGas : ℕ
    functionResult : E.EvalResult L
    functionReturn :
      interpretFrom Σ functionGas L ≡ returned functionResult

    callGas : ℕ
    callResult : E.EvalResult
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ])
    callReturn :
      interpretFrom (E.changes functionResult ▶ˢ Σ) callGas
        (E.term functionResult
          ⦂∀ applyBodies (E.changes functionResult) B
          [ E.changes functionResult ▶ᵗ A ]) ≡ returned callResult

    result-splits : wholeResult ≡
      sequence-type-application-result functionResult callResult
    gas-splits : functionGas + callGas ≡ gas

open TypeApplicationReturnPhases public

type-function-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′}
    {step : L —→[ χ ] N}
  → E.step? Σ L ≡ just (E.step-result χ N step)
  → E.step? Σ (L ⦂∀ B [ A ]) ≡
      just (E.step-result χ
        (N ⦂∀ χ ▷ᵇ B [ χ ▷ᵗ A ])
        (ξ-• step refl refl))
type-function-step-question function-step-eq
    rewrite function-step-eq = refl

type-app-final-none : ∀ {Δ} {Σ : TyStore Δ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
  → L ≢ blame
  → E.value? L ≡ nothing
  → E.type-app-final? Σ L B A ≡ nothing
type-app-final-none {L = ` x} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = ƛ N} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = L · M} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = Λ N} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = L ⦂∀ C [ R ]} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = $ κ} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = L ⊕[ op ] M} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = M ⟨ c ⟩} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = M ↑ c} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = M ↓ c} L≠blame value-eq
    rewrite value-eq = refl
type-app-final-none {L = blame} L≠blame value-eq =
  ⊥-elim (L≠blame refl)

type-application-body-injective : ∀ {Δ}
    {L L′ : Term Δ} {B B′ : Ty (suc Δ)} {A A′ : Ty Δ}
  → L ⦂∀ B [ A ] ≡ L′ ⦂∀ B′ [ A′ ]
  → B ≡ B′
type-application-body-injective refl = refl

type-application-argument-injective : ∀ {Δ}
    {L L′ : Term Δ} {B B′ : Ty (suc Δ)} {A A′ : Ty Δ}
  → L ⦂∀ B [ A ] ≡ L′ ⦂∀ B′ [ A′ ]
  → A ≡ A′
type-application-argument-injective refl = refl

imprecise-phase-body-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {χs : StoreChanges Δᴵ₀ Δᴵ₁}
  → (W₀≼W₁ : Future W₀ W₁)
  → (∀ M → χs ▶ᵀ M ≡ liftImpreciseTerm W₀≼W₁ M)
  → (B : Ty (suc Δᴵ₀)) (A : Ty Δᴵ₀)
  → applyBodies χs B ≡ liftImpreciseBody W₀≼W₁ B
imprecise-phase-body-eq {χs = χs} W₀≼W₁ terms B A =
  type-application-body-injective
    (trans (sym (apply-terms-type-application χs blame B A))
      (trans (terms (blame ⦂∀ B [ A ]))
        (lift-imprecise-type-application W₀≼W₁ blame B A)))

precise-phase-body-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {χs : StoreChanges Δᴾ₀ Δᴾ₁}
  → (W₀≼W₁ : Future W₀ W₁)
  → (∀ M → χs ▶ᵀ M ≡ liftPreciseTerm W₀≼W₁ M)
  → (B : Ty (suc Δᴾ₀)) (A : Ty Δᴾ₀)
  → applyBodies χs B ≡ liftPreciseBody W₀≼W₁ B
precise-phase-body-eq {χs = χs} W₀≼W₁ terms B A =
  type-application-body-injective
    (trans (sym (apply-terms-type-application χs blame B A))
      (trans (terms (blame ⦂∀ B [ A ]))
        (lift-precise-type-application W₀≼W₁ blame B A)))

imprecise-phase-argument-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {χs : StoreChanges Δᴵ₀ Δᴵ₁}
  → (W₀≼W₁ : Future W₀ W₁)
  → (∀ M → χs ▶ᵀ M ≡ liftImpreciseTerm W₀≼W₁ M)
  → (B : Ty (suc Δᴵ₀)) (A : Ty Δᴵ₀)
  → χs ▶ᵗ A ≡ liftImpreciseTy W₀≼W₁ A
imprecise-phase-argument-eq {χs = χs} W₀≼W₁ terms B A =
  type-application-argument-injective
    (trans (sym (apply-terms-type-application χs blame B A))
      (trans (terms (blame ⦂∀ B [ A ]))
        (lift-imprecise-type-application W₀≼W₁ blame B A)))

precise-phase-argument-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {χs : StoreChanges Δᴾ₀ Δᴾ₁}
  → (W₀≼W₁ : Future W₀ W₁)
  → (∀ M → χs ▶ᵀ M ≡ liftPreciseTerm W₀≼W₁ M)
  → (B : Ty (suc Δᴾ₀)) (A : Ty Δᴾ₀)
  → χs ▶ᵗ A ≡ liftPreciseTy W₀≼W₁ A
precise-phase-argument-eq {χs = χs} W₀≼W₁ terms B A =
  type-application-argument-injective
    (trans (sym (apply-terms-type-application χs blame B A))
      (trans (terms (blame ⦂∀ B [ A ]))
        (lift-precise-type-application W₀≼W₁ blame B A)))

type-app-stuck-step-none : ∀ {Δ} {Σ : TyStore Δ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
  → E.step? Σ L ≡ nothing
  → E.value? L ≡ nothing
  → L ≢ blame
  → E.step? Σ (L ⦂∀ B [ A ]) ≡ nothing
type-app-stuck-step-none {Σ = Σ}
    function-step-eq function-value-eq L≠blame
    rewrite function-step-eq =
  type-app-final-none {Σ = Σ} L≠blame function-value-eq

eval-type-app-stuck-none : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
  → E.step? Σ (L ⦂∀ B [ A ]) ≡ nothing
  → E.evalFrom Σ (suc gas) (L ⦂∀ B [ A ]) ≡ nothing
eval-type-app-stuck-none {Σ = Σ} {gas = gas} {L = L} {B = B}
    {A = A} step-eq with E.step? Σ (L ⦂∀ B [ A ]) | step-eq
eval-type-app-stuck-none step-eq | nothing | refl = refl

type-app-stuck-not-returned : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (L ⦂∀ B [ A ])}
  → E.step? Σ L ≡ nothing
  → E.value? L ≡ nothing
  → L ≢ blame
  → E.evalFrom Σ (suc gas) (L ⦂∀ B [ A ]) ≡
      just (E.returned result)
  → ⊥
type-app-stuck-not-returned {Σ = Σ} {gas = gas}
    function-step-eq function-value-eq L≠blame result-eq =
  impossible
  where
  step-none = type-app-stuck-step-none {Σ = Σ} function-step-eq
    function-value-eq L≠blame
  none-eq = eval-type-app-stuck-none {Σ = Σ} {gas = gas} step-none

  impossible : ⊥
  impossible with trans (sym none-eq) result-eq
  impossible | ()

eval-blame-type-application : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {B : Ty (suc Δ)} {A : Ty Δ}
  → E.evalFrom Σ (suc gas) (blame ⦂∀ B [ A ]) ≡
      just (E.blamed (keep ∷ [])
        (↠-step (pure-step blame-•) ↠-refl))
eval-blame-type-application {Σ = Σ} {gas = zero} = refl
eval-blame-type-application {Σ = Σ} {gas = suc gas} = refl

blame-type-application-not-returned : ∀
    {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (blame ⦂∀ B [ A ])}
  → E.evalFrom Σ gas (blame ⦂∀ B [ A ]) ≡
      just (E.returned result)
  → ⊥
blame-type-application-not-returned {gas = zero} ()
blame-type-application-not-returned {Σ = Σ} {gas = suc gas}
    result-eq with trans
      (sym (eval-blame-type-application {Σ = Σ} {gas = gas}))
      result-eq
blame-type-application-not-returned result-eq | ()

type-function-stuck-impossible : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (L ⦂∀ B [ A ])}
  → E.step? Σ L ≡ nothing
  → E.value? L ≡ nothing
  → E.evalFrom Σ (suc gas) (L ⦂∀ B [ A ]) ≡
      just (E.returned result)
  → ⊥
type-function-stuck-impossible {Σ = Σ} {gas = gas} {L = L}
    function-step-eq function-value-eq result-eq with blame-view L
type-function-stuck-impossible {Σ = Σ} {gas = gas}
    function-step-eq function-value-eq result-eq | is-blame refl =
  blame-type-application-not-returned {Σ = Σ} {gas = suc gas}
    result-eq
type-function-stuck-impossible {Σ = Σ} {gas = gas}
    function-step-eq function-value-eq result-eq
    | not-blame L≠blame =
  type-app-stuck-not-returned {Σ = Σ} {gas = gas}
    function-step-eq function-value-eq L≠blame result-eq

type-application-return-phases-eval : ∀ {Δ : TyCtx}
    {Σ : TyStore Δ} {gas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (L ⦂∀ B [ A ])}
  → E.evalFrom Σ gas (L ⦂∀ B [ A ]) ≡
      just (E.returned result)
  → TypeApplicationReturnPhases Σ gas L B A result
type-application-return-phases-eval {gas = zero} ()
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} {result = result} result-eq
    with E.value? L in function-value-eq
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} {result = result} result-eq
    | just vL =
  type-return-phases zero operatorResult₀ operatorReturn₀
    (suc gas) result callReturn₀ refl refl
  where
  operatorResult₀ = E.result _ [] L ↠-refl vL
  operatorReturn₀ = value-return-exact {Σ = Σ} zero vL
  callReturn₀ = trans
    (interpret-from-eval {Σ = Σ} {gas = suc gas}
      {M = L ⦂∀ B [ A ]})
    (cong interpreter-outcome result-eq)
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing
    with E.step? Σ L in function-step-eq
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas
      (N ⦂∀ χ ▷ᵇ B [ χ ▷ᵗ A ]) in next-eq
type-application-return-phases-eval result-eq | nothing
    | just (E.step-result χ N step) | nothing
    rewrite function-step-eq | next-eq
    with result-eq
type-application-return-phases-eval result-eq | nothing
    | just (E.step-result χ N step) | nothing | ()
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    rewrite function-step-eq | next-eq
    with result-eq
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    with type-application-return-phases-eval {Σ = χ ▷ˢ Σ}
      {gas = gas} {L = N} {B = χ ▷ᵇ B} {A = χ ▷ᵗ A}
      {result = next-result} next-eq
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | type-return-phases functionGas functionResult functionReturn
        callGas callResult callReturn result-split gas-eq =
  type-return-phases (suc functionGas)
    (prepend-result step functionResult)
    (prepend-return {Σ = Σ} {M = L} {gas = functionGas}
      function-step-eq functionReturn)
    callGas callResult callReturn
    (cong (prepend-result (ξ-• step refl refl)) result-split)
    (cong suc gas-eq)
type-application-return-phases-eval result-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)
    rewrite function-step-eq | next-eq
    with result-eq
type-application-return-phases-eval result-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed changes trace) | ()
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing | nothing
    with blame-view L
type-application-return-phases-eval {gas = suc gas} result-eq
    | nothing | nothing | is-blame refl with gas
type-application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | zero with result-eq
type-application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | zero | ()
type-application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | suc gas′ with result-eq
type-application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | suc gas′ | ()
type-application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} result-eq | nothing | nothing
    | not-blame L≠blame
    with E.type-app-final? Σ L B A in final-eq
type-application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≠blame | nothing
    with result-eq
type-application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≠blame | nothing | ()
type-application-return-phases-eval {Σ = Σ} {L = L} result-eq
    | nothing | nothing | not-blame L≠blame
    | just (E.step-result χ N step) = ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (type-app-final-none {Σ = Σ} L≠blame function-value-eq)
  impossible | ()

type-application-return-phases : ∀ {Δ : TyCtx}
    {Σ : TyStore Δ} {gas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (L ⦂∀ B [ A ])}
  → interpretFrom Σ gas (L ⦂∀ B [ A ]) ≡ returned result
  → TypeApplicationReturnPhases Σ gas L B A result
type-application-return-phases {Σ = Σ} {gas = gas}
    {L = L} {B = B} {A = A} result-eq =
  type-application-return-phases-eval {Σ = Σ} {gas = gas}
    {L = L} {B = B} {A = A}
    (eval-from-return {Σ = Σ} {gas = gas}
      {M = L ⦂∀ B [ A ]} result-eq)

type-application-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas callGas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {functionResult : E.EvalResult L}
    {callResult : E.EvalResult
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ])}
  → E.evalFrom Σ functionGas L ≡ just (E.returned functionResult)
  → E.evalFrom (E.changes functionResult ▶ˢ Σ) callGas
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ]) ≡
      just (E.returned callResult)
  → Σ[ wholeGas ∈ ℕ ]
      E.evalFrom Σ wholeGas (L ⦂∀ B [ A ]) ≡
        just (E.returned
          (sequence-type-application-result functionResult callResult))
type-application-return-expand-eval {Σ = Σ} {functionGas = zero}
    {callGas = callGas} {L = L} {B = B} {A = A}
    function-eq call-eq
    with blame-view L
type-application-return-expand-eval function-eq call-eq
    | is-blame refl with function-eq
type-application-return-expand-eval function-eq call-eq
    | is-blame refl | ()
type-application-return-expand-eval {Σ = Σ} {functionGas = zero}
    {callGas = callGas} {L = L} {B = B} {A = A}
    function-eq call-eq | not-blame L≠blame
    with E.value? L in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = L} L≠blame)) function-eq
type-application-return-expand-eval {Σ = Σ} {functionGas = zero}
    {callGas = callGas} function-eq call-eq
    | not-blame L≠blame | just vL | refl
    rewrite value-step-none {Σ = Σ} vL | value-eq =
  callGas , call-eq
type-application-return-expand-eval function-eq call-eq
    | not-blame L≠blame | nothing | ()
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    with blame-view L
type-application-return-expand-eval function-eq call-eq
    | is-blame refl with function-eq
type-application-return-expand-eval function-eq call-eq
    | is-blame refl | ()
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≠blame
    with E.value? L in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc functionGas} {M = L} L≠blame)) function-eq
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    function-eq call-eq
    | not-blame L≠blame | just vL | refl
    rewrite value-step-none {Σ = Σ} vL | value-eq =
  callGas , call-eq
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≠blame | nothing | normalized-eq
    with E.step? Σ L in function-step-eq
type-application-return-expand-eval function-eq call-eq
    | not-blame L≠blame | nothing | () | nothing
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≠blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
type-application-return-expand-eval function-eq call-eq
    | not-blame L≠blame | nothing | ()
    | just (E.step-result χ N step) | nothing
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≠blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with type-application-return-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {callGas = callGas}
      {L = N} {B = χ ▷ᵇ B} {A = χ ▷ᵗ A}
      {functionResult = next-result} next-eq call-eq
type-application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≠blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | wholeGas , whole-eq =
  suc wholeGas , eval-prepend-return {Σ = Σ}
    (type-function-step-question {Σ = Σ} function-step-eq) whole-eq
type-application-return-expand-eval function-eq call-eq
    | not-blame L≠blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)

type-application-return-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas callGas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {functionResult : E.EvalResult L}
    {callResult : E.EvalResult
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ])}
  → interpretFrom Σ functionGas L ≡ returned functionResult
  → interpretFrom (E.changes functionResult ▶ˢ Σ) callGas
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ]) ≡ returned callResult
  → Σ[ wholeGas ∈ ℕ ]
      interpretFrom Σ wholeGas (L ⦂∀ B [ A ]) ≡
        returned
          (sequence-type-application-result functionResult callResult)
type-application-return-expand {Σ = Σ}
    {functionGas = functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A}
    {functionResult = functionResult} {callResult = callResult}
    function-eq call-eq
    with type-application-return-expand-eval {Σ = Σ}
      {functionGas = functionGas} {callGas = callGas}
      {L = L} {B = B} {A = A}
      {functionResult = functionResult} {callResult = callResult}
      (eval-from-return {Σ = Σ} {gas = functionGas} {M = L}
        function-eq)
      (eval-from-return
        {Σ = E.changes functionResult ▶ˢ Σ} {gas = callGas}
        {M = E.term functionResult
          ⦂∀ applyBodies (E.changes functionResult) B
          [ E.changes functionResult ▶ᵗ A ]}
        call-eq)
type-application-return-expand {Σ = Σ} {L = L} {B = B} {A = A}
    function-eq call-eq
    | wholeGas , eval-eq =
  wholeGas , trans
    (interpret-from-eval {Σ = Σ} {gas = wholeGas}
      {M = L ⦂∀ B [ A ]})
    (cong interpreter-outcome eval-eq)

data TypeApplicationBlamePhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (L : Term Δ)
    (B : Ty (suc Δ)) (A : Ty Δ) : Set where
  type-function-phase-blames :
      (functionGas : ℕ)
    → BlamesFrom Σ functionGas L
    → functionGas ≤ gas
    → TypeApplicationBlamePhases Σ gas L B A

  type-call-phase-blames :
      (functionGas : ℕ)
    → (functionResult : E.EvalResult L)
    → interpretFrom Σ functionGas L ≡ returned functionResult
    → (callGas : ℕ)
    → BlamesFrom (E.changes functionResult ▶ˢ Σ) callGas
        (E.term functionResult
          ⦂∀ applyBodies (E.changes functionResult) B
          [ E.changes functionResult ▶ᵗ A ])
    → functionGas + callGas ≤ gas
    → TypeApplicationBlamePhases Σ gas L B A

type-function-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {functionGas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {changes : StoreChanges Δ Δ′} {trace : L —↠[ changes ] blame}
  → E.evalFrom Σ functionGas L ≡ just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ L ⦂∀ B [ A ] —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (L ⦂∀ B [ A ]) ≡
        just (E.blamed wholeChanges wholeTrace)
type-function-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {L = L} {B = B} {A = A} function-eq with blame-view L
type-function-blame-expand-eval {Σ = Σ} function-eq
    | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-•) ↠-refl ,
    eval-blame-type-application {Σ = Σ} {gas = zero}
type-function-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {L = L} function-eq | not-blame L≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} L≢blame
    with E.value? L
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL | ()
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | ()
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq with blame-view L
type-function-blame-expand-eval {Σ = Σ} function-eq
    | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-•) ↠-refl ,
    eval-blame-type-application {Σ = Σ} {gas = zero}
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} function-eq
    | not-blame L≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc functionGas}
      L≢blame
    with E.value? L in function-value-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL | ()
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq | not-blame L≢blame | nothing
    with E.step? Σ L in function-step-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | nothing with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | nothing | ()
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step) | nothing
    with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step) | nothing | ()
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) with function-eq
type-function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) | ()
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) with function-eq
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with type-function-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {L = N}
      {B = χ ▷ᵇ B} {A = χ ▷ᵗ A} next-eq
type-function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {B = B} {A = A}
    function-eq | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-• step refl refl) wholeTrace ,
  eval-prepend-blamed {Σ = Σ}
    {gas = wholeGas}
    (type-function-step-question {Σ = Σ} function-step-eq) whole-eq

type-function-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
  → BlamesFrom Σ functionGas L
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L ⦂∀ B [ A ])
type-function-blame-expand {Σ = Σ} {functionGas = functionGas}
    {L = L} {B = B} {A = A}
    (Δ′ , changes , trace , function-eq)
    with type-function-blame-expand-eval {Σ = Σ}
      {functionGas = functionGas} {L = L} {B = B} {A = A}
      (eval-from-blame {Σ = Σ} {gas = functionGas} function-eq)
type-function-blame-expand {Σ = Σ} functionBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

type-application-call-blame-expand-eval : ∀ {Δ Δ′}
    {Σ : TyStore Δ} {functionGas callGas : ℕ}
    {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
    {functionResult : E.EvalResult L}
    {changes : StoreChanges (E.Δ′ functionResult) Δ′}
    {trace :
      E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ] —↠[ changes ] blame}
  → E.evalFrom Σ functionGas L ≡ just (E.returned functionResult)
  → E.evalFrom (E.changes functionResult ▶ˢ Σ) callGas
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ]) ≡
      just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ L ⦂∀ B [ A ] —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (L ⦂∀ B [ A ]) ≡
        just (E.blamed wholeChanges wholeTrace)
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = zero} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    with blame-view L
type-application-call-blame-expand-eval function-eq call-eq
    | is-blame refl with function-eq
type-application-call-blame-expand-eval function-eq call-eq
    | is-blame refl | ()
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = zero} {callGas = callGas} {L = L}
    function-eq call-eq | not-blame L≢blame
    with E.value? L in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = L} L≢blame)) function-eq
type-application-call-blame-expand-eval {callGas = callGas}
    function-eq call-eq | not-blame L≢blame | just vL | refl =
  callGas , _ , _ , _ , call-eq
type-application-call-blame-expand-eval function-eq call-eq
    | not-blame L≢blame | nothing | ()
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    with blame-view L
type-application-call-blame-expand-eval function-eq call-eq
    | is-blame refl with function-eq
type-application-call-blame-expand-eval function-eq call-eq
    | is-blame refl | ()
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} function-eq call-eq | not-blame L≢blame
    with E.value? L in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc functionGas} {M = L} L≢blame)) function-eq
type-application-call-blame-expand-eval {callGas = callGas}
    function-eq call-eq | not-blame L≢blame | just vL | refl =
  callGas , _ , _ , _ , call-eq
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    with E.step? Σ L in function-step-eq
type-application-call-blame-expand-eval function-eq call-eq
    | not-blame L≢blame | nothing | () | nothing
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
type-application-call-blame-expand-eval function-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with type-application-call-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {callGas = callGas}
      {L = N} {B = χ ▷ᵇ B} {A = χ ▷ᵗ A}
      {functionResult = next-result} next-eq call-eq
type-application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} function-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-• step refl refl) wholeTrace ,
  eval-prepend-blamed {Σ = Σ}
    {gas = wholeGas}
    (type-function-step-question {Σ = Σ} function-step-eq) whole-eq
type-application-call-blame-expand-eval function-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)

type-application-call-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas callGas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {functionResult : E.EvalResult L}
  → interpretFrom Σ functionGas L ≡ returned functionResult
  → BlamesFrom (E.changes functionResult ▶ˢ Σ) callGas
      (E.term functionResult
        ⦂∀ applyBodies (E.changes functionResult) B
        [ E.changes functionResult ▶ᵗ A ])
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L ⦂∀ B [ A ])
type-application-call-blame-expand {Σ = Σ}
    {functionGas = functionGas} {callGas = callGas}
    {L = L} {B = B} {A = A} {functionResult = functionResult}
    function-eq (Δ′ , changes , trace , call-eq)
    with type-application-call-blame-expand-eval {Σ = Σ}
      {functionGas = functionGas} {callGas = callGas}
      {L = L} {B = B} {A = A} {functionResult = functionResult}
      (eval-from-return {Σ = Σ} {gas = functionGas} function-eq)
      (eval-from-blame {Σ = E.changes functionResult ▶ˢ Σ}
        {gas = callGas} call-eq)
type-application-call-blame-expand {Σ = Σ} function-eq callBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

type-application-blame-phases-eval : ∀ {Δ Δ′}
    {Σ : TyStore Δ} {gas : ℕ} {L : Term Δ}
    {B : Ty (suc Δ)} {A : Ty Δ}
    {changes : StoreChanges Δ Δ′}
    {trace : L ⦂∀ B [ A ] —↠[ changes ] blame}
  → E.evalFrom Σ gas (L ⦂∀ B [ A ]) ≡
      just (E.blamed changes trace)
  → TypeApplicationBlamePhases Σ gas L B A
type-application-blame-phases-eval {gas = zero} ()
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq
    with E.value? L in function-value-eq
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | just vL =
  type-call-phase-blames zero
    (E.result _ [] L ↠-refl vL)
    (value-return-exact {Σ = Σ} zero vL)
    (suc gas) (blame-from-eval {Σ = Σ} {gas = suc gas} whole-eq)
    ≤-refl
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    with E.step? Σ L in function-step-eq
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas
      (N ⦂∀ χ ▷ᵇ B [ χ ▷ᵗ A ]) in next-eq
type-application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | nothing
    rewrite function-step-eq | next-eq with whole-eq
type-application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | nothing | ()
type-application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | just (E.returned next-result)
    rewrite function-step-eq | next-eq with whole-eq
type-application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | just (E.returned next-result)
    | ()
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
    rewrite function-step-eq | next-eq with whole-eq
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with type-application-blame-phases-eval {Σ = χ ▷ˢ Σ}
      {gas = gas} {L = N} {B = χ ▷ᵇ B} {A = χ ▷ᵗ A} next-eq
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | type-function-phase-blames functionGas functionBlame
        functionGas≤ =
  type-function-phase-blames (suc functionGas)
    (prepend-blamed {Σ = Σ} function-step-eq functionBlame)
    (s≤s functionGas≤)
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | type-call-phase-blames functionGas functionResult
        functionReturn callGas callBlame phases≤ =
  type-call-phase-blames (suc functionGas)
    (prepend-result step functionResult)
    (prepend-return {Σ = Σ} function-step-eq functionReturn)
    callGas callBlame (s≤s phases≤)
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing | nothing
    with blame-view L
type-application-blame-phases-eval whole-eq | nothing | nothing
    | is-blame refl =
  type-function-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
type-application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {B = B} {A = A} whole-eq | nothing | nothing
    | not-blame L≢blame
    with E.type-app-final? Σ L B A in final-eq
type-application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | nothing with whole-eq
type-application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | nothing | ()
type-application-blame-phases-eval {Σ = Σ} {L = L}
    {B = B} {A = A} whole-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step) = ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (type-app-final-none {Σ = Σ} {B = B} {A = A}
      L≢blame function-value-eq)
  impossible | ()

type-application-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
  → BlamesFrom Σ gas (L ⦂∀ B [ A ])
  → TypeApplicationBlamePhases Σ gas L B A
type-application-blame-phases {Σ = Σ} {gas = gas}
    {L = L} {B = B} {A = A}
    (Δ′ , changes , trace , whole-eq) =
  type-application-blame-phases-eval {Σ = Σ} {gas = gas}
    {L = L} {B = B} {A = A}
    (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)

type-application-return-positive≤ : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
    {result : E.EvalResult (L ⦂∀ B [ A ])}
  → interpretFrom Σ gas (L ⦂∀ B [ A ]) ≡ returned result
  → suc zero ≤ gas
type-application-return-positive≤ {gas = zero} ()
type-application-return-positive≤ {gas = suc gas} result-eq = s≤s z≤n

type-application-blame-positive≤ : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {L : Term Δ} {B : Ty (suc Δ)} {A : Ty Δ}
  → BlamesFrom Σ gas (L ⦂∀ B [ A ])
  → suc zero ≤ gas
type-application-blame-positive≤ {gas = zero}
    (Δ′ , changes , trace , ())
type-application-blame-positive≤ {gas = suc gas} blaming = s≤s z≤n

------------------------------------------------------------------------
-- The fresh argument atom selected by elimination
------------------------------------------------------------------------

empty-paired-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ)
    (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) Fin.zero
empty-paired-atom W Aᴾ Aᴵ =
  fresh-semantic-atom {W = W} Aᴾ Aᴵ
    (λ k Vᴵ Vᴾ → ⊥) (λ ()) (λ ())

empty-dynamic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ)
  → DynamicSemanticAtom (preciseBindCore W Aᴾ) Fin.zero
empty-dynamic-atom W Aᴾ =
  fresh-dynamic-semantic-atom {W = W} Aᴾ
    (λ k Vᴵ Vᴾ → ⊥) (λ ()) (λ ())

precise-universal-body-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {B C : Ty (suc Δᴾ)}
  → embedPrecise (core W) (`∀ B) ≡
      `∀ (renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) C)
  → B ≡ C
precise-universal-body-eq {W = W} eq = ty-all-injective
  (renameᵗ-injective
    (toRenameᵗ-injective (preciseEmbedding (core W))) eq)

imprecise-universal-body-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {B C : Ty (suc Δᴵ)}
  → embedImprecise (core W) (`∀ B) ≡
      `∀ (renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W)))) C)
  → B ≡ C
imprecise-universal-body-eq {W = W} eq = ty-all-injective
  (renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W))) eq)

precise-universal-bodies-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {P : Ty (suc Δᶜ)}
    {B C : Ty (suc Δᴾ)}
  → embedPrecise (core W) (`∀ B) ≡ `∀ P
  → embedPrecise (core W) (`∀ C) ≡ `∀ P
  → B ≡ C
precise-universal-bodies-eq {W = W} B-eq C-eq =
  ty-all-injective
    (renameᵗ-injective
      (toRenameᵗ-injective (preciseEmbedding (core W)))
      (trans B-eq (sym C-eq)))

imprecise-universal-bodies-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {P : Ty (suc Δᶜ)}
    {B C : Ty (suc Δᴵ)}
  → embedImprecise (core W) (`∀ B) ≡ `∀ P
  → embedImprecise (core W) (`∀ C) ≡ `∀ P
  → B ≡ C
imprecise-universal-bodies-eq {W = W} B-eq C-eq =
  ty-all-injective
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans B-eq (sym C-eq)))

imprecise-types-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {P : Ty Δᶜ}
    {B C : Ty Δᴵ}
  → embedImprecise (core W) B ≡ P
  → embedImprecise (core W) C ≡ P
  → B ≡ C
imprecise-types-eq {W = W} B-eq C-eq =
  renameᵗ-injective
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (trans B-eq (sym C-eq))

precise-body-lift-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (C : Ty (suc Δᴾ₀))
  → renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W₁))))
      (liftPreciseBody W₀≼W₁ C) ≡
    liftCenterBody W₀≼W₁
      (renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) C)
precise-body-lift-eq {W₀ = W₀} {W₁ = W₁} W₀≼W₁ C =
  ty-all-injective
    (trans
      (cong (embedPrecise (core W₁))
        (sym (liftPreciseTy-universal W₀≼W₁ C)))
      (trans (embedPrecise-lift W₀≼W₁ (`∀ C))
        (liftCenterTy-universal W₀≼W₁
          (renameᵗ (extᵗ (Consistency.toRenameᵗ
            (preciseEmbedding (core W₀)))) C))))

imprecise-body-lift-eq : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (C : Ty (suc Δᴵ₀))
  → renameᵗ (extᵗ (Consistency.toRenameᵗ
      (impreciseEmbedding (core W₁))))
      (liftImpreciseBody W₀≼W₁ C) ≡
    liftCenterBody W₀≼W₁
      (renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W₀)))) C)
imprecise-body-lift-eq {W₀ = W₀} {W₁ = W₁} W₀≼W₁ C =
  ty-all-injective
    (trans
      (cong (embedImprecise (core W₁))
        (sym (liftImpreciseTy-universal W₀≼W₁ C)))
      (trans (embedImprecise-lift W₀≼W₁ (`∀ C))
        (liftCenterTy-universal W₀≼W₁
          (renameᵗ (extᵗ (Consistency.toRenameᵗ
            (impreciseEmbedding (core W₀)))) C))))

lift-local-body-imprecision : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Cᴾ : Ty (suc Δᴾ₀)} {Cᴵ : Ty (suc Δᴵ₀)}
  → (W₀≼W₁ : Future W₀ W₁)
  → I.extᵐ (impEnv (core W₀)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W₀)))) Cᴵ
  → I.extᵐ (impEnv (core W₁)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₁))))
        (liftPreciseBody W₀≼W₁ Cᴾ)
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W₁))))
        (liftImpreciseBody W₀≼W₁ Cᴵ)
lift-local-body-imprecision {W₀ = W₀} {W₁ = W₁}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} W₀≼W₁ p =
  subst≡ (λ P → I.extᵐ (impEnv (core W₁)) I.⊢ P ⊑ localᴵ)
    (sym (precise-body-lift-eq W₀≼W₁ Cᴾ))
    (subst≡ (λ Q → I.extᵐ (impEnv (core W₁)) I.⊢ centerᴾ ⊑ Q)
      (sym (imprecise-body-lift-eq W₀≼W₁ Cᴵ))
      (liftCenterBodyImprecision W₀≼W₁ p))
  where
  localᴵ = renameᵗ (extᵗ (Consistency.toRenameᵗ
    (impreciseEmbedding (core W₁))))
    (liftImpreciseBody W₀≼W₁ Cᴵ)

  centerᴾ = liftCenterBody W₀≼W₁
    (renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W₀)))) Cᴾ)

positive-universal-application : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {Pᴾ Pᴵ : Ty (suc Δᶜ)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Pᴾ ⊑ Pᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Cᴵ [ Rᴵ ]ᵗ}
    {fresh : SemanticAtom
      (pairedBindCore (core W) Rᴾ Rᴵ) Fin.zero}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → embedPrecise (core W) (`∀ Cᴾ) ≡ `∀ Pᴾ
  → embedImprecise (core W) (`∀ Cᴵ) ≡ `∀ Pᴵ
  → suc zero ≤ k
  → ValueImprecision W (I.∀⊑∀ p) k Vᴵ Vᴾ
  → let step = future-paired (future-refl {W = W}) r fresh
    in ComputationsRelated W (PostBindValueRelation step s) k
      (Vᴵ ⦂∀ Cᴵ [ Rᴵ ]) (Vᴾ ⦂∀ Cᴾ [ Rᴾ ])
positive-universal-application {k = zero} Cᴾ-eq Cᴵ-eq () related
positive-universal-application {W = W} {Cᴾ = Cᴾ} {Cᴵ = Cᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {p = p} {r = r} {s = s}
    {fresh = fresh} {k = suc k} Cᴾ-eq Cᴵ-eq positive related
    with related-universal-instantiation {W = W} {p = p} {r = r}
      {fresh = fresh} related
positive-universal-application {W = W} {Cᴾ = Cᴾ} {Cᴵ = Cᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {p = p} {r = r} {s = s}
    {fresh = fresh} {k = suc k} Cᴾ-eq Cᴵ-eq positive related
    | Bᴾ , Bᴵ , eqᴾ , eqᴵ , call
    rewrite precise-universal-bodies-eq {W = W} eqᴾ Cᴾ-eq
          | imprecise-universal-bodies-eq {W = W} eqᴵ Cᴵ-eq =
  call s

right-universal-application : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Cᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {Rᴾ : Ty Δᴾ}
    {Pᴾ : Ty (suc Δᶜ)} {Pᴵ : Ty Δᶜ}
    {p : I.instᵐ (impEnv (core W)) I.⊢ Pᴾ ⊑ ⇑ᵗ Pᴵ}
    {nonvar : NonVar Pᴾ} {occurs : Fin.zero ∈ᵗ Pᴾ}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ}
    {fresh : DynamicSemanticAtom
      (preciseBindCore (core W) Rᴾ) Fin.zero}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → embedPrecise (core W) (`∀ Cᴾ) ≡ `∀ Pᴾ
  → embedImprecise (core W) Bᴵ ≡ Pᴵ
  → ValueImprecision W (I.∀⊑ nonvar occurs p) k Vᴵ Vᴾ
  → let step = future-precise (future-refl {W = W}) fresh
    in ComputationsRelated W (PostBindValueRelation step s) k
      Vᴵ (Vᴾ ⦂∀ Cᴾ [ Rᴾ ])
right-universal-application {W = W} {Cᴾ = Cᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {s = s} {fresh = fresh}
    Cᴾ-eq Bᴵ-eq related
    with right-related-universal-instantiation
      {W = W} {fresh = fresh} related
right-universal-application {W = W} {Cᴾ = Cᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {s = s} {fresh = fresh}
    Cᴾ-eq Bᴵ-eq related
    | Dᴾ , Dᴵ , eqᴾ , eqᴵ , call
    rewrite precise-universal-bodies-eq {W = W} eqᴾ Cᴾ-eq
          | imprecise-types-eq {W = W} eqᴵ Bᴵ-eq =
  call s

positive-lifted-universal-application : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Cᴾ : Ty (suc Δᴾ₀)} {Cᴵ : Ty (suc Δᴵ₀)}
    {Rᴾ : Ty Δᴾ₀} {Rᴵ : Ty Δᴵ₀}
    {p : I.extᵐ (impEnv (core W₀)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W₀)))) Cᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W₀ ⟩ Rᴵ}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W₀ ⟩ Cᴵ [ Rᴵ ]ᵗ}
    {k : ℕ} {Vᴵ : Term Δᴵ₁} {Vᴾ : Term Δᴾ₁}
  → (W₀≼W₁ : Future W₀ W₁)
  → (fresh : SemanticAtom
      (pairedBindCore (core W₁)
        (liftPreciseTy W₀≼W₁ Rᴾ)
        (liftImpreciseTy W₀≼W₁ Rᴵ)) Fin.zero)
  → suc zero ≤ k
  → ValueImprecision W₁
      (liftCenterImprecision W₀≼W₁ (I.∀⊑∀ p)) k Vᴵ Vᴾ
  → let r′ = liftLocalImprecision W₀≼W₁ r
        s′ = ClosureProof.local-imprecision-reindex {W = W₁}
          (liftLocalImprecision W₀≼W₁ s)
          (sym (lift-precise-open W₀≼W₁ Cᴾ Rᴾ))
          (sym (lift-imprecise-open W₀≼W₁ Cᴵ Rᴵ))
        step = future-paired (future-refl {W = W₁}) r′ fresh
    in ComputationsRelated W₁ (PostBindValueRelation step s′) k
      (Vᴵ ⦂∀ liftImpreciseBody W₀≼W₁ Cᴵ
        [ liftImpreciseTy W₀≼W₁ Rᴵ ])
      (Vᴾ ⦂∀ liftPreciseBody W₀≼W₁ Cᴾ
        [ liftPreciseTy W₀≼W₁ Rᴾ ])
positive-lifted-universal-application {W₀ = W₀} {W₁ = W₁}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {p = p} {r = r} {s = s} {k = k} W₀≼W₁ fresh positive related =
  positive-universal-application {W = W₁} {p = local-body}
    {r = liftLocalImprecision W₀≼W₁ r}
    {s = ClosureProof.local-imprecision-reindex {W = W₁}
      (liftLocalImprecision W₀≼W₁ s)
      (sym (lift-precise-open W₀≼W₁ Cᴾ Rᴾ))
      (sym (lift-imprecise-open W₀≼W₁ Cᴵ Rᴵ))}
    {fresh = fresh}
    refl refl positive explicit-related
  where
  local-universal = liftLocalImprecision W₀≼W₁ (I.∀⊑∀ p)

  local-body = lift-local-body-imprecision W₀≼W₁ p

  explicit-local-universal = I.∀⊑∀ local-body

  local-related = ClosureProof.value-imprecision-center→local
    W₀≼W₁ (I.∀⊑∀ p) related

  explicit-related = ClosureProof.value-imprecision-reindex
    explicit-local-universal local-universal
    (cong (embedPrecise (core W₁))
      (sym (liftPreciseTy-universal W₀≼W₁ Cᴾ)))
    (cong (embedImprecise (core W₁))
      (sym (liftImpreciseTy-universal W₀≼W₁ Cᴵ))) local-related

reindex-lifted-type-call : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂
     Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Cᴾ : Ty (suc Δᴾ₀)} {Cᴵ : Ty (suc Δᴵ₀)}
    {Rᴾ : Ty Δᴾ₀} {Rᴵ : Ty Δᴵ₀}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W₀ ⟩ Cᴵ [ Rᴵ ]ᵗ}
    {Dᴾ : Ty (suc Δᴾ₂)} {Dᴵ : Ty (suc Δᴵ₂)}
    {Sᴾ : Ty Δᴾ₂} {Sᴵ : Ty Δᴵ₂}
    {Vᴾ : Term Δᴾ₂} {Vᴵ : Term Δᴵ₂}
    {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ} {step : Future W₂ bound}
    {k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → (W₁≼W₂ : Future W₁ W₂)
  → Dᴾ ≡ liftPreciseBody W₁≼W₂
      (liftPreciseBody W₀≼W₁ Cᴾ)
  → Dᴵ ≡ liftImpreciseBody W₁≼W₂
      (liftImpreciseBody W₀≼W₁ Cᴵ)
  → Sᴾ ≡ liftPreciseTy W₁≼W₂ (liftPreciseTy W₀≼W₁ Rᴾ)
  → Sᴵ ≡ liftImpreciseTy W₁≼W₂
      (liftImpreciseTy W₀≼W₁ Rᴵ)
  → ComputationsRelated W₂
      (PostBindValueRelation step
        (ClosureProof.local-imprecision-reindex {W = W₂}
          (liftLocalImprecision (future-trans W₀≼W₁ W₁≼W₂) s)
          (sym (lift-precise-open
            (future-trans W₀≼W₁ W₁≼W₂) Cᴾ Rᴾ))
          (sym (lift-imprecise-open
            (future-trans W₀≼W₁ W₁≼W₂) Cᴵ Rᴵ)))) k
      (Vᴵ ⦂∀ liftImpreciseBody (future-trans W₀≼W₁ W₁≼W₂) Cᴵ
        [ liftImpreciseTy (future-trans W₀≼W₁ W₁≼W₂) Rᴵ ])
      (Vᴾ ⦂∀ liftPreciseBody (future-trans W₀≼W₁ W₁≼W₂) Cᴾ
        [ liftPreciseTy (future-trans W₀≼W₁ W₁≼W₂) Rᴾ ])
  → ComputationsRelated W₂
      (PostBindValueRelation step
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ s))) k
      (Vᴵ ⦂∀ Dᴵ [ Sᴵ ]) (Vᴾ ⦂∀ Dᴾ [ Sᴾ ])
reindex-lifted-type-call {W₀ = W₀} {W₂ = W₂}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {s = s} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    W₀≼W₁ W₁≼W₂ bodyEqᴾ bodyEqᴵ
    argumentEqᴾ argumentEqᴵ related =
  ClosureProof.computations-related-post-bind-reindex
    local-result sequential-result
    preciseResultEq impreciseResultEq
    impreciseTermEq preciseTermEq related
  where
  composite = future-trans W₀≼W₁ W₁≼W₂

  local-result = ClosureProof.local-imprecision-reindex {W = W₂}
    (liftLocalImprecision composite s)
    (sym (lift-precise-open composite Cᴾ Rᴾ))
    (sym (lift-imprecise-open composite Cᴵ Rᴵ))

  sequential-result = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ s)

  preciseResultEq = trans
    (cong (embedPrecise (core W₂))
      (sym (lift-precise-open composite Cᴾ Rᴾ)))
    (trans (embedPrecise-lift composite (Cᴾ [ Rᴾ ]ᵗ))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        (embedPrecise (core W₀) (Cᴾ [ Rᴾ ]ᵗ))))

  impreciseResultEq = trans
    (cong (embedImprecise (core W₂))
      (sym (lift-imprecise-open composite Cᴵ Rᴵ)))
    (trans (embedImprecise-lift composite (Cᴵ [ Rᴵ ]ᵗ))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        (embedImprecise (core W₀) (Cᴵ [ Rᴵ ]ᵗ))))

  preciseTermEq = cong₂ (λ D S → Vᴾ ⦂∀ D [ S ])
    (trans (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ Cᴾ)
      (sym bodyEqᴾ))
    (trans (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ Rᴾ)
      (sym argumentEqᴾ))

  impreciseTermEq = cong₂ (λ D S → Vᴵ ⦂∀ D [ S ])
    (trans (liftImpreciseBody-trans W₀≼W₁ W₁≼W₂ Cᴵ)
      (sym bodyEqᴵ))
    (trans (liftImpreciseTy-trans W₀≼W₁ W₁≼W₂ Rᴵ)
      (sym argumentEqᴵ))

related-type-call-after-function : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Cᴾ : Ty (suc Δᴾ₀)} {Cᴵ : Ty (suc Δᴵ₀)}
    {Rᴾ : Ty Δᴾ₀} {Rᴵ : Ty Δᴵ₀}
    {p : I.extᵐ (impEnv (core W₀)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W₀)))) Cᴵ}
    {r : Rᴾ ⊑ᵂ⟨ core W₀ ⟩ Rᴵ}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W₀ ⟩ Cᴵ [ Rᴵ ]ᵗ}
    {Dᴾ : Ty (suc Δᴾ₂)} {Dᴵ : Ty (suc Δᴵ₂)}
    {Sᴾ : Ty Δᴾ₂} {Sᴵ : Ty Δᴵ₂}
    {Vᴾ : Term Δᴾ₂} {Vᴵ : Term Δᴵ₂} {k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → (W₁≼W₂ : Future W₁ W₂)
  → Dᴾ ≡ liftPreciseBody W₁≼W₂
      (liftPreciseBody W₀≼W₁ Cᴾ)
  → Dᴵ ≡ liftImpreciseBody W₁≼W₂
      (liftImpreciseBody W₀≼W₁ Cᴵ)
  → Sᴾ ≡ liftPreciseTy W₁≼W₂ (liftPreciseTy W₀≼W₁ Rᴾ)
  → Sᴵ ≡ liftImpreciseTy W₁≼W₂
      (liftImpreciseTy W₀≼W₁ Rᴵ)
  → suc zero ≤ k
  → ValueImprecision W₂
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁ (I.∀⊑∀ p))) k Vᴵ Vᴾ
  → let composite = future-trans W₀≼W₁ W₁≼W₂
        r′ = liftLocalImprecision composite r
        fresh = empty-paired-atom (core W₂)
          (liftPreciseTy composite Rᴾ) (liftImpreciseTy composite Rᴵ)
        step = future-paired (future-refl {W = W₂}) r′ fresh
    in ComputationsRelated W₂
      (PostBindValueRelation step
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ s))) k
      (Vᴵ ⦂∀ Dᴵ [ Sᴵ ]) (Vᴾ ⦂∀ Dᴾ [ Sᴾ ])
related-type-call-after-function {W₀ = W₀} {W₁ = W₁} {W₂ = W₂}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {p = p} {r = r} {s = s} {Dᴾ = Dᴾ} {Dᴵ = Dᴵ}
    {Sᴾ = Sᴾ} {Sᴵ = Sᴵ} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k}
    W₀≼W₁ W₁≼W₂ bodyEqᴾ bodyEqᴵ argumentEqᴾ argumentEqᴵ
    positive functionRelated =
  reindex-lifted-type-call {step = step} {k = k}
    W₀≼W₁ W₁≼W₂
    bodyEqᴾ bodyEqᴵ argumentEqᴾ argumentEqᴵ localCall
  where
  composite = future-trans W₀≼W₁ W₁≼W₂

  compositeFunction = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision composite (I.∀⊑∀ p))
    (liftCenterImprecision W₁≼W₂
      (liftCenterImprecision W₀≼W₁ (I.∀⊑∀ p)))
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedPrecise (core W₀) (`∀ Cᴾ)))
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedImprecise (core W₀) (`∀ Cᴵ))) functionRelated

  fresh = empty-paired-atom (core W₂)
    (liftPreciseTy composite Rᴾ) (liftImpreciseTy composite Rᴵ)

  step = future-paired (future-refl {W = W₂})
    (liftLocalImprecision composite r) fresh

  localCall = positive-lifted-universal-application
    {W₀ = W₀} {W₁ = W₂} {Cᴾ = Cᴾ} {Cᴵ = Cᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {p = p} {r = r} {s = s}
    composite fresh positive compositeFunction

right-type-call-after-function : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁
     Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Cᴾ : Ty (suc Δᴾ₀)} {Bᴵ : Ty Δᴵ₀} {Rᴾ : Ty Δᴾ₀}
    {p : I.instᵐ (impEnv (core W₀)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ
      ⊑ ⇑ᵗ (embedImprecise (core W₀) Bᴵ)}
    {nonvar : NonVar (renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W₀)))) Cᴾ)}
    {occurs : Fin.zero ∈ᵗ renameᵗ
      (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ}
    {s : Cᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W₀ ⟩ Bᴵ}
    {Dᴾ : Ty (suc Δᴾ₂)} {Sᴾ : Ty Δᴾ₂}
    {Vᴾ : Term Δᴾ₂} {Vᴵ : Term Δᴵ₂} {k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → (W₁≼W₂ : Future W₁ W₂)
  → Dᴾ ≡ liftPreciseBody W₁≼W₂
      (liftPreciseBody W₀≼W₁ Cᴾ)
  → Sᴾ ≡ liftPreciseTy W₁≼W₂ (liftPreciseTy W₀≼W₁ Rᴾ)
  → ValueImprecision W₂
      (liftCenterImprecision W₁≼W₂
        (liftCenterImprecision W₀≼W₁
          (I.∀⊑ nonvar occurs p))) k Vᴵ Vᴾ
  → let composite = future-trans W₀≼W₁ W₁≼W₂
        fresh = empty-dynamic-atom (core W₂)
          (liftPreciseTy composite Rᴾ)
        step = future-precise (future-refl {W = W₂}) fresh
    in ComputationsRelated W₂
      (PostBindValueRelation step
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ s))) k
      Vᴵ (Vᴾ ⦂∀ Dᴾ [ Sᴾ ])
right-type-call-after-function {W₀ = W₀} {W₁ = W₁} {W₂ = W₂}
    {Cᴾ = Cᴾ} {Bᴵ = Bᴵ} {Rᴾ = Rᴾ}
    {p = p} {nonvar = nonvar} {occurs = occurs} {s = s}
    {Dᴾ = Dᴾ} {Sᴾ = Sᴾ} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ} {k = k}
    W₀≼W₁ W₁≼W₂ bodyEqᴾ argumentEqᴾ functionRelated =
  ClosureProof.computations-related-post-bind-reindex
    local-result sequential-result
    preciseResultEq impreciseResultEq refl preciseTermEq localCall
  where
  composite = future-trans W₀≼W₁ W₁≼W₂

  compositeFunction = ClosureProof.value-imprecision-reindex
    (liftCenterImprecision composite (I.∀⊑ nonvar occurs p))
    (liftCenterImprecision W₁≼W₂
      (liftCenterImprecision W₀≼W₁ (I.∀⊑ nonvar occurs p)))
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedPrecise (core W₀) (`∀ Cᴾ)))
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedImprecise (core W₀) Bᴵ)) functionRelated

  p-lifted = liftCenterDynamicBodyImprecision composite p

  p-structural = subst≡
    (λ T → I.instᵐ (impEnv (core W₂)) I.⊢
      liftCenterBody composite
        (renameᵗ (extᵗ (Consistency.toRenameᵗ
          (preciseEmbedding (core W₀)))) Cᴾ) ⊑ T)
    (liftCenterBody-shift composite (embedImprecise (core W₀) Bᴵ))
    p-lifted

  structural = I.∀⊑
    (liftCenterBody-nonvar composite nonvar)
    (liftCenterBody-occurs composite occurs)
    p-structural

  structuralFunction = ClosureProof.value-imprecision-reindex
    structural
    (liftCenterImprecision composite (I.∀⊑ nonvar occurs p))
    (sym (liftCenterTy-universal composite
      (renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W₀)))) Cᴾ)))
    refl compositeFunction

  local-result = ClosureProof.local-imprecision-reindex {W = W₂}
    (liftLocalImprecision composite s)
    (sym (lift-precise-open composite Cᴾ Rᴾ)) refl

  fresh = empty-dynamic-atom (core W₂)
    (liftPreciseTy composite Rᴾ)

  step = future-precise (future-refl {W = W₂}) fresh

  localCall = right-universal-application
    {W = W₂} {p = p-structural} {s = local-result}
    {fresh = fresh} {k = k}
    (cong `∀ (precise-body-lift-eq composite Cᴾ))
    (embedImprecise-lift composite Bᴵ) structuralFunction

  sequential-result = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ s)

  preciseResultEq = trans
    (cong (embedPrecise (core W₂))
      (sym (lift-precise-open composite Cᴾ Rᴾ)))
    (trans (embedPrecise-lift composite (Cᴾ [ Rᴾ ]ᵗ))
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        (embedPrecise (core W₀) (Cᴾ [ Rᴾ ]ᵗ))))

  impreciseResultEq = trans (embedImprecise-lift composite Bᴵ)
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedImprecise (core W₀) Bᴵ))

  preciseTermEq = cong₂ (λ D S → Vᴾ ⦂∀ D [ S ])
    (trans (liftPreciseBody-trans W₀≼W₁ W₁≼W₂ Cᴾ)
      (sym bodyEqᴾ))
    (trans (liftPreciseTy-trans W₀≼W₁ W₁≼W₂ Rᴾ)
      (sym argumentEqᴾ))

------------------------------------------------------------------------
-- Joining the operator and instantiated-call worlds
------------------------------------------------------------------------

assemble-right-type-application-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁ Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {Aᴾ Aᴵ : Ty Δᶜ₀}
    {q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ}
    {Lᴾ : Term Δᴾ₀} {Lᴵ : Term Δᴵ₀}
    {functionResultᴾ : E.EvalResult Lᴾ}
    {functionResultᴵ : E.EvalResult Lᴵ}
    {Bᴾ : Ty (suc Δᴾ₀)} {Rᴾ : Ty Δᴾ₀}
    {callResultᴾ : E.EvalResult
      (E.term functionResultᴾ
        ⦂∀ applyBodies (E.changes functionResultᴾ) Bᴾ
        [ E.changes functionResultᴾ ▶ᵗ Rᴾ ])}
    {W₁ : World (E.Δ′ functionResultᴾ)
      (E.Δ′ functionResultᴵ) Δᶜ₁}
    {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {j k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → impreciseStore (core W₁) ≡
      E.changes functionResultᴵ ▶ˢ impreciseStore (core W₀)
  → preciseStore (core W₁) ≡
      E.changes functionResultᴾ ▶ˢ preciseStore (core W₀)
  → (∀ M → E.changes functionResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₁ M)
  → (∀ M → E.changes functionResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₁ M)
  → (step : Future W₁ bound)
  → PairedReturns W₁
      (PostBindValueRelation step
        (liftCenterImprecision W₀≼W₁ q)) j
      (E.result _ [] (E.term functionResultᴵ) ↠-refl
        (E.value functionResultᴵ)) callResultᴾ
  → j ≡ k
  → PairedReturns W₀ (FutureValueRelation q) k functionResultᴵ
      (sequence-type-application-result functionResultᴾ callResultᴾ)
assemble-right-type-application-pair {W₀ = W₀} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {q = q} {functionResultᴾ = functionResultᴾ}
    {functionResultᴵ = functionResultᴵ}
    {Bᴾ = Bᴾ} {Rᴾ = Rᴾ} {callResultᴾ = callResultᴾ}
    W₀≼W₁ functionStoreᴵ functionStoreᴾ
    functionTermsᴵ functionTermsᴾ step
    (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ
      (bound≼W₂ , factors , callValueRelated)) indexEq =
  paired-returns W₂ W₀≼W₂ impreciseStoreEq preciseStoreEq
    impreciseTermsEq preciseTermsEq finalValueRelated
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  impreciseStoreEq = trans callStoreᴵ functionStoreᴵ

  preciseStoreEq = trans callStoreᴾ
    (trans
      (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) functionStoreᴾ)
      (apply-stores-++ (E.changes functionResultᴾ)
        (E.changes callResultᴾ) (preciseStore (core W₀))))

  preciseResult = sequence-type-application-result
    {B = Bᴾ} {A = Rᴾ} functionResultᴾ callResultᴾ

  impreciseTermsEq : ∀ M → E.changes functionResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₂ M
  impreciseTermsEq M = trans (functionTermsᴵ M)
    (trans
      (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
      (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))

  preciseTermsEq : ∀ M → E.changes preciseResult ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₂ M
  preciseTermsEq M = trans
    (sym (apply-terms-++ (E.changes functionResultᴾ)
      (E.changes callResultᴾ) M))
    (trans
      (cong (λ N → E.changes callResultᴾ ▶ᵀ N)
        (functionTermsᴾ M))
      (trans
        (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
        (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  compositeQ = liftCenterImprecision W₀≼W₂ q
  sequentialQ = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ q)

  finalValueRelated = ClosureProof.value-imprecision-reindex
    compositeQ sequentialQ
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴾ)
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴵ)
    (value-index-reindex indexEq callValueRelated)

assemble-type-application-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁ Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {Aᴾ Aᴵ : Ty Δᶜ₀}
    {q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ}
    {Lᴾ : Term Δᴾ₀} {Lᴵ : Term Δᴵ₀}
    {functionResultᴾ : E.EvalResult Lᴾ}
    {functionResultᴵ : E.EvalResult Lᴵ}
    {Bᴾ : Ty (suc Δᴾ₀)} {Bᴵ : Ty (suc Δᴵ₀)}
    {Rᴾ : Ty Δᴾ₀} {Rᴵ : Ty Δᴵ₀}
    {callResultᴾ : E.EvalResult
      (E.term functionResultᴾ
        ⦂∀ applyBodies (E.changes functionResultᴾ) Bᴾ
        [ E.changes functionResultᴾ ▶ᵗ Rᴾ ])}
    {callResultᴵ : E.EvalResult
      (E.term functionResultᴵ
        ⦂∀ applyBodies (E.changes functionResultᴵ) Bᴵ
        [ E.changes functionResultᴵ ▶ᵗ Rᴵ ])}
    {W₁ : World (E.Δ′ functionResultᴾ)
      (E.Δ′ functionResultᴵ) Δᶜ₁}
    {bound : World Δᴾᵇ Δᴵᵇ Δᶜᵇ}
    {j k : ℕ}
  → (W₀≼W₁ : Future W₀ W₁)
  → impreciseStore (core W₁) ≡
      E.changes functionResultᴵ ▶ˢ impreciseStore (core W₀)
  → preciseStore (core W₁) ≡
      E.changes functionResultᴾ ▶ˢ preciseStore (core W₀)
  → (∀ M → E.changes functionResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₁ M)
  → (∀ M → E.changes functionResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₁ M)
  → (step : Future W₁ bound)
  → PairedReturns W₁
      (PostBindValueRelation step
        (liftCenterImprecision W₀≼W₁ q)) j
      callResultᴵ callResultᴾ
  → j ≡ k
  → PairedReturns W₀ (FutureValueRelation q) k
      (sequence-type-application-result functionResultᴵ callResultᴵ)
      (sequence-type-application-result functionResultᴾ callResultᴾ)
assemble-type-application-pair {W₀ = W₀} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {q = q} {functionResultᴾ = functionResultᴾ}
    {functionResultᴵ = functionResultᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
    W₀≼W₁ functionStoreᴵ functionStoreᴾ
    functionTermsᴵ functionTermsᴾ step
    (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
      callTermsᴵ callTermsᴾ
      (bound≼W₂ , factors , callValueRelated)) indexEq =
  paired-returns W₂ W₀≼W₂ impreciseStoreEq preciseStoreEq
    impreciseTermsEq preciseTermsEq finalValueRelated
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂

  impreciseStoreEq = trans callStoreᴵ
    (trans
      (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) functionStoreᴵ)
      (apply-stores-++ (E.changes functionResultᴵ)
        (E.changes callResultᴵ) (impreciseStore (core W₀))))

  preciseStoreEq = trans callStoreᴾ
    (trans
      (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) functionStoreᴾ)
      (apply-stores-++ (E.changes functionResultᴾ)
        (E.changes callResultᴾ) (preciseStore (core W₀))))

  impreciseResult = sequence-type-application-result
    {B = Bᴵ} {A = Rᴵ} functionResultᴵ callResultᴵ

  preciseResult = sequence-type-application-result
    {B = Bᴾ} {A = Rᴾ} functionResultᴾ callResultᴾ

  impreciseTermsEq : ∀ M → E.changes impreciseResult ▶ᵀ M ≡
      liftImpreciseTerm W₀≼W₂ M
  impreciseTermsEq M = trans
    (sym (apply-terms-++ (E.changes functionResultᴵ)
      (E.changes callResultᴵ) M))
    (trans
      (cong (λ N → E.changes callResultᴵ ▶ᵀ N)
        (functionTermsᴵ M))
      (trans
        (callTermsᴵ (liftImpreciseTerm W₀≼W₁ M))
        (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  preciseTermsEq : ∀ M → E.changes preciseResult ▶ᵀ M ≡
      liftPreciseTerm W₀≼W₂ M
  preciseTermsEq M = trans
    (sym (apply-terms-++ (E.changes functionResultᴾ)
      (E.changes callResultᴾ) M))
    (trans
      (cong (λ N → E.changes callResultᴾ ▶ᵀ N)
        (functionTermsᴾ M))
      (trans
        (callTermsᴾ (liftPreciseTerm W₀≼W₁ M))
        (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M))))

  compositeQ = liftCenterImprecision W₀≼W₂ q
  sequentialQ = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ q)

  preciseQEq = liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴾ
  impreciseQEq = liftCenterTy-trans W₀≼W₁ W₁≼W₂ Aᴵ

  finalValueRelated = ClosureProof.value-imprecision-reindex
    compositeQ sequentialQ preciseQEq impreciseQEq
    (value-index-reindex indexEq callValueRelated)

------------------------------------------------------------------------
-- Structural type-application compatibility
------------------------------------------------------------------------

type-application-compatible : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ : Ty (suc Δᴾ)} {Cᴵ : Ty (suc Δᴵ)}
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {p : I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Cᴾ
      ⊑ renameᵗ (extᵗ (Consistency.toRenameᵗ
        (impreciseEmbedding (core W)))) Cᴵ}
    {q : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Cᴵ [ Aᴵ ]ᵗ}
    {Lᴾ : Term Δᴾ} {Lᴵ : Term Δᴵ}
  → (∀ k → CompiledTermRelation {W = W} (I.∀⊑∀ p) k
      Γ Lᴾ Lᴵ)
  → ∀ k → CompiledTermRelation {W = W} r k Γ
      (Lᴾ ⦂∀ Cᴾ [ Aᴾ ]) (Lᴵ ⦂∀ Cᴵ [ Aᴵ ])
type-application-compatible {W = W} {Γ = Γ}
    {Cᴾ = Cᴾ} {Cᴵ = Cᴵ} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {p = p} {q = q} {r = r} {Lᴾ = Lᴾ} {Lᴵ = Lᴵ}
    L-related k W′ W≼W′ γ =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ r) (liftCenterImprecision W≼W′ r)
    refl refl (sym imprecise-type-app-eq) (sym precise-type-app-eq)
    (record
      { forward-return = forward
      ; backward-return = backward
      ; forward-blame = forwardBlame
      })
  where
  Lᴵ′ = close (impreciseClosingSubstitution γ)
    (liftImpreciseTerm W≼W′ Lᴵ)
  Lᴾ′ = close (preciseClosingSubstitution γ)
    (liftPreciseTerm W≼W′ Lᴾ)
  Cᴵ′ = liftImpreciseBody W≼W′ Cᴵ
  Cᴾ′ = liftPreciseBody W≼W′ Cᴾ
  Aᴵ′ = liftImpreciseTy W≼W′ Aᴵ
  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ

  imprecise-type-app-eq :
      close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W≼W′ (Lᴵ ⦂∀ Cᴵ [ Aᴵ ])) ≡
      Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ]
  imprecise-type-app-eq = cong
    (close (impreciseClosingSubstitution γ))
    (lift-imprecise-type-application W≼W′ Lᴵ Cᴵ Aᴵ)

  precise-type-app-eq :
      close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Lᴾ ⦂∀ Cᴾ [ Aᴾ ])) ≡
      Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]
  precise-type-app-eq = cong
    (close (preciseClosingSubstitution γ))
    (lift-precise-type-application W≼W′ Lᴾ Cᴾ Aᴾ)

  function-related = L-related k W′ W≼W′ γ

  forward : ∀ {n}
      {resultᴵ : E.EvalResult (Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ])}
    → n ≤ k
    → interpretFrom (impreciseStore (core W′)) n
        (Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ]) ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ]
       Σ[ resultᴾ ∈ E.EvalResult (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ]
         interpretFrom (preciseStore (core W′)) m
           (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ≡ returned resultᴾ
         × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ r))
            (k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W′)) m
          (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]))
  forward {n} n≤k result-eq
      with type-application-return-phases
        {Σ = impreciseStore (core W′)} result-eq
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      with forward-return function-related {n = functionGas}
        functionGas≤ functionReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    functionGas≤ = first-of-two≤ phases≤
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      with type-function-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {B = Cᴾ′} {A = Aᴾ′} preciseFunctionBlame
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-return call-related {n = callGas}
        callGas≤ callPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    callGas≤ = drop-left-≤ phases≤

    residual-positive = ≤-trans
      (type-application-return-positive≤
        {Σ = E.changes functionResult ▶ˢ
          impreciseStore (core W′)} callReturn) callGas≤

    bodyEqᴵ = imprecise-phase-body-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    bodyEqᴾ = precise-phase-body-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′
    argumentEqᴵ = imprecise-phase-argument-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    argumentEqᴾ = precise-phase-argument-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′

    call-related = related-type-call-after-function
      {W₀ = W} {W₁ = W′} {W₂ = W₁}
      {p = p} {r = q} {s = r}
      {Dᴾ = applyBodies (E.changes preciseFunctionResult) Cᴾ′}
      {Dᴵ = applyBodies (E.changes functionResult) Cᴵ′}
      {Sᴾ = E.changes preciseFunctionResult ▶ᵗ Aᴾ′}
      {Sᴵ = E.changes functionResult ▶ᵗ Aᴵ′}
      {Vᴾ = E.term preciseFunctionResult}
      {Vᴵ = E.term functionResult} {k = k ∸ functionGas}
      W≼W′ W′≼W₁
      bodyEqᴾ bodyEqᴵ argumentEqᴾ argumentEqᴵ
      residual-positive functionValueRelated

    callPhaseReturn = return-store-reindex {gas = callGas}
      {M = E.term functionResult ⦂∀
        applyBodies (E.changes functionResult) Cᴵ′
        [ E.changes functionResult ▶ᵗ Aᴵ′ ]}
      functionStoreᴵ callReturn
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      with type-application-call-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {callGas = preciseCallGas} {L = Lᴾ′}
        {B = Cᴾ′} {A = Aᴾ′} preciseFunctionReturn
        (blame-store-reindex {gas = preciseCallGas}
          {M = E.term preciseFunctionResult ⦂∀
            applyBodies (E.changes preciseFunctionResult) Cᴾ′
            [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
          (sym functionStoreᴾ) preciseCallBlame)
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      with type-application-return-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {callGas = preciseCallGas} {L = Lᴾ′}
        {B = Cᴾ′} {A = Aᴾ′}
        preciseFunctionReturn preciseCallPhaseReturn
    where
    preciseCallPhaseReturn = return-store-reindex
      {gas = preciseCallGas}
      {M = E.term preciseFunctionResult ⦂∀
        applyBodies (E.changes preciseFunctionResult) Cᴾ′
        [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
      (sym functionStoreᴾ) preciseCallReturn
  forward {n} n≤k result-eq
      | type-return-phases functionGas functionResult functionReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      | wholeGas , wholeReturn =
    inj₁ (wholeGas , preciseWholeResult , wholeReturn ,
      paired-returns-reindex result-split refl assembledPair)
    where
    preciseWholeResult = sequence-type-application-result
      preciseFunctionResult preciseCallResult

    indexEq = trans (subtract-phases k functionGas callGas)
      (cong (k ∸_) gas-split)

    assembledPair = assemble-type-application-pair
      {W₀ = W′} {q = liftCenterImprecision W≼W′ r}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = functionResult}
      {callResultᴾ = preciseCallResult} {callResultᴵ = callResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ _
      (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ callValueRelated) indexEq

  backward : ∀ {n}
      {resultᴾ : E.EvalResult (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ])}
    → n ≤ k
    → interpretFrom (preciseStore (core W′)) n
        (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ]
      Σ[ resultᴵ ∈ E.EvalResult (Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ]) ]
        interpretFrom (impreciseStore (core W′)) m
          (Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ]) ≡ returned resultᴵ
        × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ r))
            (k ∸ n) resultᴵ resultᴾ
  backward {n} n≤k result-eq
      with type-application-return-phases
        {Σ = preciseStore (core W′)} result-eq
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      with backward-return function-related {n = preciseFunctionGas}
        functionGas≤
        preciseFunctionReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    functionGas≤ = first-of-two≤ phases≤
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      with backward-return call-related {n = preciseCallGas}
        callGas≤ callPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    callGas≤ = drop-left-≤ phases≤

    residual-positive = ≤-trans
      (type-application-return-positive≤
        {Σ = E.changes preciseFunctionResult ▶ˢ
          preciseStore (core W′)} preciseCallReturn) callGas≤

    bodyEqᴵ = imprecise-phase-body-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    bodyEqᴾ = precise-phase-body-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′
    argumentEqᴵ = imprecise-phase-argument-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    argumentEqᴾ = precise-phase-argument-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′

    call-related = related-type-call-after-function
      {W₀ = W} {W₁ = W′} {W₂ = W₁}
      {p = p} {r = q} {s = r}
      {Dᴾ = applyBodies (E.changes preciseFunctionResult) Cᴾ′}
      {Dᴵ = applyBodies (E.changes functionResult) Cᴵ′}
      {Sᴾ = E.changes preciseFunctionResult ▶ᵗ Aᴾ′}
      {Sᴵ = E.changes functionResult ▶ᵗ Aᴵ′}
      {Vᴾ = E.term preciseFunctionResult}
      {Vᴵ = E.term functionResult} {k = k ∸ preciseFunctionGas}
      W≼W′ W′≼W₁
      bodyEqᴾ bodyEqᴵ argumentEqᴾ argumentEqᴵ
      residual-positive functionValueRelated

    callPhaseReturn = return-store-reindex {gas = preciseCallGas}
      {M = E.term preciseFunctionResult ⦂∀
        applyBodies (E.changes preciseFunctionResult) Cᴾ′
        [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
      functionStoreᴾ preciseCallReturn
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | callGas , callResult , callReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      with type-application-return-expand
        {Σ = impreciseStore (core W′)}
        {functionGas = functionGas} {callGas = callGas}
        {L = Lᴵ′} {B = Cᴵ′} {A = Aᴵ′}
        functionReturn callPhaseReturn
    where
    callPhaseReturn = return-store-reindex {gas = callGas}
      {M = E.term functionResult ⦂∀
        applyBodies (E.changes functionResult) Cᴵ′
        [ E.changes functionResult ▶ᵗ Aᴵ′ ]}
      (sym functionStoreᴵ) callReturn
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | callGas , callResult , callReturn ,
          paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      | wholeGas , wholeReturn =
    wholeGas , impreciseWholeResult , wholeReturn ,
      paired-returns-reindex refl result-split assembledPair
    where
    impreciseWholeResult = sequence-type-application-result
      functionResult callResult

    indexEq = trans
      (subtract-phases k preciseFunctionGas preciseCallGas)
      (cong (k ∸_) gas-split)

    assembledPair = assemble-type-application-pair
      {W₀ = W′} {q = liftCenterImprecision W≼W′ r}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = functionResult}
      {callResultᴾ = preciseCallResult} {callResultᴵ = callResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ _
      (paired-returns W₂ W₁≼W₂ callStoreᴵ callStoreᴾ
        callTermsᴵ callTermsᴾ callValueRelated) indexEq

  forwardBlame : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W′)) n
        (Lᴵ′ ⦂∀ Cᴵ′ [ Aᴵ′ ])
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W′)) m
        (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ])
  forwardBlame {n} n≤k blaming
      with type-application-blame-phases
        {Σ = impreciseStore (core W′)} blaming
  forwardBlame {n} n≤k blaming
      | type-function-phase-blames functionGas functionBlame
          functionGas≤
      with forward-blame function-related {n = functionGas}
        (≤-trans functionGas≤ n≤k) functionBlame
  forwardBlame {n} n≤k blaming
      | type-function-phase-blames functionGas functionBlame
          functionGas≤
      | preciseFunctionGas , preciseFunctionBlame
      with type-function-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {B = Cᴾ′} {A = Aᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | type-function-phase-blames functionGas functionBlame
          functionGas≤
      | preciseFunctionGas , preciseFunctionBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      with forward-return function-related {n = functionGas}
        functionGas≤ functionReturn
    where
    functionGas≤ = first-of-two≤ (≤-trans phases≤n n≤k)
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      with type-function-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {B = Cᴾ′} {A = Aᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-blame call-related {n = callGas}
        callGas≤ callPhaseBlame
    where
    phases≤k = ≤-trans phases≤n n≤k
    callGas≤ = drop-left-≤ phases≤k

    residual-positive = ≤-trans
      (type-application-blame-positive≤
        {Σ = E.changes functionResult ▶ˢ
          impreciseStore (core W′)} callBlame) callGas≤

    bodyEqᴵ = imprecise-phase-body-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    bodyEqᴾ = precise-phase-body-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′
    argumentEqᴵ = imprecise-phase-argument-eq
      {χs = E.changes functionResult} W′≼W₁
      functionTermsᴵ Cᴵ′ Aᴵ′
    argumentEqᴾ = precise-phase-argument-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′

    call-related = related-type-call-after-function
      {W₀ = W} {W₁ = W′} {W₂ = W₁}
      {p = p} {r = q} {s = r}
      {Dᴾ = applyBodies (E.changes preciseFunctionResult) Cᴾ′}
      {Dᴵ = applyBodies (E.changes functionResult) Cᴵ′}
      {Sᴾ = E.changes preciseFunctionResult ▶ᵗ Aᴾ′}
      {Sᴵ = E.changes functionResult ▶ᵗ Aᴵ′}
      {Vᴾ = E.term preciseFunctionResult}
      {Vᴵ = E.term functionResult} {k = k ∸ functionGas}
      W≼W′ W′≼W₁
      bodyEqᴾ bodyEqᴵ argumentEqᴾ argumentEqᴵ
      residual-positive functionValueRelated

    callPhaseBlame = blame-store-reindex {gas = callGas}
      {M = E.term functionResult ⦂∀
        applyBodies (E.changes functionResult) Cᴵ′
        [ E.changes functionResult ▶ᵗ Aᴵ′ ]}
      functionStoreᴵ callBlame
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | preciseCallGas , preciseCallBlame
      with type-application-call-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {callGas = preciseCallGas} {L = Lᴾ′}
        {B = Cᴾ′} {A = Aᴾ′} preciseFunctionReturn
        (blame-store-reindex {gas = preciseCallGas}
          {M = E.term preciseFunctionResult ⦂∀
            applyBodies (E.changes preciseFunctionResult) Cᴾ′
            [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
          (sym functionStoreᴾ) preciseCallBlame)
  forwardBlame {n} n≤k blaming
      | type-call-phase-blames functionGas functionResult
          functionReturn callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | preciseCallGas , preciseCallBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame

------------------------------------------------------------------------
-- Asymmetric right type-application compatibility
------------------------------------------------------------------------

right-type-application-compatible : ∀
    {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Cᴾ : Ty (suc Δᴾ)} {Aᴾ : Ty Δᴾ} {Bᴵ : Ty Δᴵ}
    {p : I.instᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Cᴾ
      ⊑ ⇑ᵗ (embedImprecise (core W) Bᴵ)}
    {nonvar : NonVar (renameᵗ (extᵗ (Consistency.toRenameᵗ
      (preciseEmbedding (core W)))) Cᴾ)}
    {occurs : Fin.zero ∈ᵗ renameᵗ
      (extᵗ (Consistency.toRenameᵗ
        (preciseEmbedding (core W)))) Cᴾ}
    {q : Aᴾ ⊑ᵂ⟨ core W ⟩ ★}
    {r : Cᴾ [ Aᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Bᴵ}
    {Lᴾ : Term Δᴾ} {Lᴵ : Term Δᴵ}
  → (∀ k → CompiledTermRelation {W = W}
      (I.∀⊑ nonvar occurs p) k Γ Lᴾ Lᴵ)
  → ∀ k → CompiledTermRelation {W = W} r k Γ
      (Lᴾ ⦂∀ Cᴾ [ Aᴾ ]) Lᴵ
right-type-application-compatible {W = W} {Γ = Γ}
    {Cᴾ = Cᴾ} {Aᴾ = Aᴾ} {Bᴵ = Bᴵ}
    {p = p} {nonvar = nonvar} {occurs = occurs}
    {q = q} {r = r} {Lᴾ = Lᴾ} {Lᴵ = Lᴵ}
    L-related k W′ W≼W′ γ =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ r) (liftCenterImprecision W≼W′ r)
    refl refl refl (sym precise-type-app-eq)
    (record
      { forward-return = forward
      ; backward-return = backward
      ; forward-blame = forwardBlame
      })
  where
  Lᴵ′ = close (impreciseClosingSubstitution γ)
    (liftImpreciseTerm W≼W′ Lᴵ)
  Lᴾ′ = close (preciseClosingSubstitution γ)
    (liftPreciseTerm W≼W′ Lᴾ)
  Cᴾ′ = liftPreciseBody W≼W′ Cᴾ
  Aᴾ′ = liftPreciseTy W≼W′ Aᴾ

  precise-type-app-eq :
      close (preciseClosingSubstitution γ)
        (liftPreciseTerm W≼W′ (Lᴾ ⦂∀ Cᴾ [ Aᴾ ])) ≡
      Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]
  precise-type-app-eq = cong
    (close (preciseClosingSubstitution γ))
    (lift-precise-type-application W≼W′ Lᴾ Cᴾ Aᴾ)

  function-related = L-related k W′ W≼W′ γ

  forward : ∀ {n} {resultᴵ : E.EvalResult Lᴵ′}
    → n ≤ k
    → interpretFrom (impreciseStore (core W′)) n Lᴵ′
        ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ]
       Σ[ resultᴾ ∈ E.EvalResult (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ]
         interpretFrom (preciseStore (core W′)) m
           (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ≡ returned resultᴾ
         × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ r))
            (k ∸ n) resultᴵ resultᴾ)
      ⊎ (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W′)) m
          (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]))
  forward {n} {resultᴵ} n≤k result-eq
      with forward-return function-related n≤k result-eq
  forward {n} {resultᴵ} n≤k result-eq
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      with type-function-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {B = Cᴾ′} {A = Aᴾ′} preciseFunctionBlame
  forward {n} {resultᴵ} n≤k result-eq
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} {resultᴵ} n≤k result-eq
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-return call-related z≤n callReturnᴵ
    where
    bodyEqᴾ = precise-phase-body-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′
    argumentEqᴾ = precise-phase-argument-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′

    call-related = right-type-call-after-function
      {W₀ = W} {W₁ = W′} {W₂ = W₁}
      {p = p} {nonvar = nonvar} {occurs = occurs} {s = r}
      {Dᴾ = applyBodies (E.changes preciseFunctionResult) Cᴾ′}
      {Sᴾ = E.changes preciseFunctionResult ▶ᵗ Aᴾ′}
      {Vᴾ = E.term preciseFunctionResult}
      {Vᴵ = E.term resultᴵ} {k = k ∸ n}
      W≼W′ W′≼W₁ bodyEqᴾ argumentEqᴾ functionValueRelated

    callReturnᴵ = value-return-exact
      {Σ = impreciseStore (core W₁)} zero (E.value resultᴵ)
  forward {n} {resultᴵ} n≤k result-eq
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      with type-application-call-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {callGas = preciseCallGas} {L = Lᴾ′}
        {B = Cᴾ′} {A = Aᴾ′} preciseFunctionReturn
        (blame-store-reindex {gas = preciseCallGas}
          {M = E.term preciseFunctionResult ⦂∀
            applyBodies (E.changes preciseFunctionResult) Cᴾ′
            [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
          (sym functionStoreᴾ) preciseCallBlame)
  forward {n} {resultᴵ} n≤k result-eq
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} {resultᴵ} n≤k result-eq
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          callPair)
      with type-application-return-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {callGas = preciseCallGas} {L = Lᴾ′}
        {B = Cᴾ′} {A = Aᴾ′}
        preciseFunctionReturn preciseCallPhaseReturn
    where
    preciseCallPhaseReturn = return-store-reindex
      {gas = preciseCallGas}
      {M = E.term preciseFunctionResult ⦂∀
        applyBodies (E.changes preciseFunctionResult) Cᴾ′
        [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
      (sym functionStoreᴾ) preciseCallReturn
  forward {n} {resultᴵ} n≤k result-eq
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          callPair)
      | wholeGas , wholeReturn =
    inj₁ (wholeGas , preciseWholeResult , wholeReturn , assembledPair)
    where
    preciseWholeResult = sequence-type-application-result
      preciseFunctionResult preciseCallResult

    assembledPair = assemble-right-type-application-pair
      {W₀ = W′} {q = liftCenterImprecision W≼W′ r}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = resultᴵ}
      {callResultᴾ = preciseCallResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ _ callPair refl

  backward : ∀ {n}
      {resultᴾ : E.EvalResult (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ])}
    → n ≤ k
    → interpretFrom (preciseStore (core W′)) n
        (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ]) ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ]
      Σ[ resultᴵ ∈ E.EvalResult Lᴵ′ ]
        interpretFrom (impreciseStore (core W′)) m Lᴵ′
          ≡ returned resultᴵ
        × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ r))
            (k ∸ n) resultᴵ resultᴾ
  backward {n} n≤k result-eq
      with type-application-return-phases
        {Σ = preciseStore (core W′)} result-eq
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      with backward-return function-related {n = preciseFunctionGas}
        functionGas≤ preciseFunctionReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    functionGas≤ = first-of-two≤ phases≤
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      with backward-return call-related {n = preciseCallGas}
        callGas≤ callPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    callGas≤ = drop-left-≤ phases≤

    bodyEqᴾ = precise-phase-body-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′
    argumentEqᴾ = precise-phase-argument-eq
      {χs = E.changes preciseFunctionResult} W′≼W₁
      functionTermsᴾ Cᴾ′ Aᴾ′

    call-related = right-type-call-after-function
      {W₀ = W} {W₁ = W′} {W₂ = W₁}
      {p = p} {nonvar = nonvar} {occurs = occurs} {s = r}
      {Dᴾ = applyBodies (E.changes preciseFunctionResult) Cᴾ′}
      {Sᴾ = E.changes preciseFunctionResult ▶ᵗ Aᴾ′}
      {Vᴾ = E.term preciseFunctionResult}
      {Vᴵ = E.term functionResult}
      {k = k ∸ preciseFunctionGas}
      W≼W′ W′≼W₁ bodyEqᴾ argumentEqᴾ functionValueRelated

    callPhaseReturn = return-store-reindex {gas = preciseCallGas}
      {M = E.term preciseFunctionResult ⦂∀
        applyBodies (E.changes preciseFunctionResult) Cᴾ′
        [ E.changes preciseFunctionResult ▶ᵗ Aᴾ′ ]}
      functionStoreᴾ preciseCallReturn
  backward {n} n≤k result-eq
      | type-return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | callGas , callResult , callReturn , callPair =
    functionGas , functionResult , functionReturn ,
      paired-returns-reindex refl result-split assembledPair
    where
    exactCallResult = E.result _ [] (E.term functionResult) ↠-refl
      (E.value functionResult)

    callResultEq : callResult ≡ exactCallResult
    callResultEq = returned-injective
      (trans (sym callReturn)
        (value-return-exact {Σ = impreciseStore (core W₁)}
          callGas (E.value functionResult)))

    exactCallPair = paired-returns-reindex
      (sym callResultEq) refl callPair

    indexEq = trans
      (subtract-phases k preciseFunctionGas preciseCallGas)
      (cong (k ∸_) gas-split)

    assembledPair = assemble-right-type-application-pair
      {W₀ = W′} {q = liftCenterImprecision W≼W′ r}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = functionResult}
      {callResultᴾ = preciseCallResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ _ exactCallPair indexEq

  forwardBlame : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W′)) n Lᴵ′
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W′)) m
        (Lᴾ′ ⦂∀ Cᴾ′ [ Aᴾ′ ])
  forwardBlame {n} n≤k blaming
      with forward-blame function-related n≤k blaming
  forwardBlame {n} n≤k blaming
      | preciseFunctionGas , preciseFunctionBlame
      with type-function-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {B = Cᴾ′} {A = Aᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | preciseFunctionGas , preciseFunctionBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame
