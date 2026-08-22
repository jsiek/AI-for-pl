module proof.LR-narrow.Application where

-- File Charter:
--   * Proves compatibility of the CTI application constructor.
--   * Decomposes call-by-value application runs into function, argument, and
--     value-application phases.
--   * Threads the future worlds produced by the two component computations.

open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-assoc; m∸n≤m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.TermSubstitution using (subst-cong)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import Reduction
import Eval as E
open import Interpreter
import Imprecision as I
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.FunctionApplication
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete; value-eval; value-return)
open import proof.LR-narrow.BetaExpansion using
  (value-step-none; interpreter-outcome; interpret-from-eval)
open import proof.TypeInTermSubst using (renameᵗᵐ-preserves-Value)
import proof.LR-narrow.Closure as ClosureProof
import proof.LR-narrow.ClosingSubstitution as ClosingProof

------------------------------------------------------------------------
-- Evaluator phase packages
------------------------------------------------------------------------

apply-change-value : ∀ {Δ Δ′} (χ : StoreChange Δ Δ′)
    {V : Term Δ}
  → Value V
  → Value (χ ▷ᵀ V)
apply-change-value keep vV = vV
apply-change-value (bind A) vV = renameᵗᵐ-preserves-Value _ vV

lift-imprecise-application : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (L M : Term Δᴵ₀)
  → liftImpreciseTerm W₀≼W₁ (L · M) ≡
      liftImpreciseTerm W₀≼W₁ L · liftImpreciseTerm W₀≼W₁ M
lift-imprecise-application future-refl L M = refl
lift-imprecise-application (future-paired W₀≼W₁ related fresh) L M
    rewrite lift-imprecise-application W₀≼W₁ L M = refl
lift-imprecise-application (future-precise W₀≼W₁ fresh) L M =
  lift-imprecise-application W₀≼W₁ L M

lift-precise-application : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    (W₀≼W₁ : Future W₀ W₁) (L M : Term Δᴾ₀)
  → liftPreciseTerm W₀≼W₁ (L · M) ≡
      liftPreciseTerm W₀≼W₁ L · liftPreciseTerm W₀≼W₁ M
lift-precise-application future-refl L M = refl
lift-precise-application (future-paired W₀≼W₁ related fresh) L M
    rewrite lift-precise-application W₀≼W₁ L M = refl
lift-precise-application (future-precise W₀≼W₁ fresh) L M
    rewrite lift-precise-application W₀≼W₁ L M = refl

gen-safe-unique : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (safe safe′ : GenSafe c)
  → safe ≡ safe′
gen-safe-unique safe-⇒ safe-⇒ = refl
gen-safe-unique safe-∀ safe-∀ = refl
gen-safe-unique (safe-inst B≢★) (safe-inst B≢★′) = refl
gen-safe-unique (safe-gen A≢★ safe) (safe-gen A≢★′ safe′)
    rewrite gen-safe-unique safe safe′ = refl

inert-unique : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    {c : μ ⊢ A ∼ B}
  → (inert inert′ : Inert c)
  → inert ≡ inert′
inert-unique inj inj = refl
inert-unique fun fun = refl
inert-unique all all = refl
inert-unique (genᵥ A≢★ safe) (genᵥ A≢★′ safe′)
    rewrite gen-safe-unique safe safe′ = refl

reveal-value-unique : ∀ {Δ A B} {c : Conv↑ Δ A B}
  → (reveal reveal′ : RevealValue c)
  → reveal ≡ reveal′
reveal-value-unique fun fun = refl
reveal-value-unique all all = refl

conceal-value-unique : ∀ {Δ A B} {c : Conv↓ Δ A B}
  → (conceal conceal′ : ConcealValue c)
  → conceal ≡ conceal′
conceal-value-unique seal seal = refl
conceal-value-unique fun fun = refl
conceal-value-unique all all = refl

wrapped-value-cong : ∀ {Δ : TyCtx} {μ : Env∼ Δ} {A B : Ty Δ}
    {V : Term Δ} {c : μ ⊢ A ∼ B}
    {vV vV′ : Value V} {inert inert′ : Inert c}
  → vV ≡ vV′
  → inert ≡ inert′
  → (vV 《 inert 》) ≡ (vV′ 《 inert′ 》)
wrapped-value-cong refl refl = refl

revealed-value-cong : ∀ {Δ A B} {V : Term Δ} {c : Conv↑ Δ A B}
    {vV vV′ : Value V} {reveal reveal′ : RevealValue c}
  → vV ≡ vV′
  → reveal ≡ reveal′
  → (vV ↑ reveal) ≡ (vV′ ↑ reveal′)
revealed-value-cong refl refl = refl

concealed-value-cong : ∀ {Δ A B} {V : Term Δ} {c : Conv↓ Δ A B}
    {vV vV′ : Value V} {conceal conceal′ : ConcealValue c}
  → vV ≡ vV′
  → conceal ≡ conceal′
  → (vV ↓ conceal) ≡ (vV′ ↓ conceal′)
concealed-value-cong refl refl = refl

value-unique : ∀ {Δ} {V : Term Δ}
  → (vV vV′ : Value V)
  → vV ≡ vV′
value-unique (ƛ N) (ƛ .N) = refl
value-unique (Λ vV) (Λ vV′) rewrite value-unique vV vV′ = refl
value-unique ($ κ) ($ .κ) = refl
value-unique (vV 《 inert 》) (vV′ 《 inert′ 》) =
  wrapped-value-cong (value-unique vV vV′) (inert-unique inert inert′)
value-unique (vV ↑ reveal) (vV′ ↑ reveal′) =
  revealed-value-cong (value-unique vV vV′)
    (reveal-value-unique reveal reveal′)
value-unique (vV ↓ conceal) (vV′ ↓ conceal′) =
  concealed-value-cong (value-unique vV vV′)
    (conceal-value-unique conceal conceal′)

_++ˢ_ : ∀ {Δ₀ Δ₁ Δ₂}
  → StoreChanges Δ₀ Δ₁
  → StoreChanges Δ₁ Δ₂
  → StoreChanges Δ₀ Δ₂
[] ++ˢ ψs = ψs
(χ ∷ χs) ++ˢ ψs = χ ∷ (χs ++ˢ ψs)

apply-stores-++ : ∀ {Δ₀ Δ₁ Δ₂}
    (χs : StoreChanges Δ₀ Δ₁) (ψs : StoreChanges Δ₁ Δ₂)
    (Σ : TyStore Δ₀)
  → ψs ▶ˢ (χs ▶ˢ Σ) ≡ (χs ++ˢ ψs) ▶ˢ Σ
apply-stores-++ [] ψs Σ = refl
apply-stores-++ (χ ∷ χs) ψs Σ =
  apply-stores-++ χs ψs (χ ▷ˢ Σ)

apply-terms-++ : ∀ {Δ₀ Δ₁ Δ₂}
    (χs : StoreChanges Δ₀ Δ₁) (ψs : StoreChanges Δ₁ Δ₂)
    (M : Term Δ₀)
  → ψs ▶ᵀ (χs ▶ᵀ M) ≡ (χs ++ˢ ψs) ▶ᵀ M
apply-terms-++ [] ψs M = refl
apply-terms-++ (χ ∷ χs) ψs M =
  apply-terms-++ χs ψs (χ ▷ᵀ M)

append-trace : ∀ {Δ₀ Δ₁ Δ₂} {M : Term Δ₀} {N : Term Δ₁}
    {P : Term Δ₂} {χs : StoreChanges Δ₀ Δ₁}
    {ψs : StoreChanges Δ₁ Δ₂}
  → M —↠[ χs ] N
  → N —↠[ ψs ] P
  → M —↠[ χs ++ˢ ψs ] P
append-trace ↠-refl N↠P = N↠P
append-trace (↠-step M→N M↠N) N↠P =
  ↠-step M→N (append-trace M↠N N↠P)

application-function-trace : ∀ {Δ₀ Δ₁}
    {L : Term Δ₀} {V : Term Δ₁} {M : Term Δ₀}
    {χs : StoreChanges Δ₀ Δ₁}
  → L —↠[ χs ] V
  → L · M —↠[ χs ] V · (χs ▶ᵀ M)
application-function-trace ↠-refl = ↠-refl
application-function-trace {M = M}
    (↠-step {χ = χ} L→N N↠V) =
  ↠-step (ξ-·₁ L→N refl)
    (application-function-trace {M = χ ▷ᵀ M} N↠V)

application-argument-trace : ∀ {Δ₀ Δ₁}
    {V M : Term Δ₀} {U : Term Δ₁}
    {χs : StoreChanges Δ₀ Δ₁}
  → (vV : Value V)
  → M —↠[ χs ] U
  → V · M —↠[ χs ] (χs ▶ᵀ V) · U
application-argument-trace vV ↠-refl = ↠-refl
application-argument-trace {V = V}
    vV (↠-step {χ = χ} M→N N↠U) =
  ↠-step (ξ-·₂ vV M→N refl)
    (application-argument-trace (apply-change-value χ vV) N↠U)

sequence-argument-result : ∀ {Δ₀} {V M : Term Δ₀}
  → Value V
  → (argumentResult : E.EvalResult M)
  → E.EvalResult
      ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult)
  → E.EvalResult (V · M)
sequence-argument-result vV
    (E.result Δ₁ χs U M↠U vU)
    (E.result Δ₂ ψs Z call↠Z vZ) =
  E.result Δ₂ (χs ++ˢ ψs) Z
    (append-trace (application-argument-trace vV M↠U) call↠Z) vZ

sequence-argument-result-value-cong : ∀ {Δ} {V M : Term Δ}
    {vV vV′ : Value V} {argumentResult : E.EvalResult M}
    {callResult : E.EvalResult
      ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult)}
  → vV ≡ vV′
  → sequence-argument-result vV argumentResult callResult ≡
      sequence-argument-result vV′ argumentResult callResult
sequence-argument-result-value-cong refl = refl

sequence-application-result : ∀ {Δ₀} {L M : Term Δ₀}
  → (functionResult : E.EvalResult L)
  → (argumentResult :
      E.EvalResult (E.changes functionResult ▶ᵀ M))
  → E.EvalResult
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult)
  → E.EvalResult (L · M)
sequence-application-result
    (E.result Δ₁ χs V L↠V vV)
    (E.result Δ₂ ψs U M↠U vU)
    (E.result Δ₃ θs Z call↠Z vZ) =
  E.result Δ₃ (χs ++ˢ (ψs ++ˢ θs)) Z
    (append-trace (application-function-trace L↠V)
      (append-trace (application-argument-trace vV M↠U) call↠Z))
    vZ

prepend-result : ∀ {Δ Δ′} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N
  → E.EvalResult N
  → E.EvalResult M
prepend-result step (E.result Δ″ changes V trace vV) =
  E.result Δ″ (_ ∷ changes) V (↠-step step trace) vV

prepend-blame : ∀ {Δ Δ′ Δ″} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N
  → (changes : StoreChanges Δ′ Δ″)
  → N —↠[ changes ] blame
  → M —↠[ χ ∷ changes ] blame
prepend-blame step changes trace = ↠-step step trace

prepend-eval-outcome : ∀ {Δ Δ′} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′}
  → M —→[ χ ] N
  → E.EvalOutcome N
  → E.EvalOutcome M
prepend-eval-outcome step (E.returned next-result) =
  E.returned (prepend-result step next-result)
prepend-eval-outcome step (E.blamed changes trace) =
  E.blamed (_ ∷ changes) (prepend-blame step changes trace)

eval-nonblame : ∀ {Δ}
  → TyStore Δ
  → ℕ
  → (M : Term Δ)
  → Maybe.Maybe (E.EvalOutcome M)
eval-nonblame Σ zero M with E.value? M
eval-nonblame Σ zero M | just vM =
  just (E.returned (E.result _ [] M ↠-refl vM))
eval-nonblame Σ zero M | nothing = nothing
eval-nonblame Σ (suc gas) M with E.value? M
eval-nonblame Σ (suc gas) M | just vM =
  just (E.returned (E.result _ [] M ↠-refl vM))
eval-nonblame Σ (suc gas) M | nothing with E.step? Σ M
eval-nonblame Σ (suc gas) M | nothing | nothing = nothing
eval-nonblame Σ (suc gas) M
    | nothing | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-nonblame Σ (suc gas) M
    | nothing | just (E.step-result χ N step) | nothing = nothing
eval-nonblame Σ (suc gas) M
    | nothing | just (E.step-result χ N step)
    | just next-outcome = just (prepend-eval-outcome step next-outcome)

eval-from-nonblame : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ}
  → M ≢ blame
  → E.evalFrom Σ gas M ≡ eval-nonblame Σ gas M
eval-from-nonblame {gas = zero} {M = ` x} M≢blame = refl
eval-from-nonblame {gas = suc gas} {M = ` x} M≢blame = refl
eval-from-nonblame {gas = zero} {M = ƛ N} M≢blame = refl
eval-from-nonblame {gas = suc gas} {M = ƛ N} M≢blame = refl
eval-from-nonblame {gas = zero} {M = L · M} M≢blame = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = L · M} M≢blame
    with E.step? Σ (L · M)
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = L · M} M≢blame
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {gas = zero} {M = Λ N} M≢blame
    with E.value? N
eval-from-nonblame M≢blame | just vN = refl
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {gas = suc gas} {M = Λ N} M≢blame
    with E.value? N
eval-from-nonblame M≢blame | just vN = refl
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {gas = zero} {M = L ⦂∀ B [ A ]} M≢blame = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = L ⦂∀ B [ A ]}
    M≢blame with E.step? Σ (L ⦂∀ B [ A ])
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas}
    {M = L ⦂∀ B [ A ]} M≢blame
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {gas = zero} {M = $ κ} M≢blame = refl
eval-from-nonblame {gas = suc gas} {M = $ κ} M≢blame = refl
eval-from-nonblame {gas = zero} {M = L ⊕[ op ] M} M≢blame = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = L ⊕[ op ] M}
    M≢blame with E.step? Σ (L ⊕[ op ] M)
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas}
    {M = L ⊕[ op ] M} M≢blame
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step) | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {gas = zero} {M = M ⟨ c ⟩} M≢blame
    with E.value? M
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {gas = zero} {M = M ⟨ c ⟩} M≢blame
    | just vM with E.inert? c
eval-from-nonblame M≢blame | just vM | just inert = refl
eval-from-nonblame M≢blame | just vM | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame with E.value? M
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame | nothing with E.step? Σ (M ⟨ c ⟩)
eval-from-nonblame M≢blame | nothing | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame | nothing | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame | just vM with E.inert? c
eval-from-nonblame M≢blame | just vM | just inert = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame | just vM | nothing with E.step? Σ (M ⟨ c ⟩)
eval-from-nonblame M≢blame | just vM | nothing | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ⟨ c ⟩}
    M≢blame | just vM | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | just vM | nothing | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | just vM | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | just vM | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {gas = zero} {M = M ↑ c} M≢blame
    with E.value? (M ↑ c)
eval-from-nonblame M≢blame | just vM = refl
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↑ c} M≢blame
    with E.value? (M ↑ c)
eval-from-nonblame M≢blame | just vM = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↑ c} M≢blame
    | nothing with E.step? Σ (M ↑ c)
eval-from-nonblame M≢blame | nothing | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↑ c} M≢blame
    | nothing | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {gas = zero} {M = M ↓ c} M≢blame
    with E.value? (M ↓ c)
eval-from-nonblame M≢blame | just vM = refl
eval-from-nonblame M≢blame | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↓ c} M≢blame
    with E.value? (M ↓ c)
eval-from-nonblame M≢blame | just vM = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↓ c} M≢blame
    | nothing with E.step? Σ (M ↓ c)
eval-from-nonblame M≢blame | nothing | nothing = refl
eval-from-nonblame {Σ = Σ} {gas = suc gas} {M = M ↓ c} M≢blame
    | nothing | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step) | nothing = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) = refl
eval-from-nonblame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace) = refl
eval-from-nonblame {M = blame} M≢blame = ⊥-elim (M≢blame refl)

data BlameView {Δ : TyCtx} (M : Term Δ) : Set where
  is-blame : M ≡ blame → BlameView M
  not-blame : M ≢ blame → BlameView M

blame-view : ∀ {Δ : TyCtx} (M : Term Δ) → BlameView M
blame-view (` x) = not-blame (λ ())
blame-view (ƛ N) = not-blame (λ ())
blame-view (L · M) = not-blame (λ ())
blame-view (Λ N) = not-blame (λ ())
blame-view (L ⦂∀ B [ A ]) = not-blame (λ ())
blame-view ($ κ) = not-blame (λ ())
blame-view (L ⊕[ op ] M) = not-blame (λ ())
blame-view (M ⟨ c ⟩) = not-blame (λ ())
blame-view (M ↑ c) = not-blame (λ ())
blame-view (M ↓ c) = not-blame (λ ())
blame-view blame = is-blame refl

eval-application-prepend-return : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {L M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    {gas : ℕ} {step : L · M —→[ χ ] N}
    {next-result : E.EvalResult N}
  → E.step? Σ (L · M) ≡ just (E.step-result χ N step)
  → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.returned next-result)
  → E.evalFrom Σ (suc gas) (L · M) ≡
      just (E.returned (prepend-result step next-result))
eval-application-prepend-return step-eq next-eq
    rewrite step-eq | next-eq = refl

app-argument-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {V M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    {step : M —→[ χ ] N}
  → (vV : Value V)
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V · M) ≡
        just (E.step-result χ ((χ ▷ᵀ V) · N)
          (ξ-·₂ vV′ step refl))
app-argument-step-question {Σ = Σ} {V = V} {M = M}
    {χ = χ} {N = N} vV argument-step-eq
    with value-question-complete vV | value-step-none {Σ = Σ} vV
app-argument-step-question vV argument-step-eq
    | vV′ , value-eq | function-step-eq
    rewrite function-step-eq | argument-step-eq | value-eq =
  vV′ , refl

argument-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
    {argumentGas callGas : ℕ} {V M : Term Δ}
    {argumentResult : E.EvalResult M}
    {callResult : E.EvalResult
      ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult)}
  → (vV : Value V)
  → E.evalFrom Σ argumentGas M ≡ just (E.returned argumentResult)
  → E.evalFrom (E.changes argumentResult ▶ˢ Σ) callGas
      ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult)
      ≡ just (E.returned callResult)
  → Σ[ wholeGas ∈ ℕ ]
      E.evalFrom Σ wholeGas (V · M) ≡
        just (E.returned
          (sequence-argument-result vV argumentResult callResult))
argument-return-expand-eval {Σ = Σ} {argumentGas = zero}
    {callGas = callGas} {V = V} {M = M} vV argument-eq call-eq
    with blame-view M
argument-return-expand-eval vV argument-eq call-eq
    | is-blame refl with argument-eq
argument-return-expand-eval vV argument-eq call-eq
    | is-blame refl | ()
argument-return-expand-eval {Σ = Σ} {argumentGas = zero}
    {callGas = callGas} {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    | not-blame M≢blame
    with E.value? M in argument-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = M} M≢blame)) argument-eq
argument-return-expand-eval {callGas = callGas} vV argument-eq call-eq
    | not-blame M≢blame | just vM | refl = callGas , call-eq
argument-return-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    with blame-view M
argument-return-expand-eval vV argument-eq call-eq
    | is-blame refl with argument-eq
argument-return-expand-eval vV argument-eq call-eq
    | is-blame refl | ()
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    | not-blame M≢blame
    with E.value? M in argument-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc argumentGas} {M = M} M≢blame)) argument-eq
argument-return-expand-eval {callGas = callGas} vV argument-eq call-eq
    | not-blame M≢blame | just vM | refl = callGas , call-eq
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    with E.step? Σ M in argument-step-eq
argument-return-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | () | nothing
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) argumentGas N in next-eq
argument-return-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    {argumentResult = argumentResult} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with normalized-eq
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    with argument-return-expand-eval {Σ = χ ▷ˢ Σ}
      {argumentGas = argumentGas} {callGas = callGas}
      {V = χ ▷ᵀ V} {M = N} {argumentResult = next-result}
      (apply-change-value χ vV) next-eq call-eq
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | wholeGas , whole-eq
    with app-argument-step-question {Σ = Σ} vV argument-step-eq
argument-return-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M}
    vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | wholeGas , whole-eq | vV′ , application-step-eq
    rewrite value-unique vV′ vV =
  suc wholeGas ,
  eval-application-prepend-return {Σ = Σ} application-step-eq whole-eq
argument-return-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)

app-function-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {L M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    {step : L —→[ χ ] N}
  → E.step? Σ L ≡ just (E.step-result χ N step)
  → E.step? Σ (L · M) ≡
      just (E.step-result χ (N · (χ ▷ᵀ M)) (ξ-·₁ step refl))
app-function-step-question function-step-eq
    rewrite function-step-eq = refl

application-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas argumentGas callGas : ℕ} {L M : Term Δ}
    {functionResult : E.EvalResult L}
    {argumentResult : E.EvalResult
      (E.changes functionResult ▶ᵀ M)}
    {callResult : E.EvalResult
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult)}
  → E.evalFrom Σ functionGas L ≡ just (E.returned functionResult)
  → E.evalFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M) ≡
        just (E.returned argumentResult)
  → E.evalFrom
      (E.changes argumentResult ▶ˢ
        (E.changes functionResult ▶ˢ Σ)) callGas
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult) ≡ just (E.returned callResult)
  → Σ[ wholeGas ∈ ℕ ]
      E.evalFrom Σ wholeGas (L · M) ≡
        just (E.returned
          (sequence-application-result functionResult argumentResult
            callResult))
application-return-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    with blame-view L
application-return-expand-eval function-eq argument-eq call-eq
    | is-blame refl with function-eq
application-return-expand-eval function-eq argument-eq call-eq
    | is-blame refl | ()
application-return-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = L} L≢blame)) function-eq
application-return-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    {callGas = callGas} function-eq argument-eq call-eq
    | not-blame L≢blame | just vL | refl =
  argument-return-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    {callGas = callGas} vL argument-eq call-eq
application-return-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    with blame-view L
application-return-expand-eval function-eq argument-eq call-eq
    | is-blame refl with function-eq
application-return-expand-eval function-eq argument-eq call-eq
    | is-blame refl | ()
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc functionGas} {M = L} L≢blame)) function-eq
application-return-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    {callGas = callGas} function-eq argument-eq call-eq
    | not-blame L≢blame | just vL | refl =
  argument-return-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    {callGas = callGas} vL argument-eq call-eq
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    with E.step? Σ L in function-step-eq
application-return-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | () | nothing
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
application-return-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with normalized-eq
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    with application-return-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {callGas = callGas} {L = N} {M = χ ▷ᵀ M}
      next-eq argument-eq call-eq
application-return-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | wholeGas , whole-eq =
  suc wholeGas , eval-application-prepend-return {Σ = Σ}
    (app-function-step-question {Σ = Σ} function-step-eq) whole-eq
application-return-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)

eval-prepend-return : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
    {step : M —→[ χ ] N} {result : E.EvalResult N}
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.returned result)
  → E.evalFrom Σ (suc gas) M ≡
      just (E.returned (prepend-result step result))
eval-prepend-return {M = ` x} () next-eq
eval-prepend-return {M = ƛ N} () next-eq
eval-prepend-return {Σ = Σ} {M = L · M} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-return {M = Λ N} () next-eq
eval-prepend-return {Σ = Σ} {M = L ⦂∀ B [ A ]} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-return {M = $ κ} () next-eq
eval-prepend-return {Σ = Σ} {M = L ⊕[ op ] M} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-return {Σ = Σ} {M = M ⟨ c ⟩} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    with E.value? (M ⟨ c ⟩)
eval-prepend-return {Σ = Σ} {M = M ⟨ c ⟩} step-eq next-eq
    | just vM with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-return step-eq next-eq | just vM | ()
eval-prepend-return step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-return {Σ = Σ} {M = M ↑ c} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    with E.value? (M ↑ c)
eval-prepend-return {Σ = Σ} {M = M ↑ c} step-eq next-eq
    | just vM with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-return step-eq next-eq | just vM | ()
eval-prepend-return step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-return {Σ = Σ} {M = M ↓ c} {χ = χ} {N = N}
    {gas = gas} {step = step} step-eq next-eq
    with E.value? (M ↓ c)
eval-prepend-return {Σ = Σ} {M = M ↓ c} step-eq next-eq
    | just vM with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-return step-eq next-eq | just vM | ()
eval-prepend-return step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-return {M = blame} () next-eq

eval-prepend-blamed : ∀ {Δ Δ′ Δ″} {Σ : TyStore Δ} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
    {step : M —→[ χ ] N} {changes : StoreChanges Δ′ Δ″}
    {trace : N —↠[ changes ] blame}
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.blamed changes trace)
  → E.evalFrom Σ (suc gas) M ≡
      just (E.blamed (χ ∷ changes) (↠-step step trace))
eval-prepend-blamed {M = ` x} () next-eq
eval-prepend-blamed {M = ƛ N} () next-eq
eval-prepend-blamed {Σ = Σ} {M = L · M} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {M = Λ N} () next-eq
eval-prepend-blamed {Σ = Σ} {M = L ⦂∀ B [ A ]} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {M = $ κ} () next-eq
eval-prepend-blamed {Σ = Σ} {M = L ⊕[ op ] M} step-eq next-eq
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {Σ = Σ} {M = M ⟨ c ⟩} step-eq next-eq
    with E.value? (M ⟨ c ⟩)
eval-prepend-blamed {Σ = Σ} step-eq next-eq | just vM
    with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-blamed step-eq next-eq | just vM | ()
eval-prepend-blamed step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {Σ = Σ} {M = M ↑ c} step-eq next-eq
    with E.value? (M ↑ c)
eval-prepend-blamed {Σ = Σ} step-eq next-eq | just vM
    with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-blamed step-eq next-eq | just vM | ()
eval-prepend-blamed step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {Σ = Σ} {M = M ↓ c} step-eq next-eq
    with E.value? (M ↓ c)
eval-prepend-blamed {Σ = Σ} step-eq next-eq | just vM
    with trans (sym (value-step-none {Σ = Σ} vM)) step-eq
eval-prepend-blamed step-eq next-eq | just vM | ()
eval-prepend-blamed step-eq next-eq | nothing
    rewrite step-eq | next-eq = refl
eval-prepend-blamed {M = blame} () next-eq

prepend-return : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
    {step : M —→[ χ ] N} {result : E.EvalResult N}
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → interpretFrom (χ ▷ˢ Σ) gas N ≡ returned result
  → interpretFrom Σ (suc gas) M ≡
      returned (prepend-result step result)
prepend-return {Σ = Σ} {M = M} {χ = χ} {N = N} {gas = gas}
    {step = step} {result = result} step-eq next-eq
    with E.evalFrom (χ ▷ˢ Σ) gas N in eval-eq
prepend-return step-eq next-eq | nothing with next-eq
prepend-return step-eq next-eq | nothing | ()
prepend-return {result = result} step-eq next-eq
    | just (E.returned result′)
    with next-eq
prepend-return {Σ = Σ} {M = M} {gas = gas}
    step-eq next-eq | just (E.returned result) | refl
    = trans (interpret-from-eval {Σ = Σ} {gas = suc gas} {M = M})
        (cong (interpreter-outcome {M = M})
          (eval-prepend-return {Σ = Σ} {M = M} {gas = gas}
            step-eq eval-eq))
prepend-return step-eq next-eq | just (E.blamed changes trace)
    with next-eq
prepend-return step-eq next-eq | just (E.blamed changes trace) | ()

return-from-eval : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {result : E.EvalResult M}
  → E.evalFrom Σ gas M ≡ just (E.returned result)
  → interpretFrom Σ gas M ≡ returned result
return-from-eval {Σ = Σ} {gas = gas} {M = M} eval-eq =
  trans (interpret-from-eval {Σ = Σ} {gas = gas} {M = M})
    (cong (interpreter-outcome {M = M}) eval-eq)

eval-from-return : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {result : E.EvalResult M}
  → interpretFrom Σ gas M ≡ returned result
  → E.evalFrom Σ gas M ≡ just (E.returned result)
eval-from-return {Σ = Σ} {gas = gas} {M = M} {result = result}
    result-eq with E.evalFrom Σ gas M
eval-from-return result-eq | nothing with result-eq
eval-from-return result-eq | nothing | ()
eval-from-return {result = result} result-eq
    | just (E.returned result′) with result-eq
eval-from-return result-eq | just (E.returned result) | refl = refl
eval-from-return result-eq | just (E.blamed changes trace) with result-eq
eval-from-return result-eq | just (E.blamed changes trace) | ()

value-return-exact : ∀ {Δ} {Σ : TyStore Δ} {V : Term Δ}
    (gas : ℕ) (vV : Value V)
  → interpretFrom Σ gas V ≡
      returned (E.result Δ [] V ↠-refl vV)
value-return-exact {Σ = Σ} gas vV
    with value-return {Σ = Σ} gas vV
value-return-exact gas vV | vV′ , return-eq
    rewrite value-unique vV′ vV = return-eq

record ArgumentReturnPhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (V M : Term Δ)
    (wholeResult : E.EvalResult (V · M)) : Set where
  constructor argument-return-phases-record
  field
    argumentFunctionValue′ : Value V

    argumentGas′ : ℕ
    argumentResult′ : E.EvalResult M
    argumentReturn′ :
      interpretFrom Σ argumentGas′ M ≡ returned argumentResult′

    callGas′ : ℕ
    callResult′ : E.EvalResult
      ((E.changes argumentResult′ ▶ᵀ V) · E.term argumentResult′)
    callReturn′ :
      interpretFrom (E.changes argumentResult′ ▶ˢ Σ) callGas′
        ((E.changes argumentResult′ ▶ᵀ V)
          · E.term argumentResult′) ≡ returned callResult′

    argument-result-splits : wholeResult ≡
      sequence-argument-result argumentFunctionValue′ argumentResult′
        callResult′

    argument-gas-splits : argumentGas′ + callGas′ ≡ gas

open ArgumentReturnPhases public

app-value-final-none : ∀ {Δ : TyCtx} {V M : Term Δ}
    (vV : Value V)
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.app-value-final? vV M ≡ nothing
app-value-final-none {M = ` x} vV M≢blame eq = refl
app-value-final-none {M = ƛ N} vV M≢blame ()
app-value-final-none {M = L · M} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = Λ N} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = L ⦂∀ B [ A ]} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = $ κ} vV M≢blame ()
app-value-final-none {M = L ⊕[ op ] M} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = M ⟨ c ⟩} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = M ↑ c} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = M ↓ c} vV M≢blame eq rewrite eq = refl
app-value-final-none {M = blame} vV M≢blame eq = ⊥-elim (M≢blame refl)

app-final-none : ∀ {Δ : TyCtx} {V M : Term Δ}
    (vV : Value V)
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.app-final? V M ≡ nothing
app-final-none (ƛ N) M≢blame argument-value-eq =
  app-value-final-none (ƛ N) M≢blame argument-value-eq
app-final-none (Λ vV) M≢blame argument-value-eq
    with value-question-complete vV
app-final-none (Λ vV) M≢blame argument-value-eq | vV′ , value-eq
    rewrite value-eq =
  app-value-final-none (Λ vV′) M≢blame argument-value-eq
app-final-none ($ κ) M≢blame argument-value-eq =
  app-value-final-none ($ κ) M≢blame argument-value-eq
app-final-none (vV 《 inert 》) M≢blame argument-value-eq
    with value-question-complete (vV 《 inert 》)
app-final-none (vV 《 inert 》) M≢blame argument-value-eq
    | wrapped , value-eq rewrite value-eq =
  app-value-final-none wrapped M≢blame argument-value-eq
app-final-none (vV ↑ reveal) M≢blame argument-value-eq
    with value-question-complete (vV ↑ reveal)
app-final-none (vV ↑ reveal) M≢blame argument-value-eq
    | wrapped , value-eq rewrite value-eq =
  app-value-final-none wrapped M≢blame argument-value-eq
app-final-none (vV ↓ conceal) M≢blame argument-value-eq
    with value-question-complete (vV ↓ conceal)
app-final-none (vV ↓ conceal) M≢blame argument-value-eq
    | wrapped , value-eq rewrite value-eq =
  app-value-final-none wrapped M≢blame argument-value-eq

app-stuck-step-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {V M : Term Δ}
  → (vV : Value V)
  → E.step? Σ M ≡ nothing
  → E.value? M ≡ nothing
  → M ≢ blame
  → E.step? Σ (V · M) ≡ nothing
app-stuck-step-none {Σ = Σ} {V = V} {M = M}
    vV argument-step-eq argument-value-eq M≢blame
    with E.step? Σ V | value-step-none {Σ = Σ} vV
app-stuck-step-none {Σ = Σ} {V = V} {M = M}
    vV argument-step-eq argument-value-eq M≢blame
    | nothing | refl with E.step? Σ M | argument-step-eq
app-stuck-step-none {Σ = Σ} {V = V} {M = M}
    vV argument-step-eq argument-value-eq M≢blame
    | nothing | refl | nothing | refl =
  app-final-none vV M≢blame argument-value-eq

eval-app-stuck-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ}
  → E.step? Σ (V · M) ≡ nothing
  → E.evalFrom Σ (suc gas) (V · M) ≡ nothing
eval-app-stuck-none {Σ = Σ} {gas = gas} {V = V} {M = M}
    step-eq with E.step? Σ (V · M) | step-eq
eval-app-stuck-none step-eq | nothing | refl = refl

app-blame-step-question : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {V : Term Δ}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.step? Σ (V · blame) ≡
        just (E.step-result keep blame (pure-step (blame-·₂ vV′)))
app-blame-step-question (ƛ N) = (ƛ N) , refl
app-blame-step-question (Λ vV) with value-question-complete vV
app-blame-step-question (Λ vV) | vV′ , value-eq
    rewrite value-eq = (Λ vV′) , refl
app-blame-step-question ($ κ) = ($ κ) , refl
app-blame-step-question {Σ = Σ} (vV 《 inert 》)
    with value-question-complete (vV 《 inert 》)
       | value-step-none {Σ = Σ} (vV 《 inert 》)
app-blame-step-question {Σ = Σ} (vV 《 inert 》)
    | wrapped , value-eq | step-eq
    rewrite step-eq | value-eq = wrapped , refl
app-blame-step-question {Σ = Σ} (vV ↑ reveal)
    with value-question-complete (vV ↑ reveal)
       | value-step-none {Σ = Σ} (vV ↑ reveal)
app-blame-step-question {Σ = Σ} (vV ↑ reveal)
    | wrapped , value-eq | step-eq
    rewrite step-eq | value-eq = wrapped , refl
app-blame-step-question {Σ = Σ} (vV ↓ conceal)
    with value-question-complete (vV ↓ conceal)
       | value-step-none {Σ = Σ} (vV ↓ conceal)
app-blame-step-question {Σ = Σ} (vV ↓ conceal)
    | wrapped , value-eq | step-eq
    rewrite step-eq | value-eq = wrapped , refl

app-blame-not-returned : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V : Term Δ} {result : E.EvalResult (V · blame)}
  → Value V
  → E.evalFrom Σ (suc gas) (V · blame) ≡ just (E.returned result)
  → ⊥
app-blame-not-returned {Σ = Σ} {gas = zero} {V = V}
    vV result-eq with app-blame-step-question {Σ = Σ} vV
app-blame-not-returned vV result-eq | vV′ , step-eq
    rewrite step-eq with result-eq
app-blame-not-returned vV result-eq | vV′ , step-eq | ()
app-blame-not-returned {Σ = Σ} {gas = suc gas} {V = V}
    vV result-eq with app-blame-step-question {Σ = Σ} vV
app-blame-not-returned vV result-eq | vV′ , step-eq
    rewrite step-eq with result-eq
app-blame-not-returned vV result-eq | vV′ , step-eq | ()

argument-stuck-impossible : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V · M)}
  → Value V
  → E.step? Σ M ≡ nothing
  → E.value? M ≡ nothing
  → E.evalFrom Σ (suc gas) (V · M) ≡ just (E.returned result)
  → ⊥
argument-stuck-impossible {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV argument-step-eq argument-value-eq result-eq
    with blame-view M
argument-stuck-impossible {Σ = Σ} {gas = gas} {V = V}
    vV argument-step-eq argument-value-eq result-eq
    | is-blame refl = app-blame-not-returned {Σ = Σ} vV result-eq
argument-stuck-impossible {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV argument-step-eq argument-value-eq result-eq
    | not-blame M≢blame =
  impossible
  where
  step-none = app-stuck-step-none {Σ = Σ} vV argument-step-eq
    argument-value-eq M≢blame
  none-eq = eval-app-stuck-none {Σ = Σ} {gas = gas} step-none

  impossible : ⊥
  impossible with trans (sym none-eq) result-eq
  impossible | ()

app-final-left-none : ∀ {Δ : TyCtx} {L M : Term Δ}
  → L ≢ blame
  → E.value? L ≡ nothing
  → E.app-final? L M ≡ nothing
app-final-left-none {L = ` x} L≢blame value-eq = refl
app-final-left-none {L = ƛ N} L≢blame ()
app-final-left-none {L = L · N} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = Λ N} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = L ⦂∀ B [ A ]} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = $ κ} L≢blame ()
app-final-left-none {L = L ⊕[ op ] N} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = L ⟨ c ⟩} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = L ↑ c} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = L ↓ c} L≢blame value-eq
    rewrite value-eq = refl
app-final-left-none {L = blame} L≢blame value-eq =
  ⊥-elim (L≢blame refl)

app-function-stuck-step-none : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {L M : Term Δ}
  → E.step? Σ L ≡ nothing
  → E.value? L ≡ nothing
  → L ≢ blame
  → E.step? Σ (L · M) ≡ nothing
app-function-stuck-step-none {Σ = Σ} {L = L} {M = M}
    function-step-eq function-value-eq L≢blame
    rewrite function-step-eq
    with E.step? Σ M in argument-step-eq
app-function-stuck-step-none {L = L} {M = M}
    function-step-eq function-value-eq L≢blame
    | just (E.step-result χ N step)
    with E.value? L | function-value-eq
app-function-stuck-step-none {L = L} {M = M}
    function-step-eq function-value-eq L≢blame
    | just (E.step-result χ N step)
    | nothing | refl rewrite argument-step-eq =
  app-final-left-none L≢blame function-value-eq
app-function-stuck-step-none {L = L} {M = M}
    function-step-eq function-value-eq L≢blame
    | nothing
    rewrite argument-step-eq =
  app-final-left-none L≢blame function-value-eq

blame-function-step-question : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {M : Term Δ}
  → E.step? Σ (blame · M) ≡
      just (E.step-result keep blame (pure-step blame-·₁))
blame-function-step-question {Σ = Σ} {M = M}
    with E.step? Σ M
blame-function-step-question | just (E.step-result χ N step) = refl
blame-function-step-question | nothing = refl

eval-blame-function-application : ∀
    {Δ : TyCtx} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
  → E.evalFrom Σ (suc gas) (blame · M) ≡
      just (E.blamed (keep ∷ [])
        (↠-step (pure-step blame-·₁) ↠-refl))
eval-blame-function-application {Σ = Σ} {gas = zero} {M = M}
    rewrite blame-function-step-question {Σ = Σ} {M = M} = refl
eval-blame-function-application {Σ = Σ} {gas = suc gas} {M = M}
    rewrite blame-function-step-question {Σ = Σ} {M = M} = refl

blame-function-application-not-returned : ∀
    {Δ : TyCtx} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
    {result : E.EvalResult (blame · M)}
  → E.evalFrom Σ gas (blame · M) ≡ just (E.returned result)
  → ⊥
blame-function-application-not-returned {gas = zero} ()
blame-function-application-not-returned {Σ = Σ} {gas = suc gas}
    {M = M} result-eq
    with trans (sym (eval-blame-function-application
      {Σ = Σ} {gas = gas} {M = M})) result-eq
blame-function-application-not-returned result-eq | ()

function-stuck-impossible : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L · M)}
  → E.step? Σ L ≡ nothing
  → E.value? L ≡ nothing
  → E.evalFrom Σ (suc gas) (L · M) ≡ just (E.returned result)
  → ⊥
function-stuck-impossible {Σ = Σ} {gas = gas} {L = L} {M = M}
    function-step-eq function-value-eq result-eq
    with blame-view L
function-stuck-impossible {Σ = Σ} {gas = gas} {M = M}
    function-step-eq function-value-eq result-eq
    | is-blame refl =
  blame-function-application-not-returned
    {Σ = Σ} {gas = suc gas} {M = M} result-eq
function-stuck-impossible {Σ = Σ} {gas = gas} {L = L} {M = M}
    function-step-eq function-value-eq result-eq
    | not-blame L≢blame =
  impossible
  where
  step-none = app-function-stuck-step-none {Σ = Σ}
    function-step-eq function-value-eq L≢blame
  none-eq = eval-app-stuck-none {Σ = Σ} {gas = gas} step-none

  impossible : ⊥
  impossible with trans (sym none-eq) result-eq
  impossible | ()

argument-return-phases-eval : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V · M)}
  → Value V
  → E.evalFrom Σ gas (V · M) ≡ just (E.returned result)
  → ArgumentReturnPhases Σ gas V M result
argument-return-phases-eval {gas = zero} vV ()
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    with E.step? Σ M in argument-step-eq
       | value-question-complete vV
       | value-step-none {Σ = Σ} vV
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    with E.evalFrom (χ ▷ˢ Σ) gas ((χ ▷ᵀ V) · N) in next-eq
argument-return-phases-eval vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | nothing
    rewrite value-step-eq | argument-step-eq | value-eq | next-eq
    with result-eq
argument-return-phases-eval vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | nothing | ()
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.returned next-result)
    rewrite value-step-eq | argument-step-eq | value-eq | next-eq
    with result-eq
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.returned next-result) | refl
    with argument-return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
      {V = χ ▷ᵀ V} {M = N} {result = next-result}
      (apply-change-value χ vV′) next-eq
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.returned next-result) | refl
    | argument-return-phases-record functionValue argumentGas
        argumentResult argumentReturn callGas callResult callReturn
        result-split gas-eq =
  argument-return-phases-record vV′ (suc argumentGas)
    (prepend-result step argumentResult)
    (prepend-return {Σ = Σ} {M = M} {gas = argumentGas}
      argument-step-eq argumentReturn)
    callGas callResult callReturn
    (cong (prepend-result (ξ-·₂ vV′ step refl))
      (trans result-split
        (sequence-argument-result-value-cong
          {argumentResult = argumentResult} {callResult = callResult}
          (value-unique functionValue (apply-change-value χ vV′)))))
    (cong suc gas-eq)
argument-return-phases-eval vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed changes trace)
    rewrite value-step-eq | argument-step-eq | value-eq | next-eq
    with result-eq
argument-return-phases-eval vV result-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed changes trace) | ()
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | nothing | vV′ , value-eq | value-step-eq
    with E.value? M in argument-value-eq
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | nothing | vV′ , value-eq | value-step-eq
    | just vM with value-eval {Σ = Σ} zero vM
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | nothing | vV′ , value-eq | value-step-eq
    | just vM | vM′ , argument-eval =
  argument-return-phases-record vV′ zero
    (E.result _ [] M ↠-refl vM′)
    (return-from-eval {Σ = Σ} {gas = zero} {M = M} argument-eval)
    (suc gas) _
    (return-from-eval {Σ = Σ} {gas = suc gas} {M = V · M}
      result-eq)
    refl
    refl
argument-return-phases-eval {Σ = Σ} {gas = suc gas} {V = V}
    {M = M} vV result-eq
    | nothing | vV′ , value-eq | value-step-eq
    | nothing = ⊥-elim
      (argument-stuck-impossible {Σ = Σ} {gas = gas} {V = V}
        {M = M} vV argument-step-eq argument-value-eq result-eq)

argument-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V · M)}
  → Value V
  → interpretFrom Σ gas (V · M) ≡ returned result
  → ArgumentReturnPhases Σ gas V M result
argument-return-phases {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV result-eq =
  argument-return-phases-eval {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV (eval-from-return {Σ = Σ} {gas = gas} {M = V · M}
      result-eq)

record ApplicationReturnPhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (L M : Term Δ)
    (wholeResult : E.EvalResult (L · M)) : Set where
  constructor return-phases
  field
    functionGas : ℕ
    functionResult : E.EvalResult L
    functionReturn :
      interpretFrom Σ functionGas L ≡ returned functionResult

    argumentGas : ℕ
    argumentResult :
      E.EvalResult (E.changes functionResult ▶ᵀ M)
    argumentReturn :
      interpretFrom (E.changes functionResult ▶ˢ Σ) argumentGas
        (E.changes functionResult ▶ᵀ M) ≡ returned argumentResult

    callGas : ℕ
    callResult : E.EvalResult
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult)
    callReturn :
      interpretFrom
        (E.changes argumentResult ▶ˢ
          (E.changes functionResult ▶ˢ Σ)) callGas
        ((E.changes argumentResult ▶ᵀ E.term functionResult)
          · E.term argumentResult) ≡ returned callResult

    result-splits : wholeResult ≡
      sequence-application-result functionResult argumentResult callResult

    gas-splits : functionGas + argumentGas + callGas ≡ gas

open ApplicationReturnPhases public

application-value-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ} {result : E.EvalResult (V · M)}
  → Value V
  → E.evalFrom Σ gas (V · M) ≡ just (E.returned result)
  → ArgumentReturnPhases Σ gas V M result
application-value-return-phases = argument-return-phases-eval

application-return-phases-eval : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L · M)}
  → E.evalFrom Σ gas (L · M) ≡ just (E.returned result)
  → ApplicationReturnPhases Σ gas L M result
application-return-phases-eval {gas = zero} ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} {result = result} result-eq
    with E.value? L in function-value-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} {result = result} result-eq
    | just vL
    with application-value-return-phases {Σ = Σ} {gas = suc gas}
      {V = L} {M = M} {result = result} vL result-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | just vL
    | argument-return-phases-record functionValue argumentGas
        argumentResult argumentReturn callGas callResult callReturn
        result-split gas-eq =
  return-phases zero (E.result _ [] L ↠-refl functionValue)
    (value-return-exact {Σ = Σ} zero functionValue)
    argumentGas argumentResult argumentReturn
    callGas callResult callReturn result-split gas-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing with E.step? Σ L in function-step-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas (N · (χ ▷ᵀ M)) in next-eq
application-return-phases-eval result-eq
    | nothing | just (E.step-result χ N step) | nothing
    rewrite function-step-eq | next-eq
    with result-eq
application-return-phases-eval result-eq
    | nothing | just (E.step-result χ N step) | nothing | ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result)
    rewrite function-step-eq | next-eq
    with result-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    with application-return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
      {L = N} {M = χ ▷ᵀ M} {result = next-result} next-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | return-phases functionGas functionResult functionReturn
        argumentGas argumentResult argumentReturn
        callGas callResult callReturn result-split gas-eq =
  return-phases (suc functionGas)
    (prepend-result step functionResult)
    (prepend-return {Σ = Σ} {M = L} {gas = functionGas}
      function-step-eq functionReturn)
    argumentGas argumentResult argumentReturn
    callGas callResult callReturn
    (cong (prepend-result (ξ-·₁ step refl)) result-split)
    (cong suc gas-eq)
application-return-phases-eval result-eq
    | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace)
    rewrite function-step-eq | next-eq
    with result-eq
application-return-phases-eval result-eq
    | nothing | just (E.step-result χ N step)
    | just (E.blamed changes trace) | ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing
    with blame-view L | E.step? Σ M in argument-step-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing | is-blame refl
    | just (E.step-result χ N step)
    with gas
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl
    | just (E.step-result χ N step) | zero
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl
    | just (E.step-result χ N step) | zero | ()
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl
    | just (E.step-result χ N step) | suc gas′
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl
    | just (E.step-result χ N step) | suc gas′ | ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing | is-blame refl | nothing
    with gas
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | nothing | zero
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | nothing | zero | ()
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | nothing | suc gas′
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | is-blame refl | nothing | suc gas′ | ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step)
    with E.value? L | function-value-eq
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step) | nothing | refl
    with E.app-final? L M in final-eq
application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step) | nothing | refl | nothing
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step) | nothing | refl | nothing | ()
application-return-phases-eval {L = L} result-eq
    | nothing | nothing | not-blame L≢blame
    | just (E.step-result χ N step) | nothing | refl
    | just (E.step-result ψ P final-step) =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (app-final-left-none L≢blame function-value-eq)
  impossible | ()
application-return-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} result-eq
    | nothing | nothing | not-blame L≢blame | nothing
    with E.app-final? L M in final-eq
application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≢blame | nothing | nothing
    with result-eq
application-return-phases-eval result-eq
    | nothing | nothing | not-blame L≢blame | nothing | nothing | ()
application-return-phases-eval {L = L} result-eq
    | nothing | nothing | not-blame L≢blame | nothing
    | just (E.step-result ψ P final-step) =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (app-final-left-none L≢blame function-value-eq)
  impossible | ()

application-return-phases : ∀ {Δ : TyCtx} {Σ : TyStore Δ}
    {gas : ℕ} {L M : Term Δ} {result : E.EvalResult (L · M)}
  → interpretFrom Σ gas (L · M) ≡ returned result
  → ApplicationReturnPhases Σ gas L M result
application-return-phases {Σ = Σ} {gas = gas} {L = L} {M = M}
    result-eq =
  application-return-phases-eval {Σ = Σ} {gas = gas} {L = L} {M = M}
    (eval-from-return {Σ = Σ} {gas = gas} {M = L · M} result-eq)

application-return-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas argumentGas callGas : ℕ} {L M : Term Δ}
    {functionResult : E.EvalResult L}
    {argumentResult : E.EvalResult
      (E.changes functionResult ▶ᵀ M)}
    {callResult : E.EvalResult
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult)}
  → interpretFrom Σ functionGas L ≡ returned functionResult
  → interpretFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M) ≡ returned argumentResult
  → interpretFrom
      (E.changes argumentResult ▶ˢ
        (E.changes functionResult ▶ˢ Σ)) callGas
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult) ≡ returned callResult
  → Σ[ wholeGas ∈ ℕ ]
      interpretFrom Σ wholeGas (L · M) ≡
        returned (sequence-application-result functionResult
          argumentResult callResult)
application-return-expand {Σ = Σ} {functionGas = functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    {argumentResult = argumentResult}
    function-eq argument-eq call-eq
    with application-return-expand-eval {Σ = Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {callGas = callGas} {L = L} {M = M}
      (eval-from-return {Σ = Σ} {gas = functionGas} function-eq)
      (eval-from-return
        {Σ = E.changes functionResult ▶ˢ Σ} {gas = argumentGas}
        argument-eq)
      (eval-from-return
        {Σ = E.changes argumentResult ▶ˢ
          (E.changes functionResult ▶ˢ Σ)} {gas = callGas} call-eq)
application-return-expand {Σ = Σ} function-eq argument-eq call-eq
    | wholeGas , whole-eq =
  wholeGas , return-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

eval-from-blame : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {changes : StoreChanges Δ Δ′}
    {trace : M —↠[ changes ] blame}
  → interpretFrom Σ gas M ≡ blamed changes trace
  → E.evalFrom Σ gas M ≡ just (E.blamed changes trace)
eval-from-blame {Σ = Σ} {gas = gas} {M = M} blame-eq
    with E.evalFrom Σ gas M
eval-from-blame blame-eq | nothing with blame-eq
eval-from-blame blame-eq | nothing | ()
eval-from-blame blame-eq | just (E.returned result′) with blame-eq
eval-from-blame blame-eq | just (E.returned result′) | ()
eval-from-blame blame-eq | just (E.blamed changes trace)
    with blame-eq
eval-from-blame blame-eq | just (E.blamed changes trace) | refl = refl

blame-from-eval : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {changes : StoreChanges Δ Δ′}
    {trace : M —↠[ changes ] blame}
  → E.evalFrom Σ gas M ≡ just (E.blamed changes trace)
  → BlamesFrom Σ gas M
blame-from-eval {Σ = Σ} {gas = gas} {M = M}
    {changes = changes} {trace = trace} eval-eq =
  _ , changes , trace ,
  trans (interpret-from-eval {Σ = Σ} {gas = gas} {M = M})
    (cong (interpreter-outcome {M = M}) eval-eq)

prepend-blamed : ∀ {Δ Δ′} {Σ : TyStore Δ} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
    {step : M —→[ χ ] N}
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → BlamesFrom (χ ▷ˢ Σ) gas N
  → BlamesFrom Σ (suc gas) M
prepend-blamed {Σ = Σ} {M = M} {χ = χ} {gas = gas}
    {step = step} step-eq (Δ″ , changes , trace , blame-eq) =
  blame-from-eval {Σ = Σ} {gas = suc gas}
    (eval-prepend-blamed {Σ = Σ} step-eq
      (eval-from-blame {Σ = χ ▷ˢ Σ} {gas = gas} blame-eq))

eval-application-prepend-blame : ∀ {Δ Δ′ Δ″}
    {Σ : TyStore Δ} {L M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {gas : ℕ}
    {step : L · M —→[ χ ] N}
    {changes : StoreChanges Δ′ Δ″}
    {trace : N —↠[ changes ] blame}
  → E.step? Σ (L · M) ≡ just (E.step-result χ N step)
  → E.evalFrom (χ ▷ˢ Σ) gas N ≡ just (E.blamed changes trace)
  → E.evalFrom Σ (suc gas) (L · M) ≡
      just (E.blamed (χ ∷ changes) (↠-step step trace))
eval-application-prepend-blame step-eq next-eq
    rewrite step-eq | next-eq = refl

function-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {functionGas : ℕ} {L M : Term Δ}
    {changes : StoreChanges Δ Δ′} {trace : L —↠[ changes ] blame}
  → E.evalFrom Σ functionGas L ≡ just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ L · M —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (L · M) ≡
        just (E.blamed wholeChanges wholeTrace)
function-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {L = L} {M = M} function-eq with blame-view L
function-blame-expand-eval {Σ = Σ} function-eq | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-·₁) ↠-refl ,
  eval-blame-function-application {Σ = Σ}
function-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {L = L} function-eq | not-blame L≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} L≢blame
    with E.value? L
function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL | ()
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | ()
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    with blame-view L
function-blame-expand-eval {Σ = Σ} function-eq | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-·₁) ↠-refl ,
  eval-blame-function-application {Σ = Σ}
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc functionGas}
      L≢blame
    with E.value? L in function-value-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | just vL | ()
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame | nothing
    with E.step? Σ L in function-step-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | nothing with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | nothing | ()
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step) | nothing
    with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step) | nothing | ()
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) with function-eq
function-blame-expand-eval function-eq | not-blame L≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) | ()
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
    with function-eq
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with function-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {L = N} {M = χ ▷ᵀ M} next-eq
function-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {L = L} {M = M} function-eq
    | not-blame L≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-·₁ step refl) wholeTrace ,
  eval-application-prepend-blame {Σ = Σ}
    (app-function-step-question {Σ = Σ} function-step-eq) whole-eq

function-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas : ℕ} {L M : Term Δ}
  → BlamesFrom Σ functionGas L
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L · M)
function-blame-expand {Σ = Σ} {functionGas = functionGas}
    {L = L} {M = M} (Δ′ , changes , trace , function-eq)
    with function-blame-expand-eval {Σ = Σ}
      {functionGas = functionGas} {L = L} {M = M}
      (eval-from-blame {Σ = Σ} {gas = functionGas} function-eq)
function-blame-expand {Σ = Σ} functionBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

eval-value-blame-application : ∀ {Δ} {Σ : TyStore Δ}
    {V : Term Δ}
  → (vV : Value V)
  → Σ[ vV′ ∈ Value V ]
      E.evalFrom Σ 1 (V · blame) ≡
        just (E.blamed (keep ∷ [])
          (↠-step (pure-step (blame-·₂ vV′)) ↠-refl))
eval-value-blame-application {Σ = Σ} vV
    with app-blame-step-question {Σ = Σ} vV
eval-value-blame-application vV | vV′ , step-eq
    rewrite step-eq = vV′ , refl

argument-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {argumentGas : ℕ} {V M : Term Δ}
    {changes : StoreChanges Δ Δ′} {trace : M —↠[ changes ] blame}
  → (vV : Value V)
  → E.evalFrom Σ argumentGas M ≡ just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ V · M —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (V · M) ≡
        just (E.blamed wholeChanges wholeTrace)
argument-blame-expand-eval {Σ = Σ} {argumentGas = zero}
    {V = V} {M = M} vV argument-eq with blame-view M
argument-blame-expand-eval {Σ = Σ} vV argument-eq
    | is-blame refl with eval-value-blame-application {Σ = Σ} vV
argument-blame-expand-eval vV argument-eq
    | is-blame refl | vV′ , whole-eq =
  1 , _ , keep ∷ [] ,
  ↠-step (pure-step (blame-·₂ vV′)) ↠-refl , whole-eq
argument-blame-expand-eval {Σ = Σ} {argumentGas = zero}
    {V = V} {M = M} vV argument-eq | not-blame M≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} M≢blame
    with E.value? M
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | just vM with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | just vM | ()
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | ()
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq with blame-view M
argument-blame-expand-eval {Σ = Σ} vV argument-eq
    | is-blame refl with eval-value-blame-application {Σ = Σ} vV
argument-blame-expand-eval vV argument-eq
    | is-blame refl | vV′ , whole-eq =
  1 , _ , keep ∷ [] ,
  ↠-step (pure-step (blame-·₂ vV′)) ↠-refl , whole-eq
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc argumentGas}
      M≢blame
    with E.value? M in argument-value-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | just vM with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | just vM | ()
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    with E.step? Σ M in argument-step-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | nothing with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | nothing | ()
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) argumentGas N in next-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step) | nothing
    with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step) | nothing | ()
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned nextResult) with argument-eq
argument-blame-expand-eval vV argument-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned nextResult) | ()
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) with argument-eq
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with argument-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {argumentGas = argumentGas} {V = χ ▷ᵀ V} {M = N}
      (apply-change-value χ vV) next-eq
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
    with app-argument-step-question {Σ = Σ} vV argument-step-eq
argument-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {V = V} {M = M}
    vV argument-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
    | vV′ , application-step-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-·₂ vV′ step refl) wholeTrace ,
  eval-application-prepend-blame {Σ = Σ} application-step-eq whole-eq

argument-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {argumentGas : ℕ} {V M : Term Δ}
  → Value V
  → BlamesFrom Σ argumentGas M
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (V · M)
argument-blame-expand {Σ = Σ} {argumentGas = argumentGas}
    {V = V} {M = M} vV
    (Δ′ , changes , trace , argument-eq)
    with argument-blame-expand-eval {Σ = Σ}
      {argumentGas = argumentGas} {V = V} {M = M} vV
      (eval-from-blame {Σ = Σ} {gas = argumentGas} argument-eq)
argument-blame-expand {Σ = Σ} vV argumentBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

application-argument-blame-expand-eval : ∀ {Δ Δ′}
    {Σ : TyStore Δ} {functionGas argumentGas : ℕ}
    {L M : Term Δ} {functionResult : E.EvalResult L}
    {changes : StoreChanges (E.Δ′ functionResult) Δ′}
    {trace : E.changes functionResult ▶ᵀ M —↠[ changes ] blame}
  → E.evalFrom Σ functionGas L ≡ just (E.returned functionResult)
  → E.evalFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M) ≡
        just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ L · M —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (L · M) ≡
        just (E.blamed wholeChanges wholeTrace)
application-argument-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {L = L} {M = M}
    function-eq argument-eq with blame-view L
application-argument-blame-expand-eval function-eq argument-eq
    | is-blame refl with function-eq
application-argument-blame-expand-eval function-eq argument-eq
    | is-blame refl | ()
application-argument-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {L = L} {M = M}
    function-eq argument-eq | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = L} L≢blame)) function-eq
application-argument-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} function-eq argument-eq
    | not-blame L≢blame | just vL | refl =
  argument-blame-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    vL argument-eq
application-argument-blame-expand-eval function-eq argument-eq
    | not-blame L≢blame | nothing | ()
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq with blame-view L
application-argument-blame-expand-eval function-eq argument-eq
    | is-blame refl with function-eq
application-argument-blame-expand-eval function-eq argument-eq
    | is-blame refl | ()
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc functionGas} {M = L} L≢blame)) function-eq
application-argument-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} function-eq argument-eq
    | not-blame L≢blame | just vL | refl =
  argument-blame-expand-eval {Σ = Σ} {argumentGas = argumentGas}
    vL argument-eq
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame | nothing | normalized-eq
    with E.step? Σ L in function-step-eq
application-argument-blame-expand-eval function-eq argument-eq
    | not-blame L≢blame | nothing | () | nothing
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
application-argument-blame-expand-eval function-eq argument-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
application-argument-blame-expand-eval function-eq argument-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    | just (E.returned nextResult) with normalized-eq
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    with application-argument-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {L = N} {M = χ ▷ᵀ M} next-eq argument-eq
application-argument-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} function-eq argument-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-·₁ step refl) wholeTrace ,
  eval-application-prepend-blame {Σ = Σ}
    (app-function-step-question {Σ = Σ} function-step-eq) whole-eq

application-argument-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas argumentGas : ℕ} {L M : Term Δ}
    {functionResult : E.EvalResult L}
  → interpretFrom Σ functionGas L ≡ returned functionResult
  → BlamesFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M)
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L · M)
application-argument-blame-expand {Σ = Σ}
    {functionGas = functionGas} {argumentGas = argumentGas}
    {L = L} {M = M} {functionResult = functionResult}
    function-eq (Δ′ , changes , trace , argument-eq)
    with application-argument-blame-expand-eval {Σ = Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {L = L} {M = M} {functionResult = functionResult}
      (eval-from-return {Σ = Σ} {gas = functionGas} function-eq)
      (eval-from-blame {Σ = E.changes functionResult ▶ˢ Σ}
        {gas = argumentGas} argument-eq)
application-argument-blame-expand {Σ = Σ} function-eq argumentBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

argument-call-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {argumentGas callGas : ℕ} {V M : Term Δ}
    {argumentResult : E.EvalResult M}
    {changes : StoreChanges (E.Δ′ argumentResult) Δ′}
    {trace : (E.changes argumentResult ▶ᵀ V)
      · E.term argumentResult —↠[ changes ] blame}
  → (vV : Value V)
  → E.evalFrom Σ argumentGas M ≡ just (E.returned argumentResult)
  → E.evalFrom (E.changes argumentResult ▶ˢ Σ) callGas
      ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult) ≡
        just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ V · M —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (V · M) ≡
        just (E.blamed wholeChanges wholeTrace)
argument-call-blame-expand-eval {Σ = Σ} {argumentGas = zero}
    {callGas = callGas} {V = V} {M = M}
    vV argument-eq call-eq with blame-view M
argument-call-blame-expand-eval vV argument-eq call-eq
    | is-blame refl with argument-eq
argument-call-blame-expand-eval vV argument-eq call-eq
    | is-blame refl | ()
argument-call-blame-expand-eval {Σ = Σ} {argumentGas = zero}
    {callGas = callGas} {V = V} {M = M}
    vV argument-eq call-eq | not-blame M≢blame
    with E.value? M in argument-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = M} M≢blame)) argument-eq
argument-call-blame-expand-eval {callGas = callGas}
    vV argument-eq call-eq
    | not-blame M≢blame | just vM | refl =
  callGas , _ , _ , _ , call-eq
argument-call-blame-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq with blame-view M
argument-call-blame-expand-eval vV argument-eq call-eq
    | is-blame refl with argument-eq
argument-call-blame-expand-eval vV argument-eq call-eq
    | is-blame refl | ()
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame
    with E.value? M in argument-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc argumentGas} {M = M} M≢blame)) argument-eq
argument-call-blame-expand-eval {callGas = callGas}
    vV argument-eq call-eq
    | not-blame M≢blame | just vM | refl =
  callGas , _ , _ , _ , call-eq
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    with E.step? Σ M in argument-step-eq
argument-call-blame-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | () | nothing
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) argumentGas N in next-eq
argument-call-blame-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
argument-call-blame-expand-eval vV argument-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    | just (E.returned nextResult) with normalized-eq
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    with argument-call-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {argumentGas = argumentGas} {callGas = callGas}
      {V = χ ▷ᵀ V} {M = N} (apply-change-value χ vV)
      next-eq call-eq
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
    with app-argument-step-question {Σ = Σ} vV argument-step-eq
argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = suc argumentGas} {callGas = callGas}
    {V = V} {M = M} vV argument-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq
    | vV′ , application-step-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-·₂ vV′ step refl) wholeTrace ,
  eval-application-prepend-blame {Σ = Σ} application-step-eq whole-eq

application-call-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {functionGas argumentGas callGas : ℕ} {L M : Term Δ}
    {functionResult : E.EvalResult L}
    {argumentResult : E.EvalResult
      (E.changes functionResult ▶ᵀ M)}
    {changes : StoreChanges (E.Δ′ argumentResult) Δ′}
    {trace : (E.changes argumentResult ▶ᵀ E.term functionResult)
      · E.term argumentResult —↠[ changes ] blame}
  → E.evalFrom Σ functionGas L ≡ just (E.returned functionResult)
  → E.evalFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M) ≡
        just (E.returned argumentResult)
  → E.evalFrom
      (E.changes argumentResult ▶ˢ
        (E.changes functionResult ▶ˢ Σ)) callGas
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult) ≡ just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ L · M —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (L · M) ≡
        just (E.blamed wholeChanges wholeTrace)
application-call-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    with blame-view L
application-call-blame-expand-eval function-eq argument-eq call-eq
    | is-blame refl with function-eq
application-call-blame-expand-eval function-eq argument-eq call-eq
    | is-blame refl | ()
application-call-blame-expand-eval {Σ = Σ} {functionGas = zero}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = L} L≢blame)) function-eq
application-call-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} {callGas = callGas}
    function-eq argument-eq call-eq
    | not-blame L≢blame | just vL | refl =
  argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} {callGas = callGas}
    vL argument-eq call-eq
application-call-blame-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    with blame-view L
application-call-blame-expand-eval function-eq argument-eq call-eq
    | is-blame refl with function-eq
application-call-blame-expand-eval function-eq argument-eq call-eq
    | is-blame refl | ()
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame
    with E.value? L in function-value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc functionGas} {M = L} L≢blame)) function-eq
application-call-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} {callGas = callGas}
    function-eq argument-eq call-eq
    | not-blame L≢blame | just vL | refl =
  argument-call-blame-expand-eval {Σ = Σ}
    {argumentGas = argumentGas} {callGas = callGas}
    vL argument-eq call-eq
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    with E.step? Σ L in function-step-eq
application-call-blame-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | () | nothing
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) functionGas N in next-eq
application-call-blame-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
application-call-blame-expand-eval function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    | just (E.returned nextResult) with normalized-eq
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    with application-call-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {callGas = callGas} {L = N} {M = χ ▷ᵀ M}
      next-eq argument-eq call-eq
application-call-blame-expand-eval {Σ = Σ}
    {functionGas = suc functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} function-eq argument-eq call-eq
    | not-blame L≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned nextResult) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-·₁ step refl) wholeTrace ,
  eval-application-prepend-blame {Σ = Σ}
    (app-function-step-question {Σ = Σ} function-step-eq) whole-eq

application-call-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {functionGas argumentGas callGas : ℕ} {L M : Term Δ}
    {functionResult : E.EvalResult L}
    {argumentResult : E.EvalResult
      (E.changes functionResult ▶ᵀ M)}
  → interpretFrom Σ functionGas L ≡ returned functionResult
  → interpretFrom (E.changes functionResult ▶ˢ Σ) argumentGas
      (E.changes functionResult ▶ᵀ M) ≡ returned argumentResult
  → BlamesFrom
      (E.changes argumentResult ▶ˢ
        (E.changes functionResult ▶ˢ Σ)) callGas
      ((E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult)
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (L · M)
application-call-blame-expand {Σ = Σ} {functionGas = functionGas}
    {argumentGas = argumentGas} {callGas = callGas}
    {L = L} {M = M} {functionResult = functionResult}
    {argumentResult = argumentResult} function-eq argument-eq
    (Δ′ , changes , trace , call-eq)
    with application-call-blame-expand-eval {Σ = Σ}
      {functionGas = functionGas} {argumentGas = argumentGas}
      {callGas = callGas} {L = L} {M = M}
      {functionResult = functionResult} {argumentResult = argumentResult}
      (eval-from-return {Σ = Σ} {gas = functionGas} function-eq)
      (eval-from-return {Σ = E.changes functionResult ▶ˢ Σ}
        {gas = argumentGas} argument-eq)
      (eval-from-blame {Σ = E.changes argumentResult ▶ˢ
        (E.changes functionResult ▶ˢ Σ)} {gas = callGas} call-eq)
application-call-blame-expand {Σ = Σ}
    function-eq argument-eq callBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

data ArgumentBlamePhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (V M : Term Δ) : Set where
  argument-phase-blames :
      (functionValue : Value V)
    → (argumentGas : ℕ)
    → BlamesFrom Σ argumentGas M
    → argumentGas ≤ gas
    → ArgumentBlamePhases Σ gas V M

  call-phase-blames :
      (functionValue : Value V)
    → (argumentGas : ℕ)
    → (argumentResult : E.EvalResult M)
    → interpretFrom Σ argumentGas M ≡ returned argumentResult
    → (callGas : ℕ)
    → BlamesFrom (E.changes argumentResult ▶ˢ Σ) callGas
        ((E.changes argumentResult ▶ᵀ V) · E.term argumentResult)
    → argumentGas + callGas ≤ gas
    → ArgumentBlamePhases Σ gas V M

argument-blame-phases-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ} {changes : StoreChanges Δ Δ′}
    {trace : V · M —↠[ changes ] blame}
  → Value V
  → E.evalFrom Σ gas (V · M) ≡ just (E.blamed changes trace)
  → ArgumentBlamePhases Σ gas V M
argument-blame-phases-eval {gas = zero} vV ()
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    with E.step? Σ M in argument-step-eq
       | value-question-complete vV
       | value-step-none {Σ = Σ} vV
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    with E.evalFrom (χ ▷ˢ Σ) gas ((χ ▷ᵀ V) · N) in next-eq
argument-blame-phases-eval vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | nothing rewrite value-step-eq | argument-step-eq | value-eq
      | next-eq with whole-eq
argument-blame-phases-eval vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | nothing | ()
argument-blame-phases-eval vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.returned nextResult)
    rewrite value-step-eq | argument-step-eq | value-eq | next-eq
    with whole-eq
argument-blame-phases-eval vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.returned nextResult) | ()
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed nextChanges nextTrace)
    rewrite value-step-eq | argument-step-eq | value-eq | next-eq
    with whole-eq
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed nextChanges nextTrace) | refl
    with argument-blame-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
      {V = χ ▷ᵀ V} {M = N} (apply-change-value χ vV′) next-eq
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed nextChanges nextTrace) | refl
    | argument-phase-blames functionValue argumentGas argumentBlame
        argumentGas≤ =
  argument-phase-blames vV′ (suc argumentGas)
    (prepend-blamed {Σ = Σ} argument-step-eq argumentBlame)
    (s≤s argumentGas≤)
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | just (E.step-result χ N step) | vV′ , value-eq | value-step-eq
    | just (E.blamed nextChanges nextTrace) | refl
    | call-phase-blames functionValue argumentGas argumentResult
        argumentReturn callGas callBlame phases≤ =
  call-phase-blames vV′ (suc argumentGas)
    (prepend-result step argumentResult)
    (prepend-return {Σ = Σ} argument-step-eq argumentReturn)
    callGas callBlame (s≤s phases≤)
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | nothing | vV′ , value-eq | value-step-eq
    with E.value? M in argument-value-eq
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | nothing | vV′ , value-eq | value-step-eq | just vM =
  call-phase-blames vV′ zero (E.result _ [] M ↠-refl vM)
    (value-return-exact {Σ = Σ} zero vM) (suc gas)
    (blame-from-eval {Σ = Σ} {gas = suc gas} whole-eq) ≤-refl
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | nothing | vV′ , value-eq | value-step-eq | nothing
    with blame-view M
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | nothing | vV′ , value-eq | value-step-eq | nothing
    | is-blame refl =
  argument-phase-blames vV′ zero
    (_ , [] , ↠-refl , refl) z≤n
argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {V = V} {M = M} vV whole-eq
    | nothing | vV′ , value-eq | value-step-eq | nothing
    | not-blame M≢blame = ⊥-elim impossible
  where
  app-step-none = app-stuck-step-none {Σ = Σ} vV
    argument-step-eq argument-value-eq M≢blame
  app-eval-none = eval-app-stuck-none {Σ = Σ} {gas = gas} app-step-none

  impossible : ⊥
  impossible with trans (sym app-eval-none) whole-eq
  impossible | ()

argument-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {V M : Term Δ}
  → Value V
  → BlamesFrom Σ gas (V · M)
  → ArgumentBlamePhases Σ gas V M
argument-blame-phases {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV (Δ′ , changes , trace , whole-eq) =
  argument-blame-phases-eval {Σ = Σ} {gas = gas} {V = V} {M = M}
    vV (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)

data ApplicationBlamePhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (L M : Term Δ) : Set where
  function-phase-blames :
      (functionGas : ℕ)
    → BlamesFrom Σ functionGas L
    → functionGas ≤ gas
    → ApplicationBlamePhases Σ gas L M

  application-argument-phase-blames :
      (functionGas : ℕ)
    → (functionResult : E.EvalResult L)
    → interpretFrom Σ functionGas L ≡ returned functionResult
    → (argumentGas : ℕ)
    → BlamesFrom (E.changes functionResult ▶ˢ Σ) argumentGas
        (E.changes functionResult ▶ᵀ M)
    → functionGas + argumentGas ≤ gas
    → ApplicationBlamePhases Σ gas L M

  application-call-phase-blames :
      (functionGas : ℕ)
    → (functionResult : E.EvalResult L)
    → interpretFrom Σ functionGas L ≡ returned functionResult
    → (argumentGas : ℕ)
    → (argumentResult :
        E.EvalResult (E.changes functionResult ▶ᵀ M))
    → interpretFrom (E.changes functionResult ▶ˢ Σ) argumentGas
        (E.changes functionResult ▶ᵀ M) ≡ returned argumentResult
    → (callGas : ℕ)
    → BlamesFrom
        (E.changes argumentResult ▶ˢ
          (E.changes functionResult ▶ˢ Σ)) callGas
        ((E.changes argumentResult ▶ᵀ E.term functionResult)
          · E.term argumentResult)
    → functionGas + argumentGas + callGas ≤ gas
    → ApplicationBlamePhases Σ gas L M

application-blame-phases-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {gas : ℕ} {L M : Term Δ} {changes : StoreChanges Δ Δ′}
    {trace : L · M —↠[ changes ] blame}
  → E.evalFrom Σ gas (L · M) ≡ just (E.blamed changes trace)
  → ApplicationBlamePhases Σ gas L M
application-blame-phases-eval {gas = zero} ()
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq
    with E.value? L in function-value-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | just vL
    with argument-blame-phases-eval {Σ = Σ} {gas = suc gas}
      {V = L} {M = M} vL whole-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | just vL
    | argument-phase-blames functionValue argumentGas argumentBlame
        argumentGas≤ =
  application-argument-phase-blames zero
    (E.result _ [] L ↠-refl functionValue)
    (value-return-exact {Σ = Σ} zero functionValue)
    argumentGas argumentBlame argumentGas≤
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | just vL
    | call-phase-blames functionValue argumentGas argumentResult
        argumentReturn callGas callBlame phases≤ =
  application-call-phase-blames zero
    (E.result _ [] L ↠-refl functionValue)
    (value-return-exact {Σ = Σ} zero functionValue)
    argumentGas argumentResult argumentReturn callGas callBlame phases≤
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    with E.step? Σ L in function-step-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas (N · (χ ▷ᵀ M)) in next-eq
application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | nothing
    rewrite function-step-eq | next-eq
    with whole-eq
application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | nothing | ()
application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | just (E.returned nextResult)
    rewrite function-step-eq | next-eq
    with whole-eq
application-blame-phases-eval whole-eq | nothing
    | just (E.step-result χ N step) | just (E.returned nextResult) | ()
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
    rewrite function-step-eq | next-eq
    with whole-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with application-blame-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
      {L = N} {M = χ ▷ᵀ M} next-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | function-phase-blames functionGas functionBlame functionGas≤ =
  function-phase-blames (suc functionGas)
    (prepend-blamed {Σ = Σ} function-step-eq functionBlame)
    (s≤s functionGas≤)
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | application-argument-phase-blames functionGas functionResult
        functionReturn argumentGas argumentBlame phases≤ =
  application-argument-phase-blames (suc functionGas)
    (prepend-result step functionResult)
    (prepend-return {Σ = Σ} function-step-eq functionReturn)
    argumentGas argumentBlame (s≤s phases≤)
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | application-call-phase-blames functionGas functionResult
        functionReturn argumentGas argumentResult argumentReturn
        callGas callBlame phases≤ =
  application-call-phase-blames (suc functionGas)
    (prepend-result step functionResult)
    (prepend-return {Σ = Σ} function-step-eq functionReturn)
    argumentGas argumentResult argumentReturn callGas callBlame
    (s≤s phases≤)
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    with blame-view L | E.step? Σ M in argument-step-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    | is-blame refl | just (E.step-result χ N step) =
  function-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    | is-blame refl | nothing =
  function-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    | not-blame L≢blame | just (E.step-result χ N step)
    with E.value? L | function-value-eq
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    | not-blame L≢blame | just (E.step-result χ N step)
    | nothing | refl with E.app-final? L M in final-eq
application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | just (E.step-result χ N step)
    | nothing | refl | nothing with whole-eq
application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | just (E.step-result χ N step)
    | nothing | refl | nothing | ()
application-blame-phases-eval {L = L} whole-eq | nothing | nothing
    | not-blame L≢blame | just (E.step-result χ N step)
    | nothing | refl | just (E.step-result ψ P final-step) =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (app-final-left-none L≢blame function-value-eq)
  impossible | ()
application-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {L = L} {M = M} whole-eq | nothing | nothing
    | not-blame L≢blame | nothing
    with E.app-final? L M in final-eq
application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | nothing | nothing with whole-eq
application-blame-phases-eval whole-eq | nothing | nothing
    | not-blame L≢blame | nothing | nothing | ()
application-blame-phases-eval {L = L} whole-eq | nothing | nothing
    | not-blame L≢blame | nothing
    | just (E.step-result ψ P final-step) =
  ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (app-final-left-none L≢blame function-value-eq)
  impossible | ()

application-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {L M : Term Δ}
  → BlamesFrom Σ gas (L · M)
  → ApplicationBlamePhases Σ gas L M
application-blame-phases {Σ = Σ} {gas = gas} {L = L} {M = M}
    (Δ′ , changes , trace , whole-eq) =
  application-blame-phases-eval {Σ = Σ} {gas = gas}
    {L = L} {M = M}
    (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)

------------------------------------------------------------------------
-- Step-index arithmetic for the three evaluation phases
------------------------------------------------------------------------

left-summand≤ : ∀ a b → a ≤ a + b
left-summand≤ zero b = z≤n
left-summand≤ (suc a) b = s≤s (left-summand≤ a b)

drop-left-≤ : ∀ {a b k} → a + b ≤ k → b ≤ k ∸ a
drop-left-≤ {zero} a+b≤k = a+b≤k
drop-left-≤ {suc a} {b} {zero} ()
drop-left-≤ {suc a} {b} {suc k} (s≤s a+b≤k) =
  drop-left-≤ {a} {b} {k} a+b≤k

first-of-two≤ : ∀ {a b k} → a + b ≤ k → a ≤ k
first-of-two≤ {a} {b} phases≤ =
  ≤-trans (left-summand≤ a b) phases≤

first-phase≤ : ∀ {a b c k} → a + b + c ≤ k → a ≤ k
first-phase≤ {zero} phases≤ = z≤n
first-phase≤ {suc a} {b} {c} {zero} ()
first-phase≤ {suc a} {b} {c} {suc k} (s≤s phases≤) =
  s≤s (first-phase≤ {a} {b} {c} {k} phases≤)

remaining-phases≤ : ∀ {a b c k}
  → a + b + c ≤ k
  → b + c ≤ k ∸ a
remaining-phases≤ {zero} phases≤ = phases≤
remaining-phases≤ {suc a} {b} {c} {zero} ()
remaining-phases≤ {suc a} {b} {c} {suc k} (s≤s phases≤) =
  remaining-phases≤ {a} {b} {c} {k} phases≤

second-phase≤ : ∀ {a b c k}
  → a + b + c ≤ k
  → b ≤ k ∸ a
second-phase≤ {a} {b} {c} phases≤ =
  ≤-trans (left-summand≤ b c)
    (remaining-phases≤ {a} {b} {c} phases≤)

third-phase≤ : ∀ {a b c k}
  → a + b + c ≤ k
  → c ≤ (k ∸ a) ∸ b
third-phase≤ {a} {b} {c} phases≤ =
  drop-left-≤ (remaining-phases≤ {a} {b} {c} phases≤)

subtract-phases : ∀ k a b
  → (k ∸ a) ∸ b ≡ k ∸ (a + b)
subtract-phases k zero b = refl
subtract-phases zero (suc a) zero = refl
subtract-phases zero (suc a) (suc b) = refl
subtract-phases (suc k) (suc a) b = subtract-phases k a b

subtract-three : ∀ k a b c
  → ((k ∸ a) ∸ b) ∸ c ≡ k ∸ (a + b + c)
subtract-three k a b c = trans
  (subtract-phases (k ∸ a) b c)
  (trans (subtract-phases k a (b + c))
    (cong (k ∸_) (sym (+-assoc a b c))))

application-return-positive≤ : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {L M : Term Δ} {result : E.EvalResult (L · M)}
  → interpretFrom Σ gas (L · M) ≡ returned result
  → suc zero ≤ gas
application-return-positive≤ {gas = zero} ()
application-return-positive≤ {gas = suc gas} result-eq = s≤s z≤n

application-blame-positive≤ : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {L M : Term Δ}
  → BlamesFrom Σ gas (L · M)
  → suc zero ≤ gas
application-blame-positive≤ {gas = zero} (Δ′ , changes , trace , ())
application-blame-positive≤ {gas = suc gas} blaming = s≤s z≤n

return-store-reindex : ∀ {Δ} {Σ Σ′ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {result : E.EvalResult M}
  → Σ ≡ Σ′
  → interpretFrom Σ′ gas M ≡ returned result
  → interpretFrom Σ gas M ≡ returned result
return-store-reindex refl result-eq = result-eq

blame-store-reindex : ∀ {Δ} {Σ Σ′ : TyStore Δ} {gas : ℕ}
    {M : Term Δ}
  → Σ ≡ Σ′
  → BlamesFrom Σ′ gas M
  → BlamesFrom Σ gas M
blame-store-reindex refl blaming = blaming

value-terms-reindex : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {k : ℕ} {Vᴵ Vᴵ′ : Term Δᴵ} {Vᴾ Vᴾ′ : Term Δᴾ}
  → Vᴵ ≡ Vᴵ′
  → Vᴾ ≡ Vᴾ′
  → ValueImprecision W p k Vᴵ′ Vᴾ′
  → ValueImprecision W p k Vᴵ Vᴾ
value-terms-reindex refl refl related = related

value-index-reindex : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {j k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → j ≡ k
  → ValueImprecision W p j Vᴵ Vᴾ
  → ValueImprecision W p k Vᴵ Vᴾ
value-index-reindex refl related = related

paired-returns-reindex : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {resultᴵ resultᴵ′ : E.EvalResult Mᴵ}
    {resultᴾ resultᴾ′ : E.EvalResult Mᴾ}
  → resultᴵ ≡ resultᴵ′
  → resultᴾ ≡ resultᴾ′
  → PairedReturns W R k resultᴵ′ resultᴾ′
  → PairedReturns W R k resultᴵ resultᴾ
paired-returns-reindex refl refl paired = paired

positive-function-application : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {q : impEnv (core W) I.⊢ Bᴾ ⊑ Bᴵ}
    {k : ℕ} {Vᴵ Uᴵ : Term Δᴵ} {Vᴾ Uᴾ : Term Δᴾ}
  → suc zero ≤ k
  → ValueImprecision W (I.⇒⊑⇒ p q) k Vᴵ Vᴾ
  → ValueImprecision W p k Uᴵ Uᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ · Uᴵ) (Vᴾ · Uᴾ)
positive-function-application {k = zero} () function argument
positive-function-application {k = suc k} positive function argument =
  related-function-application function argument

assemble-application-pair : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᶜ₁ Δᶜ₂ Δᶜ₃}
    {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {Aᴾ Aᴵ : Ty Δᶜ₀}
    {q : impEnv (core W₀) I.⊢ Aᴾ ⊑ Aᴵ}
    {Lᴾ Mᴾ : Term Δᴾ₀} {Lᴵ Mᴵ : Term Δᴵ₀}
    {functionResultᴾ : E.EvalResult Lᴾ}
    {functionResultᴵ : E.EvalResult Lᴵ}
    {argumentResultᴾ : E.EvalResult
      (E.changes functionResultᴾ ▶ᵀ Mᴾ)}
    {argumentResultᴵ : E.EvalResult
      (E.changes functionResultᴵ ▶ᵀ Mᴵ)}
    {callResultᴾ : E.EvalResult
      ((E.changes argumentResultᴾ ▶ᵀ E.term functionResultᴾ)
        · E.term argumentResultᴾ)}
    {callResultᴵ : E.EvalResult
      ((E.changes argumentResultᴵ ▶ᵀ E.term functionResultᴵ)
        · E.term argumentResultᴵ)}
    {W₁ : World (E.Δ′ functionResultᴾ)
      (E.Δ′ functionResultᴵ) Δᶜ₁}
    {W₂ : World (E.Δ′ argumentResultᴾ)
      (E.Δ′ argumentResultᴵ) Δᶜ₂}
    {W₃ : World (E.Δ′ callResultᴾ) (E.Δ′ callResultᴵ) Δᶜ₃}
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
  → (W₁≼W₂ : Future W₁ W₂)
  → impreciseStore (core W₂) ≡
      E.changes argumentResultᴵ ▶ˢ impreciseStore (core W₁)
  → preciseStore (core W₂) ≡
      E.changes argumentResultᴾ ▶ˢ preciseStore (core W₁)
  → (∀ M → E.changes argumentResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₁≼W₂ M)
  → (∀ M → E.changes argumentResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₁≼W₂ M)
  → (W₂≼W₃ : Future W₂ W₃)
  → impreciseStore (core W₃) ≡
      E.changes callResultᴵ ▶ˢ impreciseStore (core W₂)
  → preciseStore (core W₃) ≡
      E.changes callResultᴾ ▶ˢ preciseStore (core W₂)
  → (∀ M → E.changes callResultᴵ ▶ᵀ M ≡
      liftImpreciseTerm W₂≼W₃ M)
  → (∀ M → E.changes callResultᴾ ▶ᵀ M ≡
      liftPreciseTerm W₂≼W₃ M)
  → j ≡ k
  → ValueImprecision W₃
      (liftCenterImprecision W₂≼W₃
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ q)))
      j (E.term callResultᴵ) (E.term callResultᴾ)
  → PairedReturns W₀ (FutureValueRelation q) k
      (sequence-application-result functionResultᴵ
        argumentResultᴵ callResultᴵ)
      (sequence-application-result functionResultᴾ
        argumentResultᴾ callResultᴾ)
assemble-application-pair {W₀ = W₀} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {q = q}
    {functionResultᴾ = functionResultᴾ}
    {functionResultᴵ = functionResultᴵ}
    {argumentResultᴾ = argumentResultᴾ}
    {argumentResultᴵ = argumentResultᴵ}
    {callResultᴾ = callResultᴾ} {callResultᴵ = callResultᴵ}
    {W₁ = W₁} {W₂ = W₂} {W₃ = W₃}
    W₀≼W₁ functionStoreᴵ functionStoreᴾ
    functionTermsᴵ functionTermsᴾ
    W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
    argumentTermsᴵ argumentTermsᴾ
    W₂≼W₃ callStoreᴵ callStoreᴾ callTermsᴵ callTermsᴾ indexEq
    callValueRelated =
  paired-returns W₃ W₀≼W₃ impreciseStoreEq preciseStoreEq
    impreciseTermsEq preciseTermsEq finalValueRelated
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂
  W₀≼W₃ = future-trans W₀≼W₂ W₂≼W₃

  impreciseStoreEq = trans callStoreᴵ
    (trans (cong (λ Σ → E.changes callResultᴵ ▶ˢ Σ) argumentStoreᴵ)
      (trans
        (cong (λ Σ → E.changes callResultᴵ ▶ˢ
          (E.changes argumentResultᴵ ▶ˢ Σ)) functionStoreᴵ)
        (trans
          (apply-stores-++ (E.changes argumentResultᴵ)
            (E.changes callResultᴵ)
            (E.changes functionResultᴵ ▶ˢ impreciseStore (core W₀)))
          (apply-stores-++ (E.changes functionResultᴵ)
            (E.changes argumentResultᴵ ++ˢ E.changes callResultᴵ)
            (impreciseStore (core W₀))))))

  preciseStoreEq = trans callStoreᴾ
    (trans (cong (λ Σ → E.changes callResultᴾ ▶ˢ Σ) argumentStoreᴾ)
      (trans
        (cong (λ Σ → E.changes callResultᴾ ▶ˢ
          (E.changes argumentResultᴾ ▶ˢ Σ)) functionStoreᴾ)
        (trans
          (apply-stores-++ (E.changes argumentResultᴾ)
            (E.changes callResultᴾ)
            (E.changes functionResultᴾ ▶ˢ preciseStore (core W₀)))
          (apply-stores-++ (E.changes functionResultᴾ)
            (E.changes argumentResultᴾ ++ˢ E.changes callResultᴾ)
            (preciseStore (core W₀))))))

  impreciseApplicationResult = sequence-application-result
    functionResultᴵ argumentResultᴵ callResultᴵ

  preciseApplicationResult = sequence-application-result
    functionResultᴾ argumentResultᴾ callResultᴾ

  impreciseTermsEq : ∀ M →
      E.changes impreciseApplicationResult ▶ᵀ M ≡
        liftImpreciseTerm W₀≼W₃ M
  impreciseTermsEq M = trans
    (sym (apply-terms-++ (E.changes functionResultᴵ)
      (E.changes argumentResultᴵ ++ˢ E.changes callResultᴵ) M))
    (trans
      (cong (λ N → (E.changes argumentResultᴵ ++ˢ
        E.changes callResultᴵ) ▶ᵀ N) (functionTermsᴵ M))
      (trans
        (sym (apply-terms-++ (E.changes argumentResultᴵ)
          (E.changes callResultᴵ) (liftImpreciseTerm W₀≼W₁ M)))
        (trans
          (cong (λ N → E.changes callResultᴵ ▶ᵀ N)
            (argumentTermsᴵ (liftImpreciseTerm W₀≼W₁ M)))
          (trans
            (callTermsᴵ (liftImpreciseTerm W₁≼W₂
              (liftImpreciseTerm W₀≼W₁ M)))
            (trans
              (cong (liftImpreciseTerm W₂≼W₃)
                (sym (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))
              (sym (liftImpreciseTerm-trans W₀≼W₂ W₂≼W₃ M)))))))

  preciseTermsEq : ∀ M →
      E.changes preciseApplicationResult ▶ᵀ M ≡
        liftPreciseTerm W₀≼W₃ M
  preciseTermsEq M = trans
    (sym (apply-terms-++ (E.changes functionResultᴾ)
      (E.changes argumentResultᴾ ++ˢ E.changes callResultᴾ) M))
    (trans
      (cong (λ N → (E.changes argumentResultᴾ ++ˢ
        E.changes callResultᴾ) ▶ᵀ N) (functionTermsᴾ M))
      (trans
        (sym (apply-terms-++ (E.changes argumentResultᴾ)
          (E.changes callResultᴾ) (liftPreciseTerm W₀≼W₁ M)))
        (trans
          (cong (λ N → E.changes callResultᴾ ▶ᵀ N)
            (argumentTermsᴾ (liftPreciseTerm W₀≼W₁ M)))
          (trans
            (callTermsᴾ (liftPreciseTerm W₁≼W₂
              (liftPreciseTerm W₀≼W₁ M)))
            (trans
              (cong (liftPreciseTerm W₂≼W₃)
                (sym (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ M)))
              (sym (liftPreciseTerm-trans W₀≼W₂ W₂≼W₃ M)))))))

  compositeQ = liftCenterImprecision W₀≼W₃ q
  sequentialQ = liftCenterImprecision W₂≼W₃
    (liftCenterImprecision W₁≼W₂
      (liftCenterImprecision W₀≼W₁ q))

  preciseQEq = trans
    (liftCenterTy-trans W₀≼W₂ W₂≼W₃
      Aᴾ)
    (cong (liftCenterTy W₂≼W₃)
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        Aᴾ))

  impreciseQEq = trans
    (liftCenterTy-trans W₀≼W₂ W₂≼W₃
      Aᴵ)
    (cong (liftCenterTy W₂≼W₃)
      (liftCenterTy-trans W₀≼W₁ W₁≼W₂
        Aᴵ))

  finalValueRelated = ClosureProof.value-imprecision-reindex
    compositeQ sequentialQ preciseQEq impreciseQEq
    (value-index-reindex indexEq callValueRelated)

------------------------------------------------------------------------
-- Reopening a component relation after a returned phase
------------------------------------------------------------------------

compiled-component-future-at : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Aᴾ Aᴵ} {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Γ : CTI.CtxImp (forgetWorld W₀)}
    {p : Aᴾ ⊑ᵂ⟨ core W₀ ⟩ Aᴵ}
    {Mᴾ : Term Δᴾ₀} {Mᴵ : Term Δᴵ₀}
    {j k : ℕ}
  → CompiledTermRelation {W = W₀} p j Γ Mᴾ Mᴵ
  → (W₀≼W₁ : Future W₀ W₁)
  → (γ : RelatedClosingSubstitutions W₁ k
      (liftContextImprecision W₀≼W₁ (compiledContext W₀ Γ)))
  → (W₁≼W₂ : Future W₁ W₂)
  → j ≤ k
  → ComputationsRelated W₂
      (FutureValueRelation
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ p))) j
      (liftImpreciseTerm W₁≼W₂
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W₀≼W₁ Mᴵ)))
      (liftPreciseTerm W₁≼W₂
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W₀≼W₁ Mᴾ)))
compiled-component-future-at {W₀ = W₀} {W₂ = W₂} {Γ = Γ}
    {p = p} {Mᴾ = Mᴾ} {Mᴵ = Mᴵ} {j = j}
    related W₀≼W₁ γ W₁≼W₂ j≤k =
  ClosureProof.computations-related-reindex p-composite p-sequential
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedPrecise (core W₀) _))
    (liftCenterTy-trans W₀≼W₁ W₁≼W₂
      (embedImprecise (core W₀) _))
    imprecise-term-eq precise-term-eq
    (related W₂ W₀≼W₂ γ-trans)
  where
  W₀≼W₂ = future-trans W₀≼W₁ W₁≼W₂
  γ-down = related-closing-downward j≤k γ
  γ-future = related-closing-future W₁≼W₂ γ-down
  γ-trans = related-closing-trans W₀≼W₁ W₁≼W₂ γ-future

  p-composite = liftCenterImprecision W₀≼W₂ p
  p-sequential = liftCenterImprecision W₁≼W₂
    (liftCenterImprecision W₀≼W₁ p)

  imprecise-env-eq : ∀ x →
      closingSubstitution (impreciseClosingSubstitution γ-trans) x ≡
        closingSubstitution (imprecise-closing-future W₁≼W₂
          (impreciseClosingSubstitution γ)) x
  imprecise-env-eq x = trans
    (ClosingProof.imprecise-related-trans-lookup
      W₀≼W₁ W₁≼W₂ γ-future x)
    (trans
      (ClosingProof.imprecise-related-future-lookup W₁≼W₂ γ-down x)
      (trans
        (cong (liftImpreciseTerm W₁≼W₂)
          (ClosingProof.imprecise-related-downward-lookup j≤k γ x))
        (sym (ClosingProof.imprecise-closing-future-lookup
          W₁≼W₂ (impreciseClosingSubstitution γ) x))))

  precise-env-eq : ∀ x →
      closingSubstitution (preciseClosingSubstitution γ-trans) x ≡
        closingSubstitution (precise-closing-future W₁≼W₂
          (preciseClosingSubstitution γ)) x
  precise-env-eq x = trans
    (ClosingProof.precise-related-trans-lookup
      W₀≼W₁ W₁≼W₂ γ-future x)
    (trans
      (ClosingProof.precise-related-future-lookup W₁≼W₂ γ-down x)
      (trans
        (cong (liftPreciseTerm W₁≼W₂)
          (ClosingProof.precise-related-downward-lookup j≤k γ x))
        (sym (ClosingProof.precise-closing-future-lookup
          W₁≼W₂ (preciseClosingSubstitution γ) x))))

  imprecise-term-eq : close (impreciseClosingSubstitution γ-trans)
      (liftImpreciseTerm W₀≼W₂ Mᴵ) ≡
    liftImpreciseTerm W₁≼W₂
      (close (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W₀≼W₁ Mᴵ))
  imprecise-term-eq = trans
    (cong (close (impreciseClosingSubstitution γ-trans))
      (liftImpreciseTerm-trans W₀≼W₁ W₁≼W₂ Mᴵ))
    (trans
      (subst-cong imprecise-env-eq
        (liftImpreciseTerm W₁≼W₂
          (liftImpreciseTerm W₀≼W₁ Mᴵ)))
      (sym (imprecise-close-future W₁≼W₂
        (impreciseClosingSubstitution γ)
        (liftImpreciseTerm W₀≼W₁ Mᴵ))))

  precise-term-eq : close (preciseClosingSubstitution γ-trans)
      (liftPreciseTerm W₀≼W₂ Mᴾ) ≡
    liftPreciseTerm W₁≼W₂
      (close (preciseClosingSubstitution γ)
        (liftPreciseTerm W₀≼W₁ Mᴾ))
  precise-term-eq = trans
    (cong (close (preciseClosingSubstitution γ-trans))
      (liftPreciseTerm-trans W₀≼W₁ W₁≼W₂ Mᴾ))
    (trans
      (subst-cong precise-env-eq
        (liftPreciseTerm W₁≼W₂
          (liftPreciseTerm W₀≼W₁ Mᴾ)))
      (sym (precise-close-future W₁≼W₂
        (preciseClosingSubstitution γ)
        (liftPreciseTerm W₀≼W₁ Mᴾ))))

compiled-component-future : ∀
    {Δᴾ₀ Δᴵ₀ Δᶜ₀ Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Aᴾ Aᴵ} {W₀ : World Δᴾ₀ Δᴵ₀ Δᶜ₀}
    {W₁ : World Δᴾ₁ Δᴵ₁ Δᶜ₁}
    {W₂ : World Δᴾ₂ Δᴵ₂ Δᶜ₂}
    {Γ : CTI.CtxImp (forgetWorld W₀)}
    {p : Aᴾ ⊑ᵂ⟨ core W₀ ⟩ Aᴵ}
    {Mᴾ : Term Δᴾ₀} {Mᴵ : Term Δᴵ₀}
    {j k : ℕ}
  → (∀ i → CompiledTermRelation {W = W₀} p i Γ Mᴾ Mᴵ)
  → (W₀≼W₁ : Future W₀ W₁)
  → (γ : RelatedClosingSubstitutions W₁ k
      (liftContextImprecision W₀≼W₁ (compiledContext W₀ Γ)))
  → (W₁≼W₂ : Future W₁ W₂)
  → j ≤ k
  → ComputationsRelated W₂
      (FutureValueRelation
        (liftCenterImprecision W₁≼W₂
          (liftCenterImprecision W₀≼W₁ p))) j
      (liftImpreciseTerm W₁≼W₂
        (close (impreciseClosingSubstitution γ)
          (liftImpreciseTerm W₀≼W₁ Mᴵ)))
      (liftPreciseTerm W₁≼W₂
        (close (preciseClosingSubstitution γ)
          (liftPreciseTerm W₀≼W₁ Mᴾ)))
compiled-component-future {j = j} related =
  compiled-component-future-at (related j)

------------------------------------------------------------------------
-- Compiled application compatibility
------------------------------------------------------------------------

application-semantic-bounded : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ}
    {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
  → (k : ℕ)
  → (∀ j → j ≤ k →
      CompiledTermRelation {W = W} (I.⇒⊑⇒ p q) j Γ Lᴾ Lᴵ)
  → (∀ j → j ≤ k →
      CompiledTermRelation {W = W} p j Γ Mᴾ Mᴵ)
  → CompiledTermRelation {W = W} q k Γ
      (Lᴾ · Mᴾ) (Lᴵ · Mᴵ)
application-semantic-bounded {Aᴾ = Aᴾ} {Aᴵ = Aᴵ}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {W = W} {Γ = Γ} {p = p} {q = q}
    {Lᴾ = Lᴾ} {Mᴾ = Mᴾ} {Lᴵ = Lᴵ} {Mᴵ = Mᴵ}
    k L-related M-related W′ W≼W′ γ =
  ClosureProof.computations-related-reindex
    (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
    refl refl (sym imprecise-application-eq)
    (sym precise-application-eq)
    (record
      { forward-return = forward
      ; backward-return = backward
      ; forward-blame = forwardBlame
      })
  where
  Lᴵ′ = close (impreciseClosingSubstitution γ)
    (liftImpreciseTerm W≼W′ Lᴵ)
  Mᴵ′ = close (impreciseClosingSubstitution γ)
    (liftImpreciseTerm W≼W′ Mᴵ)
  Lᴾ′ = close (preciseClosingSubstitution γ)
    (liftPreciseTerm W≼W′ Lᴾ)
  Mᴾ′ = close (preciseClosingSubstitution γ)
    (liftPreciseTerm W≼W′ Mᴾ)

  imprecise-application-eq : close (impreciseClosingSubstitution γ)
      (liftImpreciseTerm W≼W′ (Lᴵ · Mᴵ)) ≡ Lᴵ′ · Mᴵ′
  imprecise-application-eq = cong
    (close (impreciseClosingSubstitution γ))
    (lift-imprecise-application W≼W′ Lᴵ Mᴵ)

  precise-application-eq : close (preciseClosingSubstitution γ)
      (liftPreciseTerm W≼W′ (Lᴾ · Mᴾ)) ≡ Lᴾ′ · Mᴾ′
  precise-application-eq = cong
    (close (preciseClosingSubstitution γ))
    (lift-precise-application W≼W′ Lᴾ Mᴾ)

  function-related = L-related k ≤-refl W′ W≼W′ γ

  forward : ∀ {n} {resultᴵ : E.EvalResult (Lᴵ′ · Mᴵ′)}
    → n ≤ k
    → interpretFrom (impreciseStore (core W′)) n (Lᴵ′ · Mᴵ′)
        ≡ returned resultᴵ
    →
      (Σ[ m ∈ ℕ ]
       Σ[ resultᴾ ∈ E.EvalResult (Lᴾ′ · Mᴾ′) ]
         interpretFrom (preciseStore (core W′)) m (Lᴾ′ · Mᴾ′)
           ≡ returned resultᴾ
         × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ q))
            (k ∸ n) resultᴵ resultᴾ)
      ⊎
      (Σ[ m ∈ ℕ ]
        BlamesFrom (preciseStore (core W′)) m (Lᴾ′ · Mᴾ′))
  forward {n} n≤k result-eq
      with application-return-phases
        {Σ = impreciseStore (core W′)} result-eq
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      with forward-return function-related
        (first-phase≤ {a = functionGas} {argumentGas} {callGas}
          (subst≤ gas-split n≤k)) functionReturn
    where
    subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
    subst≤ refl a≤k = a≤k
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseGas , preciseBlame)
      with function-blame-expand {Σ = preciseStore (core W′)}
        {functionGas = preciseGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseBlame
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₂ (preciseGas , preciseBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-return argument-related argumentGas≤ argumentPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    argumentGas≤ = second-phase≤
      {a = functionGas} {argumentGas} {callGas} phases≤

    raw-argument-related = compiled-component-future-at
      (M-related (k ∸ functionGas) (m∸n≤m k functionGas))
      W≼W′ γ W′≼W₁ (m∸n≤m k functionGas)

    argument-related = ClosureProof.computations-related-reindex
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      refl refl (sym (functionTermsᴵ Mᴵ′))
      (sym (functionTermsᴾ Mᴾ′)) raw-argument-related

    argumentPhaseReturn =
      return-store-reindex {gas = argumentGas}
        {M = E.changes functionResult ▶ᵀ Mᴵ′}
        functionStoreᴵ argumentReturn
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseArgumentGas , preciseArgumentBlame)
      with application-argument-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn
        (blame-store-reindex {gas = preciseArgumentGas}
          {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
          (sym functionStoreᴾ) preciseArgumentBlame)
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseArgumentGas , preciseArgumentBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      with forward-return call-related callGas≤ callPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    callGas≤ = third-phase≤
      {a = functionGas} {argumentGas} {callGas} phases≤

    pAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ p)

    qAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ q)

    explicitArrowAtW₁ = I.⇒⊑⇒ pAtW₁ qAtW₁

    sequentialArrowAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))

    preciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedPrecise (core W) Aᴾ)
          (embedPrecise (core W) Bᴾ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ))
        (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))

    impreciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedImprecise (core W) Aᴵ)
          (embedImprecise (core W) Bᴵ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ))
        (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))

    explicitFunctionAtW₁ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₁ sequentialArrowAtW₁
      (sym preciseArrowAtW₁) (sym impreciseArrowAtW₁)
      functionValueRelated

    pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
    qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
    explicitArrowAtW₂ = I.⇒⊑⇒ pAtW₂ qAtW₂
    liftedArrowAtW₂ = liftCenterImprecision W₁≼W₂
      explicitArrowAtW₁

    explicitFunctionAtW₂ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₂ liftedArrowAtW₂
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))))
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))))
      (value-imprecision-future W₁≼W₂
        (value-imprecision-downward-to
          (m∸n≤m (k ∸ functionGas) argumentGas)
          explicitFunctionAtW₁))

    functionValueAtCall = value-terms-reindex
      (argumentTermsᴵ (E.term functionResult))
      (argumentTermsᴾ (E.term preciseFunctionResult))
      explicitFunctionAtW₂

    residual-positive = ≤-trans
      (application-return-positive≤
        {Σ = E.changes argumentResult ▶ˢ
          (E.changes functionResult ▶ˢ impreciseStore (core W′))}
        callReturn)
      callGas≤

    call-related = positive-function-application residual-positive
      functionValueAtCall argumentValueRelated

    callStoreᴵ = trans argumentStoreᴵ
      (cong (λ Σ → E.changes argumentResult ▶ˢ Σ) functionStoreᴵ)

    callPhaseReturn = return-store-reindex {gas = callGas}
      {M = (E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult}
      callStoreᴵ callReturn
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      with application-call-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas}
        {callGas = preciseCallGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn preciseArgumentPhaseReturn
        preciseCallPhaseBlame
    where
    preciseArgumentPhaseReturn = return-store-reindex
      {gas = preciseArgumentGas}
      {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
      (sym functionStoreᴾ) preciseArgumentReturn

    callStoreᴾ = trans argumentStoreᴾ
      (cong (λ Σ → E.changes preciseArgumentResult ▶ˢ Σ)
        functionStoreᴾ)

    preciseCallPhaseBlame = blame-store-reindex
      {gas = preciseCallGas}
      {M = (E.changes preciseArgumentResult ▶ᵀ
        E.term preciseFunctionResult) · E.term preciseArgumentResult}
      (sym callStoreᴾ) preciseCallBlame
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | inj₂ (preciseCallGas , preciseCallBlame)
      | wholeGas , wholeBlame = inj₂ (wholeGas , wholeBlame)
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          paired-returns W₃ W₂≼W₃ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      with application-return-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas}
        {callGas = preciseCallGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn preciseArgumentPhaseReturn
        preciseCallPhaseReturn
    where
    preciseArgumentPhaseReturn = return-store-reindex
      {gas = preciseArgumentGas}
      {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
      (sym functionStoreᴾ) preciseArgumentReturn

    callStoreFromInitialᴾ = trans argumentStoreᴾ
      (cong (λ Σ → E.changes preciseArgumentResult ▶ˢ Σ)
        functionStoreᴾ)

    preciseCallPhaseReturn = return-store-reindex
      {gas = preciseCallGas}
      {M = (E.changes preciseArgumentResult ▶ᵀ
        E.term preciseFunctionResult) · E.term preciseArgumentResult}
      (sym callStoreFromInitialᴾ) preciseCallReturn
  forward {n} n≤k result-eq
      | return-phases functionGas functionResult functionReturn
          argumentGas argumentResult argumentReturn
          callGas callResult callReturn result-split gas-split
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | inj₁ (preciseCallGas , preciseCallResult , preciseCallReturn ,
          paired-returns W₃ W₂≼W₃ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated)
      | wholeGas , preciseWholeReturn =
        inj₁ (wholeGas , preciseApplicationResult , preciseWholeReturn ,
          paired-returns-reindex result-split refl assembledPair)
    where
    preciseApplicationResult = sequence-application-result
      preciseFunctionResult preciseArgumentResult preciseCallResult

    indexEq = trans (subtract-three k functionGas argumentGas callGas)
      (cong (k ∸_) gas-split)

    assembledPair = assemble-application-pair
      {W₀ = W′} {q = liftCenterImprecision W≼W′ q}
      {Lᴾ = Lᴾ′} {Mᴾ = Mᴾ′} {Lᴵ = Lᴵ′} {Mᴵ = Mᴵ′}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = functionResult}
      {argumentResultᴾ = preciseArgumentResult}
      {argumentResultᴵ = argumentResult}
      {callResultᴾ = preciseCallResult} {callResultᴵ = callResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ
      W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
      argumentTermsᴵ argumentTermsᴾ
      W₂≼W₃ callStoreᴵ callStoreᴾ callTermsᴵ callTermsᴾ indexEq
      callValueRelated

  backward : ∀ {n} {resultᴾ : E.EvalResult (Lᴾ′ · Mᴾ′)}
    → n ≤ k
    → interpretFrom (preciseStore (core W′)) n (Lᴾ′ · Mᴾ′)
        ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ]
      Σ[ resultᴵ ∈ E.EvalResult (Lᴵ′ · Mᴵ′) ]
        interpretFrom (impreciseStore (core W′)) m (Lᴵ′ · Mᴵ′)
          ≡ returned resultᴵ
        × PairedReturns W′
            (FutureValueRelation (liftCenterImprecision W≼W′ q))
            (k ∸ n) resultᴵ resultᴾ
  backward {n} n≤k result-eq
      with application-return-phases
        {Σ = preciseStore (core W′)} result-eq
  backward {n} n≤k result-eq
      | return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseArgumentGas preciseArgumentResult
          preciseArgumentReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      with backward-return function-related functionGas≤
        preciseFunctionReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    functionGas≤ = first-phase≤
      {a = preciseFunctionGas} {preciseArgumentGas} {preciseCallGas}
      phases≤
  backward {n} n≤k result-eq
      | return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseArgumentGas preciseArgumentResult
          preciseArgumentReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      with backward-return argument-related argumentGas≤
        argumentPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    argumentGas≤ = second-phase≤
      {a = preciseFunctionGas} {preciseArgumentGas} {preciseCallGas}
      phases≤

    raw-argument-related = compiled-component-future-at
      (M-related (k ∸ preciseFunctionGas)
        (m∸n≤m k preciseFunctionGas))
      W≼W′ γ W′≼W₁ (m∸n≤m k preciseFunctionGas)

    argument-related = ClosureProof.computations-related-reindex
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      refl refl (sym (functionTermsᴵ Mᴵ′))
      (sym (functionTermsᴾ Mᴾ′)) raw-argument-related

    argumentPhaseReturn = return-store-reindex
      {gas = preciseArgumentGas}
      {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
      functionStoreᴾ preciseArgumentReturn
  backward {n} n≤k result-eq
      | return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseArgumentGas preciseArgumentResult
          preciseArgumentReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | argumentGas , argumentResult , argumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated
      with backward-return call-related callGas≤ callPhaseReturn
    where
    phases≤ = subst≤ gas-split n≤k
      where
      subst≤ : ∀ {a b} → a ≡ b → b ≤ k → a ≤ k
      subst≤ refl a≤k = a≤k

    callGas≤ = third-phase≤
      {a = preciseFunctionGas} {preciseArgumentGas} {preciseCallGas}
      phases≤

    pAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ p)

    qAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ q)

    explicitArrowAtW₁ = I.⇒⊑⇒ pAtW₁ qAtW₁

    sequentialArrowAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))

    preciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedPrecise (core W) Aᴾ)
          (embedPrecise (core W) Bᴾ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ))
        (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))

    impreciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedImprecise (core W) Aᴵ)
          (embedImprecise (core W) Bᴵ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ))
        (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))

    explicitFunctionAtW₁ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₁ sequentialArrowAtW₁
      (sym preciseArrowAtW₁) (sym impreciseArrowAtW₁)
      functionValueRelated

    pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
    qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
    explicitArrowAtW₂ = I.⇒⊑⇒ pAtW₂ qAtW₂
    liftedArrowAtW₂ = liftCenterImprecision W₁≼W₂
      explicitArrowAtW₁

    explicitFunctionAtW₂ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₂ liftedArrowAtW₂
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))))
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))))
      (value-imprecision-future W₁≼W₂
        (value-imprecision-downward-to
          (m∸n≤m (k ∸ preciseFunctionGas) preciseArgumentGas)
          explicitFunctionAtW₁))

    functionValueAtCall = value-terms-reindex
      (argumentTermsᴵ (E.term functionResult))
      (argumentTermsᴾ (E.term preciseFunctionResult))
      explicitFunctionAtW₂

    residual-positive = ≤-trans
      (application-return-positive≤
        {Σ = E.changes preciseArgumentResult ▶ˢ
          (E.changes preciseFunctionResult ▶ˢ preciseStore (core W′))}
        preciseCallReturn)
      callGas≤

    call-related = positive-function-application residual-positive
      functionValueAtCall argumentValueRelated

    callStoreᴾ = trans argumentStoreᴾ
      (cong (λ Σ → E.changes preciseArgumentResult ▶ˢ Σ)
        functionStoreᴾ)

    callPhaseReturn = return-store-reindex
      {gas = preciseCallGas}
      {M = (E.changes preciseArgumentResult ▶ᵀ
        E.term preciseFunctionResult) · E.term preciseArgumentResult}
      callStoreᴾ preciseCallReturn
  backward {n} n≤k result-eq
      | return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseArgumentGas preciseArgumentResult
          preciseArgumentReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | argumentGas , argumentResult , argumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated
      | callGas , callResult , callReturn ,
          paired-returns W₃ W₂≼W₃ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      with application-return-expand
        {Σ = impreciseStore (core W′)} {functionGas = functionGas}
        {argumentGas = argumentGas} {callGas = callGas}
        {L = Lᴵ′} {M = Mᴵ′}
        functionReturn argumentPhaseReturn callPhaseReturn
    where
    argumentPhaseReturn = return-store-reindex
      {gas = argumentGas} {M = E.changes functionResult ▶ᵀ Mᴵ′}
      (sym functionStoreᴵ) argumentReturn

    callStoreFromInitialᴵ = trans argumentStoreᴵ
      (cong (λ Σ → E.changes argumentResult ▶ˢ Σ) functionStoreᴵ)

    callPhaseReturn = return-store-reindex
      {gas = callGas}
      {M = (E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult}
      (sym callStoreFromInitialᴵ) callReturn
  backward {n} n≤k result-eq
      | return-phases preciseFunctionGas preciseFunctionResult
          preciseFunctionReturn preciseArgumentGas preciseArgumentResult
          preciseArgumentReturn preciseCallGas preciseCallResult
          preciseCallReturn result-split gas-split
      | functionGas , functionResult , functionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated
      | argumentGas , argumentResult , argumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated
      | callGas , callResult , callReturn ,
          paired-returns W₃ W₂≼W₃ callStoreᴵ callStoreᴾ
            callTermsᴵ callTermsᴾ callValueRelated
      | wholeGas , wholeReturn =
        wholeGas , impreciseApplicationResult , wholeReturn ,
          paired-returns-reindex refl result-split assembledPair
    where
    impreciseApplicationResult = sequence-application-result
      functionResult argumentResult callResult

    indexEq = trans
      (subtract-three k preciseFunctionGas preciseArgumentGas
        preciseCallGas)
      (cong (k ∸_) gas-split)

    assembledPair = assemble-application-pair
      {W₀ = W′}
      {q = liftCenterImprecision W≼W′ q}
      {Lᴾ = Lᴾ′} {Mᴾ = Mᴾ′} {Lᴵ = Lᴵ′} {Mᴵ = Mᴵ′}
      {functionResultᴾ = preciseFunctionResult}
      {functionResultᴵ = functionResult}
      {argumentResultᴾ = preciseArgumentResult}
      {argumentResultᴵ = argumentResult}
      {callResultᴾ = preciseCallResult} {callResultᴵ = callResult}
      W′≼W₁ functionStoreᴵ functionStoreᴾ
      functionTermsᴵ functionTermsᴾ
      W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
      argumentTermsᴵ argumentTermsᴾ
      W₂≼W₃ callStoreᴵ callStoreᴾ callTermsᴵ callTermsᴾ indexEq
      callValueRelated

  forwardBlame : ∀ {n}
    → n ≤ k
    → BlamesFrom (impreciseStore (core W′)) n (Lᴵ′ · Mᴵ′)
    → Σ[ m ∈ ℕ ]
      BlamesFrom (preciseStore (core W′)) m (Lᴾ′ · Mᴾ′)
  forwardBlame {n} n≤k blaming
      with application-blame-phases {Σ = impreciseStore (core W′)}
        {gas = n} {L = Lᴵ′} {M = Mᴵ′} blaming
  forwardBlame {n} n≤k blaming
      | function-phase-blames functionGas functionBlame functionGas≤
      with forward-blame function-related
        (≤-trans functionGas≤ n≤k) functionBlame
  forwardBlame {n} n≤k blaming
      | function-phase-blames functionGas functionBlame functionGas≤
      | preciseFunctionGas , preciseFunctionBlame
      with function-blame-expand
        {Σ = preciseStore (core W′)} {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {M = Mᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | function-phase-blames functionGas functionBlame functionGas≤
      | preciseFunctionGas , preciseFunctionBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      with forward-return function-related functionGas≤ functionReturn
    where
    phases≤k = ≤-trans phases≤n n≤k

    functionGas≤ : functionGas ≤ k
    functionGas≤ = first-of-two≤ phases≤k
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      with function-blame-expand
        {Σ = preciseStore (core W′)} {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {M = Mᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-blame argument-related argumentGas≤
        argumentPhaseBlame
    where
    phases≤k = ≤-trans phases≤n n≤k

    argumentGas≤ : argumentGas ≤ k ∸ functionGas
    argumentGas≤ = drop-left-≤ phases≤k

    raw-argument-related = compiled-component-future-at
      (M-related (k ∸ functionGas) (m∸n≤m k functionGas))
      W≼W′ γ W′≼W₁ (m∸n≤m k functionGas)

    argument-related = ClosureProof.computations-related-reindex
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      refl refl (sym (functionTermsᴵ Mᴵ′))
      (sym (functionTermsᴾ Mᴾ′)) raw-argument-related

    argumentPhaseBlame = blame-store-reindex
      {gas = argumentGas} {M = E.changes functionResult ▶ᵀ Mᴵ′}
      functionStoreᴵ argumentBlame
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | preciseArgumentGas , preciseArgumentBlame
      with application-argument-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn
        (blame-store-reindex {gas = preciseArgumentGas}
          {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
          (sym functionStoreᴾ) preciseArgumentBlame)
  forwardBlame {n} n≤k blaming
      | application-argument-phase-blames functionGas functionResult
          functionReturn argumentGas argumentBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | preciseArgumentGas , preciseArgumentBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      with forward-return function-related functionGas≤ functionReturn
    where
    phases≤k = ≤-trans phases≤n n≤k

    functionGas≤ = first-phase≤
      {a = functionGas} {argumentGas} {callGas} phases≤k
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      with function-blame-expand
        {Σ = preciseStore (core W′)} {functionGas = preciseFunctionGas}
        {L = Lᴾ′} {M = Mᴾ′} preciseFunctionBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₂ (preciseFunctionGas , preciseFunctionBlame)
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      with forward-return argument-related argumentGas≤
        argumentPhaseReturn
    where
    phases≤k = ≤-trans phases≤n n≤k

    argumentGas≤ = second-phase≤
      {a = functionGas} {argumentGas} {callGas} phases≤k

    raw-argument-related = compiled-component-future-at
      (M-related (k ∸ functionGas) (m∸n≤m k functionGas))
      W≼W′ γ W′≼W₁ (m∸n≤m k functionGas)

    argument-related = ClosureProof.computations-related-reindex
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      (liftCenterImprecision W′≼W₁
        (liftCenterImprecision W≼W′ p))
      refl refl (sym (functionTermsᴵ Mᴵ′))
      (sym (functionTermsᴾ Mᴾ′)) raw-argument-related

    argumentPhaseReturn = return-store-reindex {gas = argumentGas}
      {M = E.changes functionResult ▶ᵀ Mᴵ′}
      functionStoreᴵ argumentReturn
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseArgumentGas , preciseArgumentBlame)
      with application-argument-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn
        (blame-store-reindex {gas = preciseArgumentGas}
          {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
          (sym functionStoreᴾ) preciseArgumentBlame)
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₂ (preciseArgumentGas , preciseArgumentBlame)
      | wholeGas , wholeBlame = wholeGas , wholeBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      with forward-blame call-related callGas≤ callPhaseBlame
    where
    phases≤k = ≤-trans phases≤n n≤k

    callGas≤ = third-phase≤
      {a = functionGas} {argumentGas} {callGas} phases≤k

    pAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ p)

    qAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ q)

    explicitArrowAtW₁ = I.⇒⊑⇒ pAtW₁ qAtW₁

    sequentialArrowAtW₁ = liftCenterImprecision W′≼W₁
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p q))

    preciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedPrecise (core W) Aᴾ)
          (embedPrecise (core W) Bᴾ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ))
        (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))

    impreciseArrowAtW₁ = trans
      (cong (liftCenterTy W′≼W₁)
        (liftCenterTy-arrow W≼W′
          (embedImprecise (core W) Aᴵ)
          (embedImprecise (core W) Bᴵ)))
      (liftCenterTy-arrow W′≼W₁
        (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ))
        (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))

    explicitFunctionAtW₁ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₁ sequentialArrowAtW₁
      (sym preciseArrowAtW₁) (sym impreciseArrowAtW₁)
      functionValueRelated

    pAtW₂ = liftCenterImprecision W₁≼W₂ pAtW₁
    qAtW₂ = liftCenterImprecision W₁≼W₂ qAtW₁
    explicitArrowAtW₂ = I.⇒⊑⇒ pAtW₂ qAtW₂
    liftedArrowAtW₂ = liftCenterImprecision W₁≼W₂
      explicitArrowAtW₁

    explicitFunctionAtW₂ = ClosureProof.value-imprecision-reindex
      explicitArrowAtW₂ liftedArrowAtW₂
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedPrecise (core W) Bᴾ)))))
      (sym (liftCenterTy-arrow W₁≼W₂
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Aᴵ)))
        (liftCenterTy W′≼W₁
          (liftCenterTy W≼W′ (embedImprecise (core W) Bᴵ)))))
      (value-imprecision-future W₁≼W₂
        (value-imprecision-downward-to
          (m∸n≤m (k ∸ functionGas) argumentGas)
          explicitFunctionAtW₁))

    functionValueAtCall = value-terms-reindex
      (argumentTermsᴵ (E.term functionResult))
      (argumentTermsᴾ (E.term preciseFunctionResult))
      explicitFunctionAtW₂

    residual-positive = ≤-trans
      (application-blame-positive≤
        {Σ = E.changes argumentResult ▶ˢ
          (E.changes functionResult ▶ˢ impreciseStore (core W′))}
        callBlame)
      callGas≤

    call-related = positive-function-application residual-positive
      functionValueAtCall argumentValueRelated

    callStoreᴵ = trans argumentStoreᴵ
      (cong (λ Σ → E.changes argumentResult ▶ˢ Σ) functionStoreᴵ)

    callPhaseBlame = blame-store-reindex
      {gas = callGas}
      {M = (E.changes argumentResult ▶ᵀ E.term functionResult)
        · E.term argumentResult}
      callStoreᴵ callBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | preciseCallGas , preciseCallBlame
      with application-call-blame-expand
        {Σ = preciseStore (core W′)}
        {functionGas = preciseFunctionGas}
        {argumentGas = preciseArgumentGas}
        {callGas = preciseCallGas} {L = Lᴾ′} {M = Mᴾ′}
        preciseFunctionReturn preciseArgumentPhaseReturn
        preciseCallPhaseBlame
    where
    preciseArgumentPhaseReturn = return-store-reindex
      {gas = preciseArgumentGas}
      {M = E.changes preciseFunctionResult ▶ᵀ Mᴾ′}
      (sym functionStoreᴾ) preciseArgumentReturn

    callStoreᴾ = trans argumentStoreᴾ
      (cong (λ Σ → E.changes preciseArgumentResult ▶ˢ Σ)
        functionStoreᴾ)

    preciseCallPhaseBlame = blame-store-reindex
      {gas = preciseCallGas}
      {M = (E.changes preciseArgumentResult ▶ᵀ
        E.term preciseFunctionResult) · E.term preciseArgumentResult}
      (sym callStoreᴾ) preciseCallBlame
  forwardBlame {n} n≤k blaming
      | application-call-phase-blames functionGas functionResult
          functionReturn argumentGas argumentResult argumentReturn
          callGas callBlame phases≤n
      | inj₁ (preciseFunctionGas , preciseFunctionResult ,
          preciseFunctionReturn ,
          paired-returns W₁ W′≼W₁ functionStoreᴵ functionStoreᴾ
            functionTermsᴵ functionTermsᴾ functionValueRelated)
      | inj₁ (preciseArgumentGas , preciseArgumentResult ,
          preciseArgumentReturn ,
          paired-returns W₂ W₁≼W₂ argumentStoreᴵ argumentStoreᴾ
            argumentTermsᴵ argumentTermsᴾ argumentValueRelated)
      | preciseCallGas , preciseCallBlame
      | wholeGas , wholeBlame = wholeGas , wholeBlame

application-compatible : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ Bᴾ Bᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {Γ : CTI.CtxImp (forgetWorld W)}
    {p : Aᴾ ⊑ᵂ⟨ core W ⟩ Aᴵ}
    {q : Bᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ}
    {Lᴾ Mᴾ : Term Δᴾ} {Lᴵ Mᴵ : Term Δᴵ}
  → forgetWorld W ∣ Γ ⊢² Lᴾ ⊑ Lᴵ ∶ I.⇒⊑⇒ p q
  → forgetWorld W ∣ Γ ⊢² Mᴾ ⊑ Mᴵ ∶ p
  → (∀ k → CompiledTermRelation {W = W}
      (I.⇒⊑⇒ p q) k Γ Lᴾ Lᴵ)
  → (∀ k → CompiledTermRelation {W = W} p k Γ Mᴾ Mᴵ)
  → ∀ k → CompiledTermRelation {W = W} q k Γ
      (Lᴾ · Mᴾ) (Lᴵ · Mᴵ)
application-compatible L⊑ M⊑ L-related M-related k =
  application-semantic-bounded k
    (λ j j≤k → L-related j)
    (λ j j≤k → M-related j)
