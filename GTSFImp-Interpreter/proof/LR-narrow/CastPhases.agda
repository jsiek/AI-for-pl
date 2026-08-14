module proof.LR-narrow.CastPhases where

-- File Charter:
--   * Decomposes cast evaluation into operand and returned-value phases.
--   * Reassembles return and blame observations through a cast frame.
--   * Contains no logical-relation-specific reasoning.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
import Consistency as C
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.Reduction using (cast-↠)
open import proof.LR-narrow.ImmediateReturn using
  (value-question-complete)
open import proof.LR-narrow.BetaExpansion using
  (interpret-from-eval; interpreter-outcome; value-step-none)
open import proof.LR-narrow.Application using
  (_++ˢ_; BlameView; is-blame; not-blame; blame-view; append-trace;
   apply-change-value; blame-from-eval; eval-from-blame;
   eval-from-return; eval-from-nonblame; eval-prepend-blamed;
   eval-prepend-return;
   prepend-blamed; prepend-result; prepend-return; return-from-eval;
   value-return-exact)

cast-operand-trace : ∀ {Δ₀ Δ₁} {M : Term Δ₀} {V : Term Δ₁}
    {μ : C.Env∼ Δ₀} {A B : Ty Δ₀} {c : μ C.⊢ A ∼ B}
    {χs : StoreChanges Δ₀ Δ₁}
  → M —↠[ χs ] V
  → M ⟨ c ⟩ —↠[ χs ] V ⟨ χs ▶ᶜ c ⟩
cast-operand-trace {c = c} = cast-↠ c

sequence-cast-result : ∀ {Δ₀} {M : Term Δ₀}
    {μ : C.Env∼ Δ₀} {A B : Ty Δ₀} {c : μ C.⊢ A ∼ B}
  → (operandResult : E.EvalResult M)
  → E.EvalResult
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)
  → E.EvalResult (M ⟨ c ⟩)
sequence-cast-result
    (E.result Δ₁ χs V M↠V vV)
    (E.result Δ₂ ψs Z call↠Z vZ) =
  E.result Δ₂ (χs ++ˢ ψs) Z
    (append-trace (cast-operand-trace M↠V) call↠Z) vZ

record CastReturnPhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (M : Term Δ)
    {μ : C.Env∼ Δ} {A B : Ty Δ} (c : μ C.⊢ A ∼ B)
    (wholeResult : E.EvalResult (M ⟨ c ⟩)) : Set where
  constructor cast-return-phases-record
  field
    operandGas : ℕ
    operandResult : E.EvalResult M
    operandReturn :
      interpretFrom Σ operandGas M ≡ returned operandResult

    callGas : ℕ
    callResult : E.EvalResult
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)
    callReturn :
      interpretFrom (E.changes operandResult ▶ˢ Σ) callGas
        (E.term operandResult
          ⟨ E.changes operandResult ▶ᶜ c ⟩) ≡ returned callResult

    result-splits : wholeResult ≡
      sequence-cast-result operandResult callResult
    gas-splits : operandGas + callGas ≡ gas

open CastReturnPhases public

record CastReturned {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (M : Term Δ)
    {μ : C.Env∼ Δ} {A B : Ty Δ} (c : μ C.⊢ A ∼ B)
    (result : E.EvalResult (M ⟨ c ⟩)) : Set where
  constructor cast-returned
  field
    castReturn : interpretFrom Σ gas (M ⟨ c ⟩) ≡ returned result

open CastReturned public

record CastBlamed {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (M : Term Δ)
    {μ : C.Env∼ Δ} {A B : Ty Δ} (c : μ C.⊢ A ∼ B) : Set where
  constructor cast-blamed
  field
    castBlame : BlamesFrom Σ gas (M ⟨ c ⟩)

open CastBlamed public

cast-operand-step-question : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {M : Term Δ} {χ : StoreChange Δ Δ′} {N : Term Δ′}
    {step : M —→[ χ ] N}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → E.step? Σ (M ⟨ c ⟩) ≡
      just (E.step-result χ (N ⟨ χ ▷ᶜ c ⟩)
        (ξ-⟨⟩ step refl))
cast-operand-step-question operand-step-eq
    rewrite operand-step-eq = refl

cast-final-none : ∀ {Δ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.cast-redex? M c ≡ nothing
cast-final-none {M = ` x} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = C.id a} M≢blame ()
cast-final-none {M = L · M} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = Λ N} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = $ κ} {c = C.id a} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = C.id a} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = blame} {c = C.id a} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = c C.↦ d} M≢blame value-eq = refl
cast-final-none {M = ƛ N} {c = c C.↦ d} M≢blame ()
cast-final-none {M = L · M} {c = c C.↦ d} M≢blame value-eq = refl
cast-final-none {M = Λ N} {c = c C.↦ d} M≢blame value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = c C.↦ d}
    M≢blame value-eq = refl
cast-final-none {M = $ κ} {c = c C.↦ d} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = c C.↦ d}
    M≢blame value-eq = refl
cast-final-none {M = M ⟨ e ⟩} {c = c C.↦ d}
    M≢blame value-eq = refl
cast-final-none {M = M ↑ e} {c = c C.↦ d} M≢blame value-eq = refl
cast-final-none {M = M ↓ e} {c = c C.↦ d} M≢blame value-eq = refl
cast-final-none {M = blame} {c = c C.↦ d} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = C.∀ᶜ c} M≢blame value-eq = refl
cast-final-none {M = ƛ N} {c = C.∀ᶜ c} M≢blame ()
cast-final-none {M = L · M} {c = C.∀ᶜ c} M≢blame value-eq = refl
cast-final-none {M = Λ N} {c = C.∀ᶜ c} M≢blame value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = C.∀ᶜ c}
    M≢blame value-eq = refl
cast-final-none {M = $ κ} {c = C.∀ᶜ c} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = C.∀ᶜ c}
    M≢blame value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = C.∀ᶜ c}
    M≢blame value-eq = refl
cast-final-none {M = M ↑ d} {c = C.∀ᶜ c} M≢blame value-eq = refl
cast-final-none {M = M ↓ d} {c = C.∀ᶜ c} M≢blame value-eq = refl
cast-final-none {M = blame} {c = C.∀ᶜ c} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = c C.!} M≢blame ()
cast-final-none {M = L · M} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = Λ N} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = $ κ} {c = c C.!} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = c C.!} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = blame} {c = c C.!} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = C.？ c} M≢blame ()
cast-final-none {M = L · M} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = Λ N} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = $ κ} {c = C.？ c} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = C.？ c} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = blame} {c = C.？ c} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = (C.inst c) B≢★} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = (C.inst c) B≢★} M≢blame ()
cast-final-none {M = L · M} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = Λ N} {c = (C.inst c) B≢★} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = $ κ} {c = (C.inst c) B≢★} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = (C.inst c) B≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = blame} {c = (C.inst c) B≢★}
    M≢blame value-eq = ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = (C.gen c) A≢★} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = (C.gen c) A≢★} M≢blame ()
cast-final-none {M = L · M} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = Λ N} {c = (C.gen c) A≢★} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = $ κ} {c = (C.gen c) A≢★} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = (C.gen c) A≢★}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = blame} {c = (C.gen c) A≢★}
    M≢blame value-eq = ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = C.bot-elim} M≢blame value-eq = refl
cast-final-none {M = ƛ N} {c = C.bot-elim} M≢blame ()
cast-final-none {M = L · M} {c = C.bot-elim} M≢blame value-eq = refl
cast-final-none {M = Λ N} {c = C.bot-elim} M≢blame value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = C.bot-elim}
    M≢blame value-eq = refl
cast-final-none {M = $ κ} {c = C.bot-elim} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = C.bot-elim}
    M≢blame value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = C.bot-elim}
    M≢blame value-eq = refl
cast-final-none {M = M ↑ d} {c = C.bot-elim} M≢blame value-eq = refl
cast-final-none {M = M ↓ d} {c = C.bot-elim} M≢blame value-eq = refl
cast-final-none {M = blame} {c = C.bot-elim} M≢blame value-eq =
  ⊥-elim (M≢blame refl)
cast-final-none {M = ` x} {c = C.bot-intro} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = ƛ N} {c = C.bot-intro} M≢blame ()
cast-final-none {M = L · M} {c = C.bot-intro} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = Λ N} {c = C.bot-intro} M≢blame value-eq
    rewrite value-eq = refl
cast-final-none {M = L ⦂∀ B [ A ]} {c = C.bot-intro}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = $ κ} {c = C.bot-intro} M≢blame ()
cast-final-none {M = L ⊕[ op ] M} {c = C.bot-intro}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ⟨ d ⟩} {c = C.bot-intro}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↑ d} {c = C.bot-intro}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = M ↓ d} {c = C.bot-intro}
    M≢blame value-eq rewrite value-eq = refl
cast-final-none {M = blame} {c = C.bot-intro} M≢blame value-eq =
  ⊥-elim (M≢blame refl)

cast-stuck-step-none : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.step? Σ M ≡ nothing
  → E.value? M ≡ nothing
  → M ≢ blame
  → E.step? Σ (M ⟨ c ⟩) ≡ nothing
cast-stuck-step-none operand-step-eq operand-value-eq M≢blame
    rewrite operand-step-eq =
  cast-final-none M≢blame operand-value-eq

cast-operand-nonvalue : ∀ {Δ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.value? M ≡ nothing
  → E.value? (M ⟨ c ⟩) ≡ nothing
cast-operand-nonvalue {M = M} {c = c} value-eq
    rewrite value-eq = refl

eval-cast-stuck-none : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ}
    {c : μ C.⊢ A ∼ B}
  → E.step? Σ (M ⟨ c ⟩) ≡ nothing
  → E.value? (M ⟨ c ⟩) ≡ nothing
  → E.evalFrom Σ (suc gas) (M ⟨ c ⟩) ≡ nothing
eval-cast-stuck-none {Σ = Σ} {gas = gas} {M = M} {c = c}
    step-eq value-eq
    with E.value? (M ⟨ c ⟩) | value-eq
eval-cast-stuck-none {Σ = Σ} {M = M} {c = c}
    step-eq value-eq | nothing | refl
    with E.step? Σ (M ⟨ c ⟩) | step-eq
eval-cast-stuck-none step-eq value-eq | nothing | refl
    | nothing | refl = refl

eval-blame-cast : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → E.evalFrom Σ (suc gas) (blame ⟨ c ⟩) ≡
      just (E.blamed (keep ∷ [])
        (↠-step (pure-step blame-⟨⟩) ↠-refl))
eval-blame-cast {Σ = Σ} {gas = zero} = refl
eval-blame-cast {Σ = Σ} {gas = suc gas} = refl

blame-cast-not-returned : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {result : E.EvalResult (blame ⟨ c ⟩)}
  → E.evalFrom Σ gas (blame ⟨ c ⟩) ≡ just (E.returned result)
  → ⊥
blame-cast-not-returned {gas = zero} ()
blame-cast-not-returned {Σ = Σ} {gas = suc gas} result-eq
    with trans (sym (eval-blame-cast {Σ = Σ} {gas = gas})) result-eq
blame-cast-not-returned result-eq | ()

cast-operand-stuck-impossible : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {result : E.EvalResult (M ⟨ c ⟩)}
  → E.step? Σ M ≡ nothing
  → E.value? M ≡ nothing
  → E.value? (M ⟨ c ⟩) ≡ nothing
  → E.evalFrom Σ (suc gas) (M ⟨ c ⟩) ≡ just (E.returned result)
  → ⊥
cast-operand-stuck-impossible {Σ = Σ} {gas = gas} {M = M}
    operand-step-eq operand-value-eq whole-value-eq result-eq
    with blame-view M
cast-operand-stuck-impossible {Σ = Σ} {gas = gas}
    operand-step-eq operand-value-eq whole-value-eq result-eq
    | is-blame refl =
  blame-cast-not-returned {Σ = Σ} {gas = suc gas} result-eq
cast-operand-stuck-impossible {Σ = Σ} {gas = gas}
    operand-step-eq operand-value-eq whole-value-eq result-eq
    | not-blame M≢blame = impossible
  where
  step-none = cast-stuck-step-none {Σ = Σ} operand-step-eq
    operand-value-eq M≢blame
  none-eq = eval-cast-stuck-none {Σ = Σ} {gas = gas}
    step-none whole-value-eq

  impossible : ⊥
  impossible with trans (sym none-eq) result-eq
  impossible | ()

cast-return-phases-eval : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ}
    {c : μ C.⊢ A ∼ B} {result : E.EvalResult (M ⟨ c ⟩)}
  → E.evalFrom Σ gas (M ⟨ c ⟩) ≡ just (E.returned result)
  → CastReturned Σ gas M c result
  → CastReturnPhases Σ gas M c result
cast-return-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    {result = result} result-eq result-return
    with E.value? (M ⟨ c ⟩) in whole-value-eq
cast-return-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    result-eq result-return | just (vM 《 inert 》)
    with value-return-exact {Σ = Σ} gas (vM 《 inert 》)
cast-return-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    result-eq result-return | just (vM 《 inert 》) | whole-return
    with trans (sym whole-return) (castReturn result-return)
cast-return-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    result-eq result-return | just (vM 《 inert 》)
    | whole-return | refl =
  cast-return-phases-record zero (E.result _ [] M ↠-refl vM)
    (value-return-exact {Σ = Σ} zero vM)
    gas _ whole-return refl refl
cast-return-phases-eval {gas = zero} result-eq result-return | nothing
    rewrite whole-value-eq
    with result-eq
cast-return-phases-eval result-eq result-return | nothing | ()
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing
    with E.value? M in operand-value-eq
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | just vM
    rewrite operand-value-eq | whole-value-eq
      | value-step-none {Σ = Σ} vM =
  cast-return-phases-record zero (E.result _ [] M ↠-refl vM)
    (value-return-exact {Σ = Σ} zero vM)
    (suc gas) _
    (castReturn result-return)
    refl refl
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    with E.step? Σ M in operand-step-eq
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas (N ⟨ χ ▷ᶜ c ⟩) in next-eq
cast-return-phases-eval {Σ = Σ} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step) | nothing
    rewrite cast-operand-step-question {Σ = Σ} {M = M} {c = c}
        operand-step-eq
      | whole-value-eq | next-eq
    with result-eq
cast-return-phases-eval result-eq result-return | nothing | nothing
    | just (E.step-result χ N step) | nothing | ()
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    rewrite cast-operand-step-question {Σ = Σ} {M = M} {c = c}
        operand-step-eq
      | whole-value-eq | next-eq
    with result-eq
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    with cast-return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas}
      {M = N} {c = χ ▷ᶜ c} {result = next-result} next-eq
      (cast-returned
        (return-from-eval {Σ = χ ▷ˢ Σ} {gas = gas}
          {M = N ⟨ χ ▷ᶜ c ⟩} next-eq))
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.returned next-result) | refl
    | cast-return-phases-record operandGas operandResult operandReturn
        callGas callResult callReturn result-split gas-eq =
  cast-return-phases-record (suc operandGas)
    (prepend-result step operandResult)
    (prepend-return {Σ = Σ} {M = M} {gas = operandGas}
      operand-step-eq operandReturn)
    callGas callResult callReturn
    (cong (prepend-result (ξ-⟨⟩ step refl)) result-split)
    (cong suc gas-eq)
cast-return-phases-eval {Σ = Σ} {M = M} {c = c}
    result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)
    rewrite cast-operand-step-question {Σ = Σ} {M = M} {c = c}
        operand-step-eq
      | whole-value-eq | next-eq
    with result-eq
cast-return-phases-eval result-eq result-return | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed changes trace) | ()
cast-return-phases-eval {Σ = Σ} {gas = suc gas} {M = M} {c = c}
    result-eq result-return | nothing | nothing | nothing
    with blame-view M
cast-return-phases-eval {Σ = Σ} {gas = suc gas}
    result-eq result-return | nothing | nothing | nothing
    | is-blame refl =
  ⊥-elim (blame-cast-not-returned {Σ = Σ} {gas = suc gas} result-eq)
cast-return-phases-eval {M = M} {c = c}
    result-eq result-return | nothing | nothing | nothing
    | not-blame M≢blame
    rewrite operand-step-eq
      | cast-final-none {c = c} M≢blame operand-value-eq
      | cast-operand-nonvalue {c = c} operand-value-eq
    with result-eq
cast-return-phases-eval result-eq result-return | nothing | nothing | nothing
    | not-blame M≢blame | ()

cast-return-phases : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
    {M : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ}
    {c : μ C.⊢ A ∼ B} {result : E.EvalResult (M ⟨ c ⟩)}
  → interpretFrom Σ gas (M ⟨ c ⟩) ≡ returned result
  → CastReturnPhases Σ gas M c result
cast-return-phases {Σ = Σ} {gas = gas} {M = M} {c = c}
    result-eq =
  cast-return-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    (eval-from-return {Σ = Σ} {gas = gas} {M = M ⟨ c ⟩} result-eq)
    (cast-returned result-eq)

cast-return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
    {operandGas callGas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {operandResult : E.EvalResult M}
    {callResult : E.EvalResult
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)}
  → E.evalFrom Σ operandGas M ≡ just (E.returned operandResult)
  → E.evalFrom (E.changes operandResult ▶ˢ Σ) callGas
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩) ≡
      just (E.returned callResult)
  → Σ[ wholeGas ∈ ℕ ] E.evalFrom Σ wholeGas (M ⟨ c ⟩) ≡
      just (E.returned
        (sequence-cast-result operandResult callResult))
cast-return-expand-eval {Σ = Σ} {operandGas = zero}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    with blame-view M
cast-return-expand-eval operand-eq call-eq | is-blame refl
    with operand-eq
cast-return-expand-eval operand-eq call-eq | is-blame refl | ()
cast-return-expand-eval {Σ = Σ} {operandGas = zero}
    {callGas = callGas} {M = M} operand-eq call-eq
    | not-blame M≢blame
    with E.value? M in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           M≢blame)) operand-eq
cast-return-expand-eval {Σ = Σ} {callGas = callGas}
    operand-eq call-eq | not-blame M≢blame | just vM | refl
    rewrite value-step-none {Σ = Σ} vM | value-eq =
  callGas , call-eq
cast-return-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    with blame-view M
cast-return-expand-eval operand-eq call-eq | is-blame refl
    with operand-eq
cast-return-expand-eval operand-eq call-eq | is-blame refl | ()
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame
    with E.value? M in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc operandGas} M≢blame)) operand-eq
cast-return-expand-eval {Σ = Σ} {callGas = callGas}
    operand-eq call-eq | not-blame M≢blame | just vM | refl
    rewrite value-step-none {Σ = Σ} vM | value-eq =
  callGas , call-eq
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    with E.step? Σ M in operand-step-eq
cast-return-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | () | nothing
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
cast-return-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with cast-return-expand-eval {Σ = χ ▷ˢ Σ}
      {operandGas = operandGas} {callGas = callGas}
      {M = N} {c = χ ▷ᶜ c} {operandResult = next-result}
      next-eq call-eq
cast-return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
    {callGas = callGas} {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result) | wholeGas , whole-eq =
  suc wholeGas , eval-prepend-return {Σ = Σ}
    (cast-operand-step-question {Σ = Σ} operand-step-eq) whole-eq
cast-return-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed changes trace)

cast-return-expand : ∀ {Δ} {Σ : TyStore Δ}
    {operandGas callGas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {operandResult : E.EvalResult M}
    {callResult : E.EvalResult
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)}
  → interpretFrom Σ operandGas M ≡ returned operandResult
  → interpretFrom (E.changes operandResult ▶ˢ Σ) callGas
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩) ≡
      returned callResult
  → Σ[ wholeGas ∈ ℕ ] interpretFrom Σ wholeGas (M ⟨ c ⟩) ≡
      returned (sequence-cast-result operandResult callResult)
cast-return-expand {Σ = Σ} {operandGas = operandGas}
    {callGas = callGas} {M = M} {c = c}
    {operandResult = operandResult}
    operand-eq call-eq
    with cast-return-expand-eval {Σ = Σ} {operandGas = operandGas}
      {callGas = callGas} {M = M} {c = c}
      (eval-from-return {Σ = Σ} {gas = operandGas} {M = M} operand-eq)
      (eval-from-return {Σ = E.changes operandResult ▶ˢ Σ}
        {gas = callGas}
        {M = E.term operandResult
          ⟨ E.changes operandResult ▶ᶜ c ⟩}
        call-eq)
cast-return-expand {Σ = Σ} {M = M} {c = c}
    operand-eq call-eq | wholeGas , whole-eq =
  wholeGas , trans
    (interpret-from-eval {Σ = Σ} {gas = wholeGas} {M = M ⟨ c ⟩})
    (cong interpreter-outcome whole-eq)

data CastBlamePhases {Δ : TyCtx}
    (Σ : TyStore Δ) (gas : ℕ) (M : Term Δ)
    {μ : C.Env∼ Δ} {A B : Ty Δ} (c : μ C.⊢ A ∼ B) : Set where
  cast-operand-phase-blames :
      (operandGas : ℕ)
    → BlamesFrom Σ operandGas M
    → operandGas ≤ gas
    → CastBlamePhases Σ gas M c

  cast-call-phase-blames :
      (operandGas : ℕ)
    → (operandResult : E.EvalResult M)
    → interpretFrom Σ operandGas M ≡ returned operandResult
    → (callGas : ℕ)
    → BlamesFrom (E.changes operandResult ▶ˢ Σ) callGas
        (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)
    → operandGas + callGas ≤ gas
    → CastBlamePhases Σ gas M c

cast-operand-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {operandGas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {changes : StoreChanges Δ Δ′} {trace : M —↠[ changes ] blame}
  → E.evalFrom Σ operandGas M ≡ just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ M ⟨ c ⟩ —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (M ⟨ c ⟩) ≡
        just (E.blamed wholeChanges wholeTrace)
cast-operand-blame-expand-eval {Σ = Σ} {operandGas = zero}
    {M = M} {c = c} operand-eq with blame-view M
cast-operand-blame-expand-eval {Σ = Σ} operand-eq
    | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-⟨⟩) ↠-refl ,
    eval-blame-cast {Σ = Σ} {gas = zero}
cast-operand-blame-expand-eval {Σ = Σ} {operandGas = zero}
    {M = M} operand-eq | not-blame M≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} M≢blame
    with E.value? M
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | just vL with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | just vL | ()
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | ()
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq with blame-view M
cast-operand-blame-expand-eval {Σ = Σ} operand-eq
    | is-blame refl =
  1 , _ , keep ∷ [] , ↠-step (pure-step blame-⟨⟩) ↠-refl ,
    eval-blame-cast {Σ = Σ} {gas = zero}
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} operand-eq
    | not-blame M≢blame
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc operandGas}
      M≢blame
    with E.value? M in operand-value-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | just vL with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | just vL | ()
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq | not-blame M≢blame | nothing
    with E.step? Σ M in operand-step-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | nothing with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | nothing | ()
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step) | nothing
    with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step) | nothing | ()
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) with operand-eq
cast-operand-blame-expand-eval operand-eq | not-blame M≢blame
    | nothing | just (E.step-result χ N step)
    | just (E.returned next-result) | ()
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) with operand-eq
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with cast-operand-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {operandGas = operandGas} {M = N}
      {c = χ ▷ᶜ c} next-eq
cast-operand-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {M = M} {c = c}
    operand-eq | not-blame M≢blame | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-⟨⟩ step refl) wholeTrace ,
  eval-prepend-blamed {Σ = Σ}
    {gas = wholeGas}
    (cast-operand-step-question {Σ = Σ} operand-step-eq) whole-eq

cast-operand-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {operandGas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → BlamesFrom Σ operandGas M
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (M ⟨ c ⟩)
cast-operand-blame-expand {Σ = Σ} {operandGas = operandGas}
    {M = M} {c = c}
    (Δ′ , changes , trace , operand-eq)
    with cast-operand-blame-expand-eval {Σ = Σ}
      {operandGas = operandGas} {M = M} {c = c}
      (eval-from-blame {Σ = Σ} {gas = operandGas} operand-eq)
cast-operand-blame-expand {Σ = Σ} operandBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

cast-call-blame-expand-eval : ∀ {Δ Δ′}
    {Σ : TyStore Δ} {operandGas callGas : ℕ}
    {M : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {operandResult : E.EvalResult M}
    {changes : StoreChanges (E.Δ′ operandResult) Δ′}
    {trace :
      E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩ —↠[ changes ] blame}
  → E.evalFrom Σ operandGas M ≡ just (E.returned operandResult)
  → E.evalFrom (E.changes operandResult ▶ˢ Σ) callGas
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩) ≡
      just (E.blamed changes trace)
  → Σ[ wholeGas ∈ ℕ ]
    Σ[ Δ″ ∈ TyCtx ]
    Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
    Σ[ wholeTrace ∈ M ⟨ c ⟩ —↠[ wholeChanges ] blame ]
      E.evalFrom Σ wholeGas (M ⟨ c ⟩) ≡
        just (E.blamed wholeChanges wholeTrace)
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = zero} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    with blame-view M
cast-call-blame-expand-eval operand-eq call-eq
    | is-blame refl with operand-eq
cast-call-blame-expand-eval operand-eq call-eq
    | is-blame refl | ()
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = zero} {callGas = callGas} {M = M}
    operand-eq call-eq | not-blame M≢blame
    with E.value? M in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
           {M = M} M≢blame)) operand-eq
cast-call-blame-expand-eval {callGas = callGas}
    operand-eq call-eq | not-blame M≢blame | just vL | refl =
  callGas , _ , _ , _ , call-eq
cast-call-blame-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    with blame-view M
cast-call-blame-expand-eval operand-eq call-eq
    | is-blame refl with operand-eq
cast-call-blame-expand-eval operand-eq call-eq
    | is-blame refl | ()
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} operand-eq call-eq | not-blame M≢blame
    with E.value? M in value-eq
       | trans (sym (eval-from-nonblame {Σ = Σ}
           {gas = suc operandGas} {M = M} M≢blame)) operand-eq
cast-call-blame-expand-eval {callGas = callGas}
    operand-eq call-eq | not-blame M≢blame | just vL | refl =
  callGas , _ , _ , _ , call-eq
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    with E.step? Σ M in operand-step-eq
cast-call-blame-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | () | nothing
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | normalized-eq
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
cast-call-blame-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step) | nothing
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    with cast-call-blame-expand-eval {Σ = χ ▷ˢ Σ}
      {operandGas = operandGas} {callGas = callGas}
      {M = N} {c = χ ▷ᶜ c}
      {operandResult = next-result} next-eq call-eq
cast-call-blame-expand-eval {Σ = Σ}
    {operandGas = suc operandGas} {callGas = callGas}
    {M = M} {c = c} operand-eq call-eq
    | not-blame M≢blame | nothing | refl
    | just (E.step-result χ N step)
    | just (E.returned next-result)
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  suc wholeGas , Δ″ , χ ∷ wholeChanges ,
  ↠-step (ξ-⟨⟩ step refl) wholeTrace ,
  eval-prepend-blamed {Σ = Σ}
    {gas = wholeGas}
    (cast-operand-step-question {Σ = Σ} operand-step-eq) whole-eq
cast-call-blame-expand-eval operand-eq call-eq
    | not-blame M≢blame | nothing | ()
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)

cast-call-blame-expand : ∀ {Δ} {Σ : TyStore Δ}
    {operandGas callGas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {operandResult : E.EvalResult M}
  → interpretFrom Σ operandGas M ≡ returned operandResult
  → BlamesFrom (E.changes operandResult ▶ˢ Σ) callGas
      (E.term operandResult ⟨ E.changes operandResult ▶ᶜ c ⟩)
  → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (M ⟨ c ⟩)
cast-call-blame-expand {Σ = Σ}
    {operandGas = operandGas} {callGas = callGas}
    {M = M} {c = c} {operandResult = operandResult}
    operand-eq (Δ′ , changes , trace , call-eq)
    with cast-call-blame-expand-eval {Σ = Σ}
      {operandGas = operandGas} {callGas = callGas}
      {M = M} {c = c} {operandResult = operandResult}
      (eval-from-return {Σ = Σ} {gas = operandGas} operand-eq)
      (eval-from-blame {Σ = E.changes operandResult ▶ˢ Σ}
        {gas = callGas} call-eq)
cast-call-blame-expand {Σ = Σ} operand-eq callBlame
    | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
  wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

cast-blame-phases-eval : ∀ {Δ Δ′}
    {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
    {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
    {changes : StoreChanges Δ Δ′}
    {trace : M ⟨ c ⟩ —↠[ changes ] blame}
  → E.evalFrom Σ gas (M ⟨ c ⟩) ≡
      just (E.blamed changes trace)
  → CastBlamed Σ gas M c
  → CastBlamePhases Σ gas M c
cast-blame-phases-eval {Σ = Σ} {gas = gas} {M = M} {c = c}
    whole-eq whole-blame
    with E.value? (M ⟨ c ⟩) in whole-value-eq
cast-blame-phases-eval {Σ = Σ} {gas = gas}
    whole-eq whole-blame | just vM
    with value-return-exact {Σ = Σ} gas vM | castBlame whole-blame
cast-blame-phases-eval whole-eq whole-blame | just vM
    | return-eq | Δ′ , changes , trace , blame-eq
    with trans (sym return-eq) blame-eq
cast-blame-phases-eval whole-eq whole-blame | just vM
    | return-eq | Δ′ , changes , trace , blame-eq | ()
cast-blame-phases-eval {gas = zero} whole-eq whole-blame | nothing
    rewrite whole-value-eq
    with whole-eq
cast-blame-phases-eval whole-eq whole-blame | nothing | ()
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing
    with E.value? M in operand-value-eq
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | just vM
    rewrite operand-value-eq | whole-value-eq
      | value-step-none {Σ = Σ} vM =
  cast-call-phase-blames zero
    (E.result _ [] M ↠-refl vM)
    (value-return-exact {Σ = Σ} zero vM)
    (suc gas) (castBlame whole-blame)
    ≤-refl
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    with E.step? Σ M in operand-step-eq
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step)
    with E.evalFrom (χ ▷ˢ Σ) gas
      (N ⟨ χ ▷ᶜ c ⟩) in next-eq
cast-blame-phases-eval whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step) | nothing
    rewrite operand-step-eq | next-eq with whole-eq
cast-blame-phases-eval whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step) | nothing | ()
cast-blame-phases-eval whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step) | just (E.returned next-result)
    rewrite operand-step-eq | next-eq with whole-eq
cast-blame-phases-eval whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step) | just (E.returned next-result)
    | ()
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace)
    rewrite operand-step-eq | next-eq with whole-eq
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    with cast-blame-phases-eval {Σ = χ ▷ˢ Σ}
      {gas = gas} {M = N} {c = χ ▷ᶜ c} next-eq
      (cast-blamed
        (blame-from-eval {Σ = χ ▷ˢ Σ} {gas = gas} next-eq))
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | cast-operand-phase-blames operandGas operandBlame
        operandGas≤ =
  cast-operand-phase-blames (suc operandGas)
    (prepend-blamed {Σ = Σ} operand-step-eq operandBlame)
    (s≤s operandGas≤)
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame | nothing | nothing
    | just (E.step-result χ N step)
    | just (E.blamed nextChanges nextTrace) | refl
    | cast-call-phase-blames operandGas operandResult
        operandReturn callGas callBlame phases≤ =
  cast-call-phase-blames (suc operandGas)
    (prepend-result step operandResult)
    (prepend-return {Σ = Σ} operand-step-eq operandReturn)
    callGas callBlame (s≤s phases≤)
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame
    | nothing | nothing | nothing
    with blame-view M
cast-blame-phases-eval whole-eq whole-blame
    | nothing | nothing | nothing
    | is-blame refl =
  cast-operand-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
cast-blame-phases-eval {Σ = Σ} {gas = suc gas}
    {M = M} {c = c} whole-eq whole-blame
    | nothing | nothing | nothing
    | not-blame M≢blame
    with E.cast-redex? M c in final-eq
cast-blame-phases-eval whole-eq whole-blame
    | nothing | nothing | nothing
    | not-blame M≢blame | nothing with whole-eq
cast-blame-phases-eval whole-eq whole-blame
    | nothing | nothing | nothing
    | not-blame M≢blame | nothing | ()
cast-blame-phases-eval {Σ = Σ} {M = M}
    {c = c} whole-eq whole-blame
    | nothing | nothing | nothing | not-blame M≢blame
    | just (E.step-result χ N step) = ⊥-elim impossible
  where
  impossible : ⊥
  impossible with trans (sym final-eq)
    (cast-final-none M≢blame operand-value-eq)
  impossible | ()

cast-blame-phases : ∀ {Δ} {Σ : TyStore Δ}
    {gas : ℕ} {M : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ} {c : μ C.⊢ A ∼ B}
  → BlamesFrom Σ gas (M ⟨ c ⟩)
  → CastBlamePhases Σ gas M c
cast-blame-phases {Σ = Σ} {gas = gas}
    {M = M} {c = c}
    (Δ′ , changes , trace , whole-eq) =
  cast-blame-phases-eval {Σ = Σ} {gas = gas}
    {M = M} {c = c}
    (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)
    (cast-blamed (Δ′ , changes , trace , whole-eq))
