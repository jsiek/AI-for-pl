module proof.LR-narrow.FramePhases where

-- File Charter:
--   * Phase decomposition of the evaluation of a wrapped term for an
--     abstract evaluation frame: a congruence context that transports
--     along store changes, propagates blame, and has no redex while its
--     operand is a non-value.
--   * Every returning or blaming run of the wrapped term splits into an
--     operand phase and a continuation phase from the wrapped returned
--     value, and such phases assemble back into whole runs.
--   * Instances: consistency casts, reveals, and conceals.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.BetaExpansion using
  (interpret-from-eval; interpreter-outcome; value-step-none)
open import proof.LR-narrow.Application using
  (_++ˢ_; BlameView; is-blame; not-blame; blame-view; append-trace;
   blame-from-eval; eval-from-blame; eval-from-return;
   eval-from-nonblame; eval-nonblame; prepend-eval-outcome;
   eval-prepend-blamed; eval-prepend-return;
   prepend-blamed; prepend-result; prepend-return; return-from-eval;
   value-return-exact)

------------------------------------------------------------------------
-- Generic evaluator unfolding on non-blame terms
------------------------------------------------------------------------

eval-value-return : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
    {vM : Value M}
  → M ≢ blame
  → E.value? M ≡ just vM
  → E.evalFrom Σ gas M ≡ just (E.returned (E.result _ [] M ↠-refl vM))
eval-value-return {Σ = Σ} {gas = zero} {M = M} M≢blame value-eq
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} M≢blame
    with E.value? M | value-eq
eval-value-return {gas = zero} M≢blame value-eq | just vM | refl = refl
eval-value-return {Σ = Σ} {gas = suc gas} {M = M} M≢blame value-eq
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
    with E.value? M | value-eq
eval-value-return {gas = suc gas} M≢blame value-eq
    | just vM | refl = refl

eval-zero-none : ∀ {Δ} {Σ : TyStore Δ} {M : Term Δ}
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.evalFrom Σ zero M ≡ nothing
eval-zero-none {Σ = Σ} {M = M} M≢blame value-eq
    rewrite eval-from-nonblame {Σ = Σ} {gas = zero} M≢blame
    with E.value? M | value-eq
eval-zero-none M≢blame value-eq | nothing | refl = refl

eval-stuck-none : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.step? Σ M ≡ nothing
  → E.evalFrom Σ (suc gas) M ≡ nothing
eval-stuck-none {Σ = Σ} {gas = gas} {M = M} M≢blame value-eq step-eq
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
    with E.value? M | value-eq
eval-stuck-none {Σ = Σ} {M = M} M≢blame value-eq step-eq
    | nothing | refl
    with E.step? Σ M | step-eq
eval-stuck-none M≢blame value-eq step-eq
    | nothing | refl | nothing | refl = refl

eval-step-unfold : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ} {M : Term Δ}
    {χ : StoreChange Δ Δ′} {N : Term Δ′} {step : M —→[ χ ] N}
  → M ≢ blame
  → E.value? M ≡ nothing
  → E.step? Σ M ≡ just (E.step-result χ N step)
  → E.evalFrom Σ (suc gas) M ≡
      Data.Maybe.map (prepend-eval-outcome step)
        (E.evalFrom (χ ▷ˢ Σ) gas N)
eval-step-unfold {Σ = Σ} {gas = gas} {M = M} {χ = χ} {N = N}
    M≢blame value-eq step-eq
    rewrite eval-from-nonblame {Σ = Σ} {gas = suc gas} M≢blame
    with E.value? M | value-eq
eval-step-unfold {Σ = Σ} {gas = gas} {M = M} {χ = χ} {N = N}
    M≢blame value-eq step-eq
    | nothing | refl
    with E.step? Σ M | step-eq
eval-step-unfold {Σ = Σ} {gas = gas} {χ = χ} {N = N}
    M≢blame value-eq step-eq
    | nothing | refl | just _ | refl
    with E.evalFrom (χ ▷ˢ Σ) gas N
eval-step-unfold M≢blame value-eq step-eq
    | nothing | refl | just _ | refl | nothing = refl
eval-step-unfold M≢blame value-eq step-eq
    | nothing | refl | just _ | refl | just outcome = refl

------------------------------------------------------------------------
-- Evaluation frames
------------------------------------------------------------------------

record Frame : Set₁ where
  field
    -- Frame data at each context, and the wrapped term.
    Frm : TyCtx → Set
    plug : ∀ {Δ} → Frm Δ → Term Δ → Term Δ

    -- Transport along one store change, extended to sequences below.
    transport : ∀ {Δ Δ′} → StoreChange Δ Δ′ → Frm Δ → Frm Δ′

    -- Congruence: a step of the operand is a step of the wrapped term
    -- with the transported frame, and the evaluator takes exactly it.
    plug-step : ∀ {Δ Δ′} (f : Frm Δ) {χ : StoreChange Δ Δ′}
        {M : Term Δ} {N : Term Δ′}
      → M —→[ χ ] N
      → plug f M —→[ χ ] plug (transport χ f) N
    plug-step? : ∀ {Δ Δ′} (f : Frm Δ) {Σ : TyStore Δ}
        {χ : StoreChange Δ Δ′} {M : Term Δ} {N : Term Δ′}
        {step : M —→[ χ ] N}
      → E.step? Σ M ≡ just (E.step-result χ N step)
      → E.step? Σ (plug f M) ≡
          just (E.step-result χ (plug (transport χ f) N)
            (plug-step f step))

    -- A stuck non-value operand leaves the wrapped term stuck.
    plug-stuck : ∀ {Δ} (f : Frm Δ) {Σ : TyStore Δ} {M : Term Δ}
      → E.step? Σ M ≡ nothing
      → E.value? M ≡ nothing
      → M ≢ blame
      → E.step? Σ (plug f M) ≡ nothing

    -- The wrapped term is a value only if the operand is.
    plug-nonvalue : ∀ {Δ} (f : Frm Δ) {M : Term Δ}
      → E.value? M ≡ nothing
      → E.value? (plug f M) ≡ nothing

    -- The wrapped term is never syntactically blame, and wrapped blame
    -- steps to blame.
    plug-not-blame : ∀ {Δ} (f : Frm Δ) (M : Term Δ) → plug f M ≢ blame
    plug-blame : ∀ {Δ} (f : Frm Δ) → plug f blame —→ blame
    plug-blame-step? : ∀ {Δ} (f : Frm Δ) {Σ : TyStore Δ}
      → E.step? Σ (plug f blame) ≡
          just (E.step-result keep blame (pure-step (plug-blame f)))

  transports : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → Frm Δ → Frm Δ′
  transports [] f = f
  transports (χ ∷ χs) f = transports χs (transport χ f)

  -- The operand trace carries the frame along.

  plug-trace : ∀ {Δ₀ Δ₁} (f : Frm Δ₀) {M : Term Δ₀} {V : Term Δ₁}
      {χs : StoreChanges Δ₀ Δ₁}
    → M —↠[ χs ] V
    → plug f M —↠[ χs ] plug (transports χs f) V
  plug-trace f ↠-refl = ↠-refl
  plug-trace f (↠-step step rest) =
    ↠-step (plug-step f step) (plug-trace (transport _ f) rest)

  sequence-result : ∀ {Δ₀} (f : Frm Δ₀) {M : Term Δ₀}
    → (operandResult : E.EvalResult M)
    → E.EvalResult
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult))
    → E.EvalResult (plug f M)
  sequence-result f (E.result Δ₁ χs V M↠V vV)
      (E.result Δ₂ ψs Z call↠Z vZ) =
    E.result Δ₂ (χs ++ˢ ψs) Z
      (append-trace (plug-trace f M↠V) call↠Z) vZ

  ----------------------------------------------------------------------
  -- Evaluator facts for wrapped terms
  ----------------------------------------------------------------------

  eval-plug-blame : ∀ {Δ} (f : Frm Δ) {Σ : TyStore Δ} {gas : ℕ}
    → E.evalFrom Σ (suc gas) (plug f blame) ≡
        just (E.blamed (keep ∷ [])
          (↠-step (pure-step (plug-blame f)) ↠-refl))
  eval-plug-blame f {Σ = Σ} {gas = zero} =
    eval-prepend-blamed {Σ = Σ} {M = plug f blame} {χ = keep}
      {N = blame} {gas = zero} {step = pure-step (plug-blame f)}
      {changes = []} {trace = ↠-refl}
      (plug-blame-step? f {Σ = Σ}) refl
  eval-plug-blame f {Σ = Σ} {gas = suc gas} =
    eval-prepend-blamed {Σ = Σ} {M = plug f blame} {χ = keep}
      {N = blame} {gas = suc gas} {step = pure-step (plug-blame f)}
      {changes = []} {trace = ↠-refl}
      (plug-blame-step? f {Σ = Σ}) refl

  plug-blame-not-returned : ∀ {Δ} (f : Frm Δ) {Σ : TyStore Δ}
      {gas : ℕ} {result : E.EvalResult (plug f blame)}
    → E.evalFrom Σ gas (plug f blame) ≡ just (E.returned result)
    → ⊥
  plug-blame-not-returned f {Σ = Σ} {gas = zero} result-eq
      with trans (sym (eval-zero-none {Σ = Σ} (plug-not-blame f blame)
        (plug-nonvalue f refl))) result-eq
  plug-blame-not-returned f {gas = zero} result-eq | ()
  plug-blame-not-returned f {Σ = Σ} {gas = suc gas} result-eq
      with trans (sym (eval-plug-blame f {Σ = Σ} {gas = gas})) result-eq
  plug-blame-not-returned f {gas = suc gas} result-eq | ()

  plug-stuck-not-returned : ∀ {Δ} (f : Frm Δ) {Σ : TyStore Δ}
      {gas : ℕ} {M : Term Δ} {result : E.EvalResult (plug f M)}
    → E.step? Σ M ≡ nothing
    → E.value? M ≡ nothing
    → E.evalFrom Σ (suc gas) (plug f M) ≡ just (E.returned result)
    → ⊥
  plug-stuck-not-returned f {Σ = Σ} {gas = gas} {M = M}
      step-eq value-eq result-eq
      with blame-view M
  plug-stuck-not-returned f {Σ = Σ} {gas = gas}
      step-eq value-eq result-eq | is-blame refl =
    plug-blame-not-returned f {Σ = Σ} {gas = suc gas} result-eq
  plug-stuck-not-returned f {Σ = Σ} {gas = gas} {M = M}
      step-eq value-eq result-eq | not-blame M≢blame
      with trans (sym (eval-stuck-none {Σ = Σ} {gas = gas} {M = plug f M}
        (plug-not-blame f M) (plug-nonvalue f value-eq)
        (plug-stuck f {Σ = Σ} step-eq value-eq M≢blame))) result-eq
  plug-stuck-not-returned f step-eq value-eq result-eq
      | not-blame M≢blame | ()

  ----------------------------------------------------------------------
  -- Return phases
  ----------------------------------------------------------------------

  record ReturnPhases {Δ : TyCtx} (Σ : TyStore Δ) (gas : ℕ)
      (f : Frm Δ) (M : Term Δ)
      (wholeResult : E.EvalResult (plug f M)) : Set where
    constructor return-phases
    pattern
    field
      operandGas : ℕ
      operandResult : E.EvalResult M
      operandReturn :
        interpretFrom Σ operandGas M ≡ returned operandResult

      callGas : ℕ
      callResult : E.EvalResult
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult))
      callReturn :
        interpretFrom (E.changes operandResult ▶ˢ Σ) callGas
          (plug (transports (E.changes operandResult) f)
            (E.term operandResult)) ≡ returned callResult

      result-splits : wholeResult ≡ sequence-result f operandResult callResult
      gas-splits : operandGas + callGas ≡ gas

  open ReturnPhases public

  return-phases-eval : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
      (f : Frm Δ) {M : Term Δ} {result : E.EvalResult (plug f M)}
    → E.evalFrom Σ gas (plug f M) ≡ just (E.returned result)
    → ReturnPhases Σ gas f M result
  return-phases-eval {Σ = Σ} {gas = gas} f {M = M} {result = result}
      result-eq
      with E.value? M in operand-value-eq
  return-phases-eval {Σ = Σ} {gas = gas} f {M = M} result-eq
      | just vM
      with E.value? (plug f M) in whole-value-eq
  return-phases-eval {Σ = Σ} {gas = gas} f {M = M} result-eq
      | just vM | just wholeValue
      with trans (sym (eval-value-return {Σ = Σ} {gas = gas}
             (plug-not-blame f M) whole-value-eq)) result-eq
  return-phases-eval {Σ = Σ} {gas = gas} f {M = M} result-eq
      | just vM | just wholeValue | refl =
    return-phases zero (E.result _ [] M ↠-refl vM)
      (value-return-exact {Σ = Σ} zero vM)
      gas _ (return-from-eval {Σ = Σ} {gas = gas} result-eq)
      refl refl
  return-phases-eval {Σ = Σ} {gas = gas} f {M = M} result-eq
      | just vM | nothing =
    return-phases zero (E.result _ [] M ↠-refl vM)
      (value-return-exact {Σ = Σ} zero vM)
      gas _ (return-from-eval {Σ = Σ} {gas = gas} result-eq)
      refl refl
  return-phases-eval {Σ = Σ} {gas = zero} f {M = M} result-eq
      | nothing
      with trans (sym (eval-zero-none {Σ = Σ} (plug-not-blame f M)
             (plug-nonvalue f operand-value-eq))) result-eq
  return-phases-eval {gas = zero} f result-eq | nothing | ()
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing
      with E.step? Σ M in operand-step-eq
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing | nothing =
    ⊥-elim (plug-stuck-not-returned f {Σ = Σ} {gas = gas}
      operand-step-eq operand-value-eq result-eq)
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing | just (E.step-result χ N step)
      with trans (sym (eval-step-unfold {Σ = Σ} {gas = gas} {M = plug f M}
             {χ = χ} {N = plug (transport χ f) N} {step = plug-step f step}
             (plug-not-blame f M) (plug-nonvalue f operand-value-eq)
             (plug-step? f {Σ = Σ} operand-step-eq))) result-eq
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing | just (E.step-result χ N step) | mapped-eq
      with E.evalFrom (χ ▷ˢ Σ) gas (plug (transport χ f) N) in next-eq
  return-phases-eval f result-eq
      | nothing | just (E.step-result χ N step) | () | nothing
  return-phases-eval f result-eq
      | nothing | just (E.step-result χ N step) | ()
      | just (E.blamed changes trace)
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing | just (E.step-result χ N step) | refl
      | just (E.returned next-result)
      with return-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas} (transport χ f)
             {M = N} {result = next-result} next-eq
  return-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} result-eq
      | nothing | just (E.step-result χ N step) | refl
      | just (E.returned next-result)
      | return-phases operandGas operandResult operandReturn
          callGas callResult callReturn result-split gas-eq =
    return-phases (suc operandGas)
      (prepend-result step operandResult)
      (prepend-return {Σ = Σ} {M = M} {gas = operandGas}
        operand-step-eq operandReturn)
      callGas callResult callReturn
      (cong (prepend-result (plug-step f step)) result-split)
      (cong suc gas-eq)

  return-phases-of : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
      (f : Frm Δ) {M : Term Δ} {result : E.EvalResult (plug f M)}
    → interpretFrom Σ gas (plug f M) ≡ returned result
    → ReturnPhases Σ gas f M result
  return-phases-of {Σ = Σ} {gas = gas} f result-eq =
    return-phases-eval {Σ = Σ} {gas = gas} f
      (eval-from-return {Σ = Σ} {gas = gas} result-eq)

  ----------------------------------------------------------------------
  -- Assembling phases into whole runs
  ----------------------------------------------------------------------

  return-expand-eval : ∀ {Δ} {Σ : TyStore Δ}
      {operandGas callGas : ℕ} (f : Frm Δ) {M : Term Δ}
      {operandResult : E.EvalResult M}
      {callResult : E.EvalResult
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult))}
    → E.evalFrom Σ operandGas M ≡ just (E.returned operandResult)
    → E.evalFrom (E.changes operandResult ▶ˢ Σ) callGas
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult)) ≡ just (E.returned callResult)
    → Σ[ wholeGas ∈ ℕ ] E.evalFrom Σ wholeGas (plug f M) ≡
        just (E.returned (sequence-result f operandResult callResult))
  return-expand-eval {Σ = Σ} {operandGas = zero} {callGas = callGas}
      f {M = M} operand-eq call-eq
      with blame-view M
  return-expand-eval f operand-eq call-eq | is-blame refl
      with operand-eq
  return-expand-eval f operand-eq call-eq | is-blame refl | ()
  return-expand-eval {Σ = Σ} {operandGas = zero} {callGas = callGas}
      f {M = M} operand-eq call-eq
      | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
             M≢blame)) operand-eq
  return-expand-eval {callGas = callGas} f operand-eq call-eq
      | not-blame M≢blame | just vM | refl = callGas , call-eq
  return-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      with blame-view M
  return-expand-eval f operand-eq call-eq | is-blame refl
      with operand-eq
  return-expand-eval f operand-eq call-eq | is-blame refl | ()
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ}
             {gas = suc operandGas} M≢blame)) operand-eq
  return-expand-eval {callGas = callGas} f operand-eq call-eq
      | not-blame M≢blame | just vM | refl = callGas , call-eq
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | normalized-eq
      with E.step? Σ M in operand-step-eq
  return-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | () | nothing
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | normalized-eq
      | just (E.step-result χ N step)
      with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
  return-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
      | just (E.step-result χ N step) | nothing
  return-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
      | just (E.step-result χ N step) | just (E.blamed changes trace)
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | refl
      | just (E.step-result χ N step) | just (E.returned next-result)
      with return-expand-eval {Σ = χ ▷ˢ Σ} {operandGas = operandGas}
             {callGas = callGas} (transport χ f) {M = N}
             {operandResult = next-result} next-eq call-eq
  return-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | refl
      | just (E.step-result χ N step) | just (E.returned next-result)
      | wholeGas , whole-eq =
    suc wholeGas ,
    eval-prepend-return {Σ = Σ} (plug-step? f {Σ = Σ} operand-step-eq)
      whole-eq

  return-expand : ∀ {Δ} {Σ : TyStore Δ}
      {operandGas callGas : ℕ} (f : Frm Δ) {M : Term Δ}
      {operandResult : E.EvalResult M}
      {callResult : E.EvalResult
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult))}
    → interpretFrom Σ operandGas M ≡ returned operandResult
    → interpretFrom (E.changes operandResult ▶ˢ Σ) callGas
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult)) ≡ returned callResult
    → Σ[ wholeGas ∈ ℕ ] interpretFrom Σ wholeGas (plug f M) ≡
        returned (sequence-result f operandResult callResult)
  return-expand {Σ = Σ} {operandGas = operandGas} {callGas = callGas}
      f {M = M} {operandResult = operandResult} operand-eq call-eq
      with return-expand-eval {Σ = Σ} {operandGas = operandGas}
             {callGas = callGas} f {M = M}
             (eval-from-return {Σ = Σ} {gas = operandGas} operand-eq)
             (eval-from-return
               {Σ = E.changes operandResult ▶ˢ Σ} {gas = callGas}
               call-eq)
  return-expand {Σ = Σ} f operand-eq call-eq | wholeGas , whole-eq =
    wholeGas , return-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

  ----------------------------------------------------------------------
  -- Blame phases
  ----------------------------------------------------------------------

  data BlamePhases {Δ : TyCtx} (Σ : TyStore Δ) (gas : ℕ)
      (f : Frm Δ) (M : Term Δ) : Set where
    operand-phase-blames :
        (operandGas : ℕ)
      → BlamesFrom Σ operandGas M
      → operandGas ≤ gas
      → BlamePhases Σ gas f M

    call-phase-blames :
        (operandGas : ℕ)
      → (operandResult : E.EvalResult M)
      → interpretFrom Σ operandGas M ≡ returned operandResult
      → (callGas : ℕ)
      → BlamesFrom (E.changes operandResult ▶ˢ Σ) callGas
          (plug (transports (E.changes operandResult) f)
            (E.term operandResult))
      → operandGas + callGas ≤ gas
      → BlamePhases Σ gas f M

  operand-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
      {operandGas : ℕ} (f : Frm Δ) {M : Term Δ}
      {changes : StoreChanges Δ Δ′} {trace : M —↠[ changes ] blame}
    → E.evalFrom Σ operandGas M ≡ just (E.blamed changes trace)
    → Σ[ wholeGas ∈ ℕ ]
      Σ[ Δ″ ∈ TyCtx ]
      Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
      Σ[ wholeTrace ∈ plug f M —↠[ wholeChanges ] blame ]
        E.evalFrom Σ wholeGas (plug f M) ≡
          just (E.blamed wholeChanges wholeTrace)
  operand-blame-expand-eval {Σ = Σ} {operandGas = zero} f {M = M}
      operand-eq with blame-view M
  operand-blame-expand-eval {Σ = Σ} f operand-eq | is-blame refl =
    1 , _ , keep ∷ [] , ↠-step (pure-step (plug-blame f)) ↠-refl ,
      eval-plug-blame f {Σ = Σ} {gas = zero}
  operand-blame-expand-eval {Σ = Σ} {operandGas = zero} f {M = M}
      operand-eq | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
             M≢blame)) operand-eq
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | just vM | ()
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | nothing | ()
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq with blame-view M
  operand-blame-expand-eval {Σ = Σ} f operand-eq | is-blame refl =
    1 , _ , keep ∷ [] , ↠-step (pure-step (plug-blame f)) ↠-refl ,
      eval-plug-blame f {Σ = Σ} {gas = zero}
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ}
             {gas = suc operandGas} M≢blame)) operand-eq
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | just vM | ()
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq | not-blame M≢blame
      | nothing | normalized-eq
      with E.step? Σ M in operand-step-eq
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | nothing | () | nothing
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq | not-blame M≢blame
      | nothing | normalized-eq | just (E.step-result χ N step)
      with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | nothing | () | just (E.step-result χ N step) | nothing
  operand-blame-expand-eval f operand-eq | not-blame M≢blame
      | nothing | () | just (E.step-result χ N step)
      | just (E.returned next-result)
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq | not-blame M≢blame
      | nothing | refl | just (E.step-result χ N step)
      | just (E.blamed nextChanges nextTrace)
      with operand-blame-expand-eval {Σ = χ ▷ˢ Σ}
             {operandGas = operandGas} (transport χ f) {M = N} next-eq
  operand-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      f {M = M} operand-eq | not-blame M≢blame
      | nothing | refl | just (E.step-result χ N step)
      | just (E.blamed nextChanges nextTrace)
      | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
    suc wholeGas , Δ″ , χ ∷ wholeChanges ,
    ↠-step (plug-step f step) wholeTrace ,
    eval-prepend-blamed {Σ = Σ} (plug-step? f {Σ = Σ} operand-step-eq)
      whole-eq

  operand-blame-expand : ∀ {Δ} {Σ : TyStore Δ} {operandGas : ℕ}
      (f : Frm Δ) {M : Term Δ}
    → BlamesFrom Σ operandGas M
    → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (plug f M)
  operand-blame-expand {Σ = Σ} {operandGas = operandGas} f {M = M}
      (Δ′ , changes , trace , operand-eq)
      with operand-blame-expand-eval {Σ = Σ} {operandGas = operandGas}
             f {M = M} (eval-from-blame {Σ = Σ} {gas = operandGas}
               operand-eq)
  operand-blame-expand {Σ = Σ} f operandBlame
      | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
    wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

  call-blame-expand-eval : ∀ {Δ Δ′} {Σ : TyStore Δ}
      {operandGas callGas : ℕ} (f : Frm Δ) {M : Term Δ}
      {operandResult : E.EvalResult M}
      {changes : StoreChanges (E.Δ′ operandResult) Δ′}
      {trace : plug (transports (E.changes operandResult) f)
        (E.term operandResult) —↠[ changes ] blame}
    → E.evalFrom Σ operandGas M ≡ just (E.returned operandResult)
    → E.evalFrom (E.changes operandResult ▶ˢ Σ) callGas
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult)) ≡ just (E.blamed changes trace)
    → Σ[ wholeGas ∈ ℕ ]
      Σ[ Δ″ ∈ TyCtx ]
      Σ[ wholeChanges ∈ StoreChanges Δ Δ″ ]
      Σ[ wholeTrace ∈ plug f M —↠[ wholeChanges ] blame ]
        E.evalFrom Σ wholeGas (plug f M) ≡
          just (E.blamed wholeChanges wholeTrace)
  call-blame-expand-eval {Σ = Σ} {operandGas = zero} {callGas = callGas}
      f {M = M} operand-eq call-eq with blame-view M
  call-blame-expand-eval f operand-eq call-eq | is-blame refl
      with operand-eq
  call-blame-expand-eval f operand-eq call-eq | is-blame refl | ()
  call-blame-expand-eval {Σ = Σ} {operandGas = zero} {callGas = callGas}
      f {M = M} operand-eq call-eq | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ} {gas = zero}
             M≢blame)) operand-eq
  call-blame-expand-eval {callGas = callGas} f operand-eq call-eq
      | not-blame M≢blame | just vM | refl =
    callGas , _ , _ , _ , call-eq
  call-blame-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      with blame-view M
  call-blame-expand-eval f operand-eq call-eq | is-blame refl
      with operand-eq
  call-blame-expand-eval f operand-eq call-eq | is-blame refl | ()
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame
      with E.value? M in value-eq
         | trans (sym (eval-from-nonblame {Σ = Σ}
             {gas = suc operandGas} M≢blame)) operand-eq
  call-blame-expand-eval {callGas = callGas} f operand-eq call-eq
      | not-blame M≢blame | just vM | refl =
    callGas , _ , _ , _ , call-eq
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | normalized-eq
      with E.step? Σ M in operand-step-eq
  call-blame-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | () | nothing
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | normalized-eq
      | just (E.step-result χ N step)
      with E.evalFrom (χ ▷ˢ Σ) operandGas N in next-eq
  call-blame-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
      | just (E.step-result χ N step) | nothing
  call-blame-expand-eval f operand-eq call-eq
      | not-blame M≢blame | nothing | ()
      | just (E.step-result χ N step) | just (E.blamed changes trace)
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | refl
      | just (E.step-result χ N step) | just (E.returned next-result)
      with call-blame-expand-eval {Σ = χ ▷ˢ Σ} {operandGas = operandGas}
             {callGas = callGas} (transport χ f) {M = N}
             {operandResult = next-result} next-eq call-eq
  call-blame-expand-eval {Σ = Σ} {operandGas = suc operandGas}
      {callGas = callGas} f {M = M} operand-eq call-eq
      | not-blame M≢blame | nothing | refl
      | just (E.step-result χ N step) | just (E.returned next-result)
      | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
    suc wholeGas , Δ″ , χ ∷ wholeChanges ,
    ↠-step (plug-step f step) wholeTrace ,
    eval-prepend-blamed {Σ = Σ} (plug-step? f {Σ = Σ} operand-step-eq)
      whole-eq

  call-blame-expand : ∀ {Δ} {Σ : TyStore Δ} {operandGas callGas : ℕ}
      (f : Frm Δ) {M : Term Δ} {operandResult : E.EvalResult M}
    → interpretFrom Σ operandGas M ≡ returned operandResult
    → BlamesFrom (E.changes operandResult ▶ˢ Σ) callGas
        (plug (transports (E.changes operandResult) f)
          (E.term operandResult))
    → Σ[ wholeGas ∈ ℕ ] BlamesFrom Σ wholeGas (plug f M)
  call-blame-expand {Σ = Σ} {operandGas = operandGas}
      {callGas = callGas} f {M = M} {operandResult = operandResult}
      operand-eq (Δ′ , changes , trace , call-eq)
      with call-blame-expand-eval {Σ = Σ} {operandGas = operandGas}
             {callGas = callGas} f {M = M} {operandResult = operandResult}
             (eval-from-return {Σ = Σ} {gas = operandGas} operand-eq)
             (eval-from-blame {Σ = E.changes operandResult ▶ˢ Σ}
               {gas = callGas} call-eq)
  call-blame-expand {Σ = Σ} f operand-eq callBlame
      | wholeGas , Δ″ , wholeChanges , wholeTrace , whole-eq =
    wholeGas , blame-from-eval {Σ = Σ} {gas = wholeGas} whole-eq

  blame-phases-eval : ∀ {Δ Δ′} {Σ : TyStore Δ} {gas : ℕ}
      (f : Frm Δ) {M : Term Δ}
      {changes : StoreChanges Δ Δ′}
      {trace : plug f M —↠[ changes ] blame}
    → E.evalFrom Σ gas (plug f M) ≡ just (E.blamed changes trace)
    → BlamePhases Σ gas f M
  blame-phases-eval {Σ = Σ} {gas = gas} f {M = M} whole-eq
      with E.value? M in operand-value-eq
  blame-phases-eval {Σ = Σ} {gas = gas} f {M = M} whole-eq
      | just vM =
    call-phase-blames zero (E.result _ [] M ↠-refl vM)
      (value-return-exact {Σ = Σ} zero vM)
      gas (blame-from-eval {Σ = Σ} {gas = gas} whole-eq) ≤-refl
  blame-phases-eval {Σ = Σ} {gas = zero} f {M = M} whole-eq
      | nothing
      with trans (sym (eval-zero-none {Σ = Σ} (plug-not-blame f M)
             (plug-nonvalue f operand-value-eq))) whole-eq
  blame-phases-eval {gas = zero} f whole-eq | nothing | ()
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing
      with E.step? Σ M in operand-step-eq
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | nothing
      with blame-view M
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | nothing | is-blame refl =
    operand-phase-blames zero (_ , [] , ↠-refl , refl) z≤n
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | nothing | not-blame M≢blame
      with trans (sym (eval-stuck-none {Σ = Σ} {gas = gas} {M = plug f M}
             (plug-not-blame f M) (plug-nonvalue f operand-value-eq)
             (plug-stuck f {Σ = Σ} operand-step-eq operand-value-eq
               M≢blame))) whole-eq
  blame-phases-eval f whole-eq | nothing | nothing | not-blame M≢blame | ()
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | just (E.step-result χ N step)
      with trans (sym (eval-step-unfold {Σ = Σ} {gas = gas} {M = plug f M}
             {χ = χ} {N = plug (transport χ f) N} {step = plug-step f step}
             (plug-not-blame f M) (plug-nonvalue f operand-value-eq)
             (plug-step? f {Σ = Σ} operand-step-eq))) whole-eq
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | just (E.step-result χ N step) | mapped-eq
      with E.evalFrom (χ ▷ˢ Σ) gas (plug (transport χ f) N) in next-eq
  blame-phases-eval f whole-eq
      | nothing | just (E.step-result χ N step) | () | nothing
  blame-phases-eval f whole-eq
      | nothing | just (E.step-result χ N step) | ()
      | just (E.returned next-result)
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | just (E.step-result χ N step) | refl
      | just (E.blamed nextChanges nextTrace)
      with blame-phases-eval {Σ = χ ▷ˢ Σ} {gas = gas} (transport χ f)
             {M = N} next-eq
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | just (E.step-result χ N step) | refl
      | just (E.blamed nextChanges nextTrace)
      | operand-phase-blames operandGas operandBlame operandGas≤ =
    operand-phase-blames (suc operandGas)
      (prepend-blamed {Σ = Σ} operand-step-eq operandBlame)
      (s≤s operandGas≤)
  blame-phases-eval {Σ = Σ} {gas = suc gas} f {M = M} whole-eq
      | nothing | just (E.step-result χ N step) | refl
      | just (E.blamed nextChanges nextTrace)
      | call-phase-blames operandGas operandResult operandReturn
          callGas callBlame phases≤ =
    call-phase-blames (suc operandGas)
      (prepend-result step operandResult)
      (prepend-return {Σ = Σ} operand-step-eq operandReturn)
      callGas callBlame (s≤s phases≤)

  blame-phases-of : ∀ {Δ} {Σ : TyStore Δ} {gas : ℕ}
      (f : Frm Δ) {M : Term Δ}
    → BlamesFrom Σ gas (plug f M)
    → BlamePhases Σ gas f M
  blame-phases-of {Σ = Σ} {gas = gas} f
      (Δ′ , changes , trace , whole-eq) =
    blame-phases-eval {Σ = Σ} {gas = gas} f
      (eval-from-blame {Σ = Σ} {gas = gas} whole-eq)
