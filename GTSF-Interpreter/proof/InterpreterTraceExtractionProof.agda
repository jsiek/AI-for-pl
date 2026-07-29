module proof.InterpreterTraceExtractionProof where

-- File Charter:
--   * Converts an eventual direct-interpreter return or blame into the exact
--     finite timeout-prefix traces consumed by double-interpreter catch-up.
--   * Uses bounded search and terminal fuel stabilization only.
--   * Contains no reduction semantics, DGG premise, or negated convergence.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import Coercions using (Coercion)
import DoubleInterpreter as Double
import DoubleInterpreterCatchUp as DoubleProof
open import Interpreter
open import InterpreterFuel
open import InterpreterOutcome
open import NuTerms using (Term)
open import Types

module TraceExtraction
  (BodyNarrowing : Term → Term → Set₁)
  (TypeNarrowing : Ty → Ty → Set₁)
  (GroundNarrowing :
    ∀ {G H} → Ground G → Ground H → Set₁)
  (CoercionNarrowing : Coercion → Coercion → Set₁)
  (NameNarrowing : Name → Name → Set₁)
  (SealNameNarrowing : SealName → SealName → Set₁)
  (LeftValueWrapperNarrowing : Value → Value → Set₁)
  (RightValueWrapperNarrowing : Value → Value → Set₁)
  where

  module Sync = Double.Synchronized
    BodyNarrowing
    TypeNarrowing
    GroundNarrowing
    CoercionNarrowing
    NameNarrowing
    SealNameNarrowing
    LeftValueWrapperNarrowing
    RightValueWrapperNarrowing

  module Catch = DoubleProof.CatchUp
    BodyNarrowing
    TypeNarrowing
    GroundNarrowing
    CoercionNarrowing
    NameNarrowing
    SealNameNarrowing
    LeftValueWrapperNarrowing
    RightValueWrapperNarrowing

  open Sync
  open Catch

  ----------------------------------------------------------------------
  -- Bounded first-terminal search: right return
  ----------------------------------------------------------------------

  right-first-return-traceᵖ :
    ∀ {right-term W V current steps W₀′ W′ V′} →
    run right-term current ≡ timed W₀′ →
    run right-term (current + steps) ≡ returned W′ V′ →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      RightCatchUpTrace right-term W V
        current steps terminal-index W′ V′
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {zero}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′ =
    ⊥-elim
      (timed≢returned
        (trans (sym timeout-eq)
          (subst
            (λ index → run right-term index ≡ returned W′ V′)
            (+-identityʳ current)
            return-eq)))
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′
      rewrite +-suc current steps
      with run right-term (suc current) in next-eq
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′
      | timed W₁ =
    let terminal-index , trace =
          right-first-return-traceᵖ
            next-eq return-eq V⊑V′
    in
    terminal-index , right-timeout next-eq trace
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′
      | blamed W₁ =
    ⊥-elim
      (blamed≢returned
        (trans
          (sym
            (run-terminal-stable
              {N = right-term} {n = suc current}
              terminal-blame next-eq steps))
          return-eq))
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′
      | failed W₁ e =
    ⊥-elim
      (failed≢returned
        (trans
          (sym
            (run-terminal-stable
              {N = right-term} {n = suc current}
              terminal-error next-eq steps))
          return-eq))
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {W′} {V′} timeout-eq return-eq V⊑V′
      | returned W₁ V₁
      with trans
        (sym
          (run-terminal-stable
            {N = right-term} {n = suc current}
            terminal-return next-eq steps))
        return-eq
  right-first-return-traceᵖ
      {right-term} {W} {V} {current} {suc steps}
      {W₀′} {.W₁} {.V₁} timeout-eq return-eq V⊑V′
      | returned W₁ V₁ | refl =
    suc current , right-return next-eq V⊑V′

  right-eventual-return⇒traceᵖ :
    ∀ {right-term W V current W₀′ m W′ V′} →
    run right-term current ≡ timed W₀′ →
    run right-term m ≡ returned W′ V′ →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      RightCatchUpTrace right-term W V
        current (suc m) terminal-index W′ V′
  right-eventual-return⇒traceᵖ
      {right-term} {W} {V} {current} {W₀′}
      {m} {W′} {V′} timeout-eq return-eq V⊑V′ =
    right-first-return-traceᵖ
      timeout-eq
      (run-terminal-after terminal-return return-eq current)
      V⊑V′

  ----------------------------------------------------------------------
  -- Bounded first-terminal search: left return
  ----------------------------------------------------------------------

  left-first-return-traceᵖ :
    ∀ {left-term W′ V′ current steps W₀ W V} →
    run left-term current ≡ timed W₀ →
    run left-term (current + steps) ≡ returned W V →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      LeftCatchUpTrace left-term W′ V′
        current steps terminal-index W V
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {zero}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′ =
    ⊥-elim
      (timed≢returned
        (trans (sym timeout-eq)
          (subst
            (λ index → run left-term index ≡ returned W V)
            (+-identityʳ current)
            return-eq)))
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′
      rewrite +-suc current steps
      with run left-term (suc current) in next-eq
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′
      | timed W₁ =
    let terminal-index , trace =
          left-first-return-traceᵖ
            next-eq return-eq V⊑V′
    in
    terminal-index , left-timeout next-eq trace
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′
      | blamed W₁ =
    ⊥-elim
      (blamed≢returned
        (trans
          (sym
            (run-terminal-stable
              {N = left-term} {n = suc current}
              terminal-blame next-eq steps))
          return-eq))
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′
      | failed W₁ e =
    ⊥-elim
      (failed≢returned
        (trans
          (sym
            (run-terminal-stable
              {N = left-term} {n = suc current}
              terminal-error next-eq steps))
          return-eq))
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {W} {V} timeout-eq return-eq V⊑V′
      | returned W₁ V₁
      with trans
        (sym
          (run-terminal-stable
            {N = left-term} {n = suc current}
            terminal-return next-eq steps))
        return-eq
  left-first-return-traceᵖ
      {left-term} {W′} {V′} {current} {suc steps}
      {W₀} {.W₁} {.V₁} timeout-eq return-eq V⊑V′
      | returned W₁ V₁ | refl =
    suc current , left-return next-eq V⊑V′

  left-eventual-return⇒traceᵖ :
    ∀ {left-term W′ V′ current W₀ m W V} →
    run left-term current ≡ timed W₀ →
    run left-term m ≡ returned W V →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      LeftCatchUpTrace left-term W′ V′
        current (suc m) terminal-index W V
  left-eventual-return⇒traceᵖ
      {left-term} {W′} {V′} {current} {W₀}
      {m} {W} {V} timeout-eq return-eq V⊑V′ =
    left-first-return-traceᵖ
      timeout-eq
      (run-terminal-after terminal-return return-eq current)
      V⊑V′

  ----------------------------------------------------------------------
  -- Bounded first-terminal search: permitted left blame
  ----------------------------------------------------------------------

  left-first-blame-traceᵖ :
    ∀ {left-term current steps W₀ W} →
    run left-term current ≡ timed W₀ →
    run left-term (current + steps) ≡ blamed W →
    Σ[ terminal-index ∈ StepIndex ]
      LeftBlameCatchUpTrace left-term
        current steps terminal-index W
  left-first-blame-traceᵖ
      {left-term} {current} {zero} {W₀} {W}
      timeout-eq blame-eq =
    ⊥-elim
      (timed≢blamed
        (trans (sym timeout-eq)
          (subst
            (λ index → run left-term index ≡ blamed W)
            (+-identityʳ current)
            blame-eq)))
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {W}
      timeout-eq blame-eq
      rewrite +-suc current steps
      with run left-term (suc current) in next-eq
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {W}
      timeout-eq blame-eq
      | timed W₁ =
    let terminal-index , trace =
          left-first-blame-traceᵖ next-eq blame-eq
    in
    terminal-index , left-blame-timeout next-eq trace
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {W}
      timeout-eq blame-eq
      | blamed W₁
      with trans
        (sym
          (run-terminal-stable
            {N = left-term} {n = suc current}
            terminal-blame next-eq steps))
        blame-eq
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {.W₁}
      timeout-eq blame-eq
      | blamed W₁ | refl =
    suc current , left-blame next-eq
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {W}
      timeout-eq blame-eq
      | failed W₁ e =
    ⊥-elim
      (blamed≢failed
        (sym
          (trans
            (sym
              (run-terminal-stable
                {N = left-term} {n = suc current}
                terminal-error next-eq steps))
            blame-eq)))
  left-first-blame-traceᵖ
      {left-term} {current} {suc steps} {W₀} {W}
      timeout-eq blame-eq
      | returned W₁ V₁ =
    ⊥-elim
      (blamed≢returned
        (sym
          (trans
            (sym
              (run-terminal-stable
                {N = left-term} {n = suc current}
                terminal-return next-eq steps))
            blame-eq)))

  left-eventual-blame⇒traceᵖ :
    ∀ {left-term current W₀ m W} →
    run left-term current ≡ timed W₀ →
    run left-term m ≡ blamed W →
    Σ[ terminal-index ∈ StepIndex ]
      LeftBlameCatchUpTrace left-term
        current (suc m) terminal-index W
  left-eventual-blame⇒traceᵖ
      {left-term} {current} {W₀} {m} {W}
      timeout-eq blame-eq =
    left-first-blame-traceᵖ
      timeout-eq
      (run-terminal-after terminal-blame blame-eq current)
