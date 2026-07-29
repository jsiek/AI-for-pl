module InterpreterTraceExtraction where

-- File Charter:
--   * Exposes bounded first-terminal search for direct-interpreter runs.
--   * Converts eventual related returns and permitted left blame into finite
--     catch-up traces.
--   * Delegates implementations to a reduction-free proof module.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat using (suc; _+_)
open import Data.Product using (Σ-syntax)

open import Coercions using (Coercion)
import DoubleInterpreter as Double
import DoubleInterpreterCatchUp as DoubleProof
open import Interpreter
open import NuTerms using (Term)
import proof.InterpreterTraceExtractionProof as Proof
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

  module Implementation = Proof.TraceExtraction
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

  right-first-return-trace :
    ∀ {right-term W V current steps W₀′ W′ V′} →
    run right-term current ≡ timed W₀′ →
    run right-term (current + steps) ≡ returned W′ V′ →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      RightCatchUpTrace right-term W V
        current steps terminal-index W′ V′
  right-first-return-trace =
    Implementation.right-first-return-traceᵖ

  right-eventual-return⇒trace :
    ∀ {right-term W V current W₀′ m W′ V′} →
    run right-term current ≡ timed W₀′ →
    run right-term m ≡ returned W′ V′ →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      RightCatchUpTrace right-term W V
        current (suc m) terminal-index W′ V′
  right-eventual-return⇒trace =
    Implementation.right-eventual-return⇒traceᵖ

  left-first-return-trace :
    ∀ {left-term W′ V′ current steps W₀ W V} →
    run left-term current ≡ timed W₀ →
    run left-term (current + steps) ≡ returned W V →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      LeftCatchUpTrace left-term W′ V′
        current steps terminal-index W V
  left-first-return-trace =
    Implementation.left-first-return-traceᵖ

  left-eventual-return⇒trace :
    ∀ {left-term W′ V′ current W₀ m W V} →
    run left-term current ≡ timed W₀ →
    run left-term m ≡ returned W V →
    Joined W V W′ V′ →
    Σ[ terminal-index ∈ StepIndex ]
      LeftCatchUpTrace left-term W′ V′
        current (suc m) terminal-index W V
  left-eventual-return⇒trace =
    Implementation.left-eventual-return⇒traceᵖ

  left-first-blame-trace :
    ∀ {left-term current steps W₀ W} →
    run left-term current ≡ timed W₀ →
    run left-term (current + steps) ≡ blamed W →
    Σ[ terminal-index ∈ StepIndex ]
      LeftBlameCatchUpTrace left-term
        current steps terminal-index W
  left-first-blame-trace =
    Implementation.left-first-blame-traceᵖ

  left-eventual-blame⇒trace :
    ∀ {left-term current W₀ m W} →
    run left-term current ≡ timed W₀ →
    run left-term m ≡ blamed W →
    Σ[ terminal-index ∈ StepIndex ]
      LeftBlameCatchUpTrace left-term
        current (suc m) terminal-index W
  left-eventual-blame⇒trace =
    Implementation.left-eventual-blame⇒traceᵖ
