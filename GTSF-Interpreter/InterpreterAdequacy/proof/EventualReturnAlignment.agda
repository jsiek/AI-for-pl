module InterpreterAdequacy.proof.EventualReturnAlignment where

-- File Charter:
--   * Aligns successful generalized interpreter-entry calls with independently
--     supplied terminating traces.
--   * Uses the already proved return soundness plus deterministic reduction.
--   * Exposes exact world paths and terminal value agreements to the
--     completeness driver.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Nat using (zero)
open import Data.Product using (_,_; Σ-syntax)

import Coercions as C
open import Interpreter
open import InterpreterAdequacy.TraceAgreement
open import InterpreterAdequacy.proof.ReturnCompletenessAlignment using
  (value-traces-deterministic)
open import InterpreterAdequacy.proof.ReturnTrace
import InterpreterAdequacy.proof.TraceAgreementProperties as Properties
open import InterpreterAdequacy.proof.RunReturnSoundnessProof using
  ( apply-return-soundᵢ
  ; coerce-return-soundᵢ
  ; instantiate-return-soundᵢ
  ; interpret-return-soundᵢ
  )
open import NuReduction using (_—↠[_]_)
import NuTerms as N

align-return-trace :
  ∀ {W prefix U V P changes v}
    {world-agreement : WorldTraceAgreement W prefix} →
  ReturnTrace world-agreement P U V →
  P —↠[ changes ] v →
  N.Value v →
  Σ[ path ∈ WorldTracePath W changes U ]
    ValueTraceAgreement
      (Properties.world-trace-agreement-++ world-agreement path)
      [] V v
align-return-trace
    (return-trace sound-changes u path sound-trace V-agrees)
    supplied vV
    with value-traces-deterministic supplied vV sound-trace
      (Properties.value-trace-value V-agrees)
align-return-trace
    (return-trace ._ ._ path sound-trace V-agrees)
    supplied vV | refl , refl =
  path , V-agrees

align-interpret-return :
  ∀ {W prefix γ θ M P n U V changes v}
    (world-agreement : WorldTraceAgreement W prefix) →
  N.No• M →
  TermTraceAgreement world-agreement [] γ θ M P →
  P —↠[ changes ] v →
  N.Value v →
  interpret W γ θ M n ≡ returned U V →
  Σ[ path ∈ WorldTracePath W changes U ]
    ValueTraceAgreement
      (Properties.world-trace-agreement-++ world-agreement path)
      [] V v
align-interpret-return {n = n} world-agreement no-M M-agrees
    trace vV result-eq =
  align-return-trace
    (interpret-return-soundᵢ n world-agreement no-M M-agrees result-eq)
    trace vV

align-apply-return :
  ∀ {W prefix F f U u n Z R changes v}
    (world-agreement : WorldTraceAgreement W prefix) →
  ValueTraceAgreement world-agreement [] F f →
  ValueTraceAgreement world-agreement [] U u →
  (f N.· u) —↠[ changes ] v →
  N.Value v →
  applyValue W F U n ≡ returned Z R →
  Σ[ path ∈ WorldTracePath W changes Z ]
    ValueTraceAgreement
      (Properties.world-trace-agreement-++ world-agreement path)
      [] R v
align-apply-return {n = n} world-agreement F-agrees U-agrees
    trace vV result-eq =
  align-return-trace
    (apply-return-soundᵢ n world-agreement F-agrees U-agrees result-eq)
    trace vV

align-instantiate-return :
  ∀ {W prefix α F f n Z R changes v}
    (world-agreement : WorldTraceAgreement W prefix) →
  lookup (visibleTypeNames [] W) zero ≡ just (seal-name α) →
  ValueTraceAgreement world-agreement [] F f →
  (f N.•) —↠[ changes ] v →
  N.Value v →
  instantiateValue W α F n ≡ returned Z R →
  Σ[ path ∈ WorldTracePath W changes Z ]
    ValueTraceAgreement
      (Properties.world-trace-agreement-++ world-agreement path)
      [] R v
align-instantiate-return {n = n} world-agreement newest F-agrees
    trace vV result-eq =
  align-return-trace
    (instantiate-return-soundᵢ
      n world-agreement newest F-agrees result-eq)
    trace vV

align-coerce-return :
  ∀ {W prefix θ τ c V v n Z R changes u}
    (world-agreement : WorldTraceAgreement W prefix) →
  TypeEnvironmentTraceAgreement world-agreement [] θ τ →
  ValueTraceAgreement world-agreement [] V v →
  (v N.⟨ C.renameᶜ τ c ⟩) —↠[ changes ] u →
  N.Value u →
  coerceValue W θ c V n ≡ returned Z R →
  Σ[ path ∈ WorldTracePath W changes Z ]
    ValueTraceAgreement
      (Properties.world-trace-agreement-++ world-agreement path)
      [] R u
align-coerce-return {n = n} world-agreement θ-agrees V-agrees
    trace vU result-eq =
  align-return-trace
    (coerce-return-soundᵢ
      n world-agreement θ-agrees V-agrees result-eq)
    trace vU
