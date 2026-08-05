module Simulation.Coercion.InterpreterQuotientValueElimination where

-- File Charter:
--   * Public quotient-frame observations for active interpreter operations.
--   * Exposes related tag, function, forall, and generalized payloads.
--   * States every result directly and delegates reduction-free proofs.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; Σ-syntax)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing
open import Narrowing.InterpreterQuotientValueNarrowing
open import Narrowing.InterpreterTermNarrowing
open import Narrowing.InterpreterTagNarrowingCore using (TagNarrowing)
open import Narrowing.InterpreterValueNarrowing using (ValueScoped)
open import Types
import proof.InterpreterQuotientValueEliminationProof as Proof

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

quotient-related-tagged-payloads :
  ∀ {W W′ V V′ U U′ G H θ θ′}
    {R : WorldRelation W W′}
    {gG : Ground G} {gH : Ground H} →
  InterpreterQuotientValueFrame R V V′
    (tagged gG θ U) (tagged gH θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  InterpreterGroundNarrowing gG gH ×
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-tagged-payloads =
  Proof.quotient-related-tagged-payloads

quotient-related-tag-observation :
  ∀ {W W′ V V′ U U′ G H θ θ′}
    {R : WorldRelation W W′}
    {gG : Ground G} {gH : Ground H} →
  InterpreterQuotientValueFrame R V V′
    (tagged gG θ U) (tagged gH θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  Σ[ tag ∈ Tag ]
  Σ[ tag′ ∈ Tag ]
    tagOf θ gG ≡ just tag ×
    tagOf θ′ gH ≡ just tag′ ×
    TagNarrowing R tag tag′ ×
    ValueNarrowing R U U′
quotient-related-tag-observation =
  Proof.quotient-related-tag-observation

quotient-related-function-payloads :
  ∀ {W W′ V V′ U U′ p p′ q q′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (function-proxy p q θ U)
    (function-proxy p′ q′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-function-payloads =
  Proof.quotient-related-function-payloads

quotient-related-forall-payloads :
  ∀ {W W′ V V′ U U′ c c′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (forall-proxy c θ U) (forall-proxy c′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-forall-payloads =
  Proof.quotient-related-forall-payloads

quotient-related-generalized-payloads :
  ∀ {W W′ V V′ U U′ A A′ c c′ θ θ′}
    {R : WorldRelation W W′} →
  InterpreterQuotientValueFrame R V V′
    (generalized A c θ U) (generalized A′ c′ θ′ U′) →
  ValueScoped W U →
  ValueScoped W′ U′ →
  ValueNarrowing R V V′ →
  TypeEnvironmentNarrowing R θ θ′ ×
  ValueNarrowing R U U′
quotient-related-generalized-payloads =
  Proof.quotient-related-generalized-payloads
