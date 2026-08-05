module proof.InterpreterValueScopeWeakeningProof where

-- File Charter:
--   * Weakens unary semantic-value and environment scope through a related
--     world extension.
--   * Supplies the scope fields needed by alpha-aware type abstractions.
--   * Contains no value-narrowing, evaluator, or reduction argument.

open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties

module ValueScopeWeakeningProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module WorldProof =
    WorldProperties.WorldNarrowingProperties (TypeNarrowing leaves)

  mutual

    value-left-scope-weaken :
      ∀ {W W′ U U′ V}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      ValueScoped W V →
      ValueScoped U V
    value-left-scope-weaken R≤S
        (closure-scoped γ-ok θ-ok) =
      closure-scoped
        (environment-left-scope-weaken R≤S γ-ok)
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
    value-left-scope-weaken R≤S constant-scoped =
      constant-scoped
    value-left-scope-weaken R≤S
        (tagged-scoped θ-ok V-ok) =
      tagged-scoped
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-left-scope-weaken R≤S V-ok)
    value-left-scope-weaken R≤S
        (sealed-scoped α-ok V-ok) =
      sealed-scoped
        (WorldProof.allocated-left-weaken R≤S α-ok)
        (value-left-scope-weaken R≤S V-ok)
    value-left-scope-weaken R≤S
        (function-proxy-scoped θ-ok V-ok) =
      function-proxy-scoped
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-left-scope-weaken R≤S V-ok)
    value-left-scope-weaken R≤S
        (type-abstraction-scoped V-ok) =
      type-abstraction-scoped
        (value-left-scope-weaken R≤S V-ok)
    value-left-scope-weaken R≤S
        (forall-proxy-scoped θ-ok V-ok) =
      forall-proxy-scoped
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-left-scope-weaken R≤S V-ok)
    value-left-scope-weaken R≤S
        (generalized-scoped θ-ok V-ok) =
      generalized-scoped
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-left-scope-weaken R≤S V-ok)

    environment-left-scope-weaken :
      ∀ {W W′ U U′ γ}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      EnvironmentScoped W γ →
      EnvironmentScoped U γ
    environment-left-scope-weaken R≤S []-environment-scoped =
      []-environment-scoped
    environment-left-scope-weaken R≤S
        (V-ok ∷-environment-scoped γ-ok) =
      value-left-scope-weaken R≤S V-ok ∷-environment-scoped
        environment-left-scope-weaken R≤S γ-ok

  mutual

    value-right-scope-weaken :
      ∀ {W W′ U U′ V′}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      ValueScoped W′ V′ →
      ValueScoped U′ V′
    value-right-scope-weaken R≤S
        (closure-scoped γ′-ok θ′-ok) =
      closure-scoped
        (environment-right-scope-weaken R≤S γ′-ok)
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
    value-right-scope-weaken R≤S constant-scoped =
      constant-scoped
    value-right-scope-weaken R≤S
        (tagged-scoped θ′-ok V′-ok) =
      tagged-scoped
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-right-scope-weaken R≤S V′-ok)
    value-right-scope-weaken R≤S
        (sealed-scoped α′-ok V′-ok) =
      sealed-scoped
        (WorldProof.allocated-right-weaken R≤S α′-ok)
        (value-right-scope-weaken R≤S V′-ok)
    value-right-scope-weaken R≤S
        (function-proxy-scoped θ′-ok V′-ok) =
      function-proxy-scoped
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-right-scope-weaken R≤S V′-ok)
    value-right-scope-weaken R≤S
        (type-abstraction-scoped V′-ok) =
      type-abstraction-scoped
        (value-right-scope-weaken R≤S V′-ok)
    value-right-scope-weaken R≤S
        (forall-proxy-scoped θ′-ok V′-ok) =
      forall-proxy-scoped
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-right-scope-weaken R≤S V′-ok)
    value-right-scope-weaken R≤S
        (generalized-scoped θ′-ok V′-ok) =
      generalized-scoped
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-right-scope-weaken R≤S V′-ok)

    environment-right-scope-weaken :
      ∀ {W W′ U U′ γ′}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      EnvironmentScoped W′ γ′ →
      EnvironmentScoped U′ γ′
    environment-right-scope-weaken R≤S []-environment-scoped =
      []-environment-scoped
    environment-right-scope-weaken R≤S
        (V′-ok ∷-environment-scoped γ′-ok) =
      value-right-scope-weaken R≤S V′-ok ∷-environment-scoped
        environment-right-scope-weaken R≤S γ′-ok
