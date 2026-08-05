module proof.InterpreterDynamicSealValueEliminationProof where

-- File Charter:
--   * Inverts source-dynamic sealed value narrowing.
--   * Excludes paired seals by target typing and quotient seals structurally.
--   * Contains no interpreter computation or reduction semantics.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)

open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Narrowing.InterpreterEnvironmentNarrowing as EnvironmentProperties
open import Narrowing.InterpreterQuotientValueNarrowing using
  (quotient-value-frame-source-not-sealed)
open import Narrowing.InterpreterTermNarrowing
open import Runtime.InterpreterValueSubstitutionShape using
  (substitute-name-sealed-source)
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties

open InterpreterValues
open Narrowing.InterpreterTermNarrowing.RelatedWorlds

module WorldProof =
  WorldProperties.WorldNarrowingProperties
    InterpreterTypeNarrowing

module EnvironmentProof =
  EnvironmentProperties.EnvironmentNarrowing
    interpreterNarrowingLeaves

sealed-payload-injective :
  ∀ {α V U} →
  sealed α V ≡ sealed α U →
  V ≡ U
sealed-payload-injective refl =
  refl

left-dynamic-sealed-payloads-after :
  ∀ {W W′ U U′ α V V′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  LeftDynamicSeal S α →
  ValueNarrowing R (sealed α V) V′ →
  ValueNarrowing S V V′
left-dynamic-sealed-payloads-after
    R≤S dynamic (sealed⊑ α~α′ V~V′) =
  ⊥-elim
    (WorldProof.left-dynamic-seal-not-linked dynamic
      (WorldProof.seal-link-weaken R≤S α~α′))
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (left-dynamic-sealed⊑
      other-dynamic V′-not-sealed V~V′) =
  EnvironmentProof.value-narrowing-weaken R≤S V~V′
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (quotient-value-frame⊑ frame U-ok U′-ok V~V′) =
  ⊥-elim (quotient-value-frame-source-not-sealed frame)
left-dynamic-sealed-payloads-after
    {α = source} R≤S dynamic
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = V}
      T≤R fresh-ok result-eq V~V′)
    with substitute-name-sealed-source X fresh V result-eq
left-dynamic-sealed-payloads-after
    {α = source} R≤S dynamic
    (left-name-instantiated⊑
      {X = X} {α = fresh} {V = .(sealed source Q)}
      T≤R fresh-ok result-eq V~V′)
    | Q , refl =
  left-name-instantiated⊑
    extension-refl
    (WorldProof.allocated-left-weaken R≤S fresh-ok)
    (sealed-payload-injective result-eq)
    (left-dynamic-sealed-payloads-after
      {V = Q}
      (WorldProof.world-extension-trans T≤R R≤S)
      dynamic V~V′)
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (right-tagged⊑ boundary θ′-ok V~V′) =
  right-tagged⊑ boundary
    (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
    (left-dynamic-sealed-payloads-after R≤S dynamic V~V′)
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (right-function-proxy⊑ boundary θ′-ok V~V′) =
  right-function-proxy⊑
    (persistent-right-function-weaken R≤S boundary)
    (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
    (left-dynamic-sealed-payloads-after R≤S dynamic V~V′)
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (right-forall-proxy⊑ boundary θ′-ok V~V′) =
  right-forall-proxy⊑
    (persistent-right-forall-weaken R≤S boundary)
    (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
    (left-dynamic-sealed-payloads-after R≤S dynamic V~V′)
left-dynamic-sealed-payloads-after
    R≤S dynamic
    (right-generalized⊑ boundary θ′-ok V~V′) =
  right-generalized⊑
    (persistent-right-generalization-weaken R≤S boundary)
    (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
    (left-dynamic-sealed-payloads-after R≤S dynamic V~V′)

left-dynamic-sealed-payloads :
  ∀ {W W′ α V V′}
    {R : WorldRelation W W′} →
  LeftDynamicSeal R α →
  ValueNarrowing R (sealed α V) V′ →
  ValueNarrowing R V V′
left-dynamic-sealed-payloads dynamic V~V′ =
  left-dynamic-sealed-payloads-after
    extension-refl dynamic V~V′
