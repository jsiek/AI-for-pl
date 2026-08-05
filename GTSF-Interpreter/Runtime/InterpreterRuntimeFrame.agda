module Runtime.InterpreterRuntimeFrame where

-- File Charter:
--   * Defines the persistent, non-typing part of a synchronized runtime.
--   * Retains static runtime contexts and concrete store/type-environment
--     realization inside closures, proxies, tags, and generalized values.
--   * Proves Kripke weakening without depending on semantic value narrowing.
--   * Contains no interpreter call or reduction semantics.

open import Data.Product using (_,_)
open import Data.Nat using (_≤_)

open import ImprecisionWf using (ImpCtx)
open import Interpreter
open import Narrowing.InterpreterCoercionNarrowing using
  (InterpreterTypeNarrowing)
import Typing.InterpreterSemanticTypingCore
open Typing.InterpreterSemanticTypingCore using (RuntimeContext)
open import Runtime.InterpreterStoreCorrespondenceRealization using
  ( StoreCorrespondenceRealization
  ; store-correspondence-realization
  ; realizes-store-correspondence
  )
open import Runtime.InterpreterTypeEnvironmentRealization using
  ( SourceDynamicName
  ; source-dynamic-abstract
  ; source-dynamic-seal
  ; AssumptionRealization
  ; paired-assumption
  ; source-dynamic-assumption
  ; TypeEnvironmentRealization
  ; type-environment-realization
  ; environments-narrow
  ; realizes-assumption
  )
import Narrowing.InterpreterWorldNarrowing
open import Narrowing.InterpreterWorldNarrowingProperties
import NuTermImprecision as NTI
import proof.InterpreterSemanticTypingProperties as SemanticProof
open import Types

module RelatedWorlds =
  Narrowing.InterpreterWorldNarrowing.WorldNarrowing
    InterpreterTypeNarrowing

open RelatedWorlds

module WorldProperties =
  WorldNarrowingProperties InterpreterTypeNarrowing

record RuntimeFrameNarrowing
    {W W′ : World}
    (R : WorldRelation W W′)
    (Φ : ImpCtx) (Δᴸ Δᴿ : TyCtx)
    (ρ : NTI.StoreImp Φ Δᴸ Δᴿ)
    (θ θ′ : TypeEnvironment) : Set₁ where
  constructor runtime-frame-narrowing
  field
    left-runtime-context :
      RuntimeContext W Δᴸ (NTI.leftStoreⁱ ρ) θ

    right-runtime-context :
      RuntimeContext W′ Δᴿ (NTI.rightStoreⁱ ρ) θ′

    store-correspondences-realized :
      StoreCorrespondenceRealization R Φ Δᴸ Δᴿ ρ θ θ′

    type-environments-realized :
      TypeEnvironmentRealization R Φ θ θ′

    abstract-supply :
      nextAbstractIndex θ′ ≤ nextAbstractIndex θ

open RuntimeFrameNarrowing public

left-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W U
left-world-extension extension-refl =
  Typing.InterpreterSemanticTypingCore.world-extension-refl
left-world-extension (extension-both R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (left-world-extension R≤S)
left-world-extension (extension-left R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (left-world-extension R≤S)
left-world-extension (extension-right R≤S) =
  left-world-extension R≤S
left-world-extension (extension-crossed R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (Typing.InterpreterSemanticTypingCore.world-extension-allocate
      (left-world-extension R≤S))

right-world-extension :
  ∀ {W W′ U U′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  Typing.InterpreterSemanticTypingCore.WorldExtension W′ U′
right-world-extension extension-refl =
  Typing.InterpreterSemanticTypingCore.world-extension-refl
right-world-extension (extension-both R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (right-world-extension R≤S)
right-world-extension (extension-left R≤S) =
  right-world-extension R≤S
right-world-extension (extension-right R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (right-world-extension R≤S)
right-world-extension (extension-crossed R≤S) =
  Typing.InterpreterSemanticTypingCore.world-extension-allocate
    (Typing.InterpreterSemanticTypingCore.world-extension-allocate
      (right-world-extension R≤S))

source-dynamic-name-weaken :
  ∀ {W W′ U U′ R S name} →
  WorldExtension {W} {W′} R {U} {U′} S →
  SourceDynamicName R name →
  SourceDynamicName S name
source-dynamic-name-weaken R≤S source-dynamic-abstract =
  source-dynamic-abstract
source-dynamic-name-weaken R≤S
    (source-dynamic-seal dynamic) =
  source-dynamic-seal
    (WorldProperties.left-dynamic-seal-weaken R≤S dynamic)

assumption-realization-weaken :
  ∀ {W W′ U U′ R S θ θ′ assumption} →
  WorldExtension {W} {W′} R {U} {U′} S →
  AssumptionRealization R θ θ′ assumption →
  AssumptionRealization S θ θ′ assumption
assumption-realization-weaken R≤S
    (paired-assumption left-at right-at name~name′) =
  paired-assumption left-at right-at
    (WorldProperties.type-name-narrowing-weaken R≤S name~name′)
assumption-realization-weaken R≤S
    (source-dynamic-assumption left-at name-ok) =
  source-dynamic-assumption left-at
    (source-dynamic-name-weaken R≤S name-ok)

type-environment-realization-weaken :
  ∀ {W W′ U U′ Φ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  TypeEnvironmentRealization R Φ θ θ′ →
  TypeEnvironmentRealization S Φ θ θ′
type-environment-realization-weaken R≤S realization =
  type-environment-realization
    (WorldProperties.type-environment-narrowing-weaken R≤S
      (environments-narrow realization))
    (λ assumption-at →
      assumption-realization-weaken R≤S
        (realizes-assumption realization assumption-at))

store-correspondence-realization-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  StoreCorrespondenceRealization R Φ Δᴸ Δᴿ ρ θ θ′ →
  StoreCorrespondenceRealization S Φ Δᴸ Δᴿ ρ θ θ′
store-correspondence-realization-weaken R≤S realization =
  store-correspondence-realization
    λ corresponds →
      let seal , seal′ , left-at , right-at , seal~seal′ =
            realizes-store-correspondence realization corresponds
      in
      seal , seal′ , left-at , right-at ,
      WorldProperties.seal-link-weaken R≤S seal~seal′

runtime-frame-weaken :
  ∀ {W W′ U U′ Φ Δᴸ Δᴿ ρ θ θ′}
    {R : WorldRelation W W′}
    {S : WorldRelation U U′} →
  WorldExtension R S →
  RuntimeFrameNarrowing R Φ Δᴸ Δᴿ ρ θ θ′ →
  RuntimeFrameNarrowing S Φ Δᴸ Δᴿ ρ θ θ′
runtime-frame-weaken R≤S runtime =
  runtime-frame-narrowing
    (SemanticProof.runtime-context-weaken
      (left-world-extension R≤S)
      (left-runtime-context runtime))
    (SemanticProof.runtime-context-weaken
      (right-world-extension R≤S)
      (right-runtime-context runtime))
    (store-correspondence-realization-weaken R≤S
      (store-correspondences-realized runtime))
    (type-environment-realization-weaken R≤S
      (type-environments-realized runtime))
    (abstract-supply runtime)
