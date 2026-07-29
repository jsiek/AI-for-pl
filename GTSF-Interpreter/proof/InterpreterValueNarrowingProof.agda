module proof.InterpreterValueNarrowingProof where

-- File Charter:
--   * Proves world-extension monotonicity for semantic values and term
--     environments.
--   * Covers every symmetric and explicitly asymmetric value constructor.
--   * Contains no evaluator or reduction argument.

open import Interpreter
open import InterpreterValueNarrowing
open import InterpreterWorldNarrowing
import InterpreterWorldNarrowingProperties as WorldProperties
open import Data.Product using (_×_; _,_; proj₁; proj₂)

module ValueNarrowingProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module WorldProof =
    WorldProperties.WorldNarrowingProperties (TypeNarrowing leaves)

  mutual

    value-narrowing-weaken :
      ∀ {W W′ U U′ V V′}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      ValueNarrowing R V V′ →
      ValueNarrowing S V V′
    value-narrowing-weaken R≤S
        (closure⊑ N~N′ γ~γ′ θ~θ′) =
      closure⊑ N~N′
        (environment-narrowing-weaken R≤S γ~γ′)
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
    value-narrowing-weaken R≤S (constant⊑ κ) =
      constant⊑ κ
    value-narrowing-weaken R≤S
        (tagged⊑ G~H θ~θ′ V~V′) =
      tagged⊑ G~H
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S (sealed⊑ α~α′ V~V′) =
      sealed⊑
        (WorldProof.seal-link-weaken R≤S α~α′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (function-proxy⊑ p~p′ q~q′ θ~θ′ V~V′) =
      function-proxy⊑ p~p′ q~q′
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S (type-abstraction⊑ V~V′) =
      type-abstraction⊑ (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (forall-proxy⊑ c~c′ θ~θ′ V~V′) =
      forall-proxy⊑ c~c′
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (generalized⊑ A~A′ c~c′ θ~θ′ V~V′) =
      generalized⊑ A~A′ c~c′
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-tagged⊑ boundary θ-ok V~V′) =
      left-tagged⊑ boundary
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-tagged⊑ boundary θ′-ok V~V′) =
      right-tagged⊑ boundary
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-function-proxy⊑ boundary θ-ok V~V′) =
      left-function-proxy⊑ boundary
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-function-proxy⊑ boundary θ′-ok V~V′) =
      right-function-proxy⊑ boundary
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-forall-proxy⊑ boundary θ-ok V~V′) =
      left-forall-proxy⊑ boundary
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-forall-proxy⊑ boundary θ′-ok V~V′) =
      right-forall-proxy⊑ boundary
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-generalized⊑ boundary θ-ok V~V′) =
      left-generalized⊑ boundary
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-generalized⊑ boundary θ′-ok V~V′) =
      right-generalized⊑ boundary
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)

    environment-narrowing-weaken :
      ∀ {W W′ U U′ γ γ′}
        {R : WorldRelation W W′}
        {S : WorldRelation U U′} →
      WorldExtension R S →
      EnvironmentNarrowing R γ γ′ →
      EnvironmentNarrowing S γ γ′
    environment-narrowing-weaken R≤S []⊑[]ᵉ =
      []⊑[]ᵉ
    environment-narrowing-weaken
        R≤S (V~V′ ∷⊑∷ᵉ γ~γ′) =
      value-narrowing-weaken R≤S V~V′ ∷⊑∷ᵉ
        environment-narrowing-weaken R≤S γ~γ′

  mutual

    value-narrowing-scoped :
      ∀ {W W′ V V′}
        {R : WorldRelation W W′} →
      ValueNarrowing R V V′ →
      ValueScoped W V × ValueScoped W′ V′
    value-narrowing-scoped
        (closure⊑ N~N′ γ~γ′ θ~θ′) =
      closure-scoped
        (proj₁ (environment-narrowing-scoped γ~γ′))
        (WorldProof.type-environment-left-scoped θ~θ′) ,
      closure-scoped
        (proj₂ (environment-narrowing-scoped γ~γ′))
        (WorldProof.type-environment-right-scoped θ~θ′)
    value-narrowing-scoped (constant⊑ κ) =
      constant-scoped , constant-scoped
    value-narrowing-scoped (tagged⊑ G~H θ~θ′ V~V′) =
      tagged-scoped
        (WorldProof.type-environment-left-scoped θ~θ′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      tagged-scoped
        (WorldProof.type-environment-right-scoped θ~θ′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped (sealed⊑ α~α′ V~V′) =
      sealed-scoped
        (WorldProof.seal-link-left-allocated α~α′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      sealed-scoped
        (WorldProof.seal-link-right-allocated α~α′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (function-proxy⊑ p~p′ q~q′ θ~θ′ V~V′) =
      function-proxy-scoped
        (WorldProof.type-environment-left-scoped θ~θ′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      function-proxy-scoped
        (WorldProof.type-environment-right-scoped θ~θ′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped (type-abstraction⊑ V~V′) =
      type-abstraction-scoped
        (proj₁ (value-narrowing-scoped V~V′)) ,
      type-abstraction-scoped
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped (forall-proxy⊑ c~c′ θ~θ′ V~V′) =
      forall-proxy-scoped
        (WorldProof.type-environment-left-scoped θ~θ′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      forall-proxy-scoped
        (WorldProof.type-environment-right-scoped θ~θ′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (generalized⊑ A~A′ c~c′ θ~θ′ V~V′) =
      generalized-scoped
        (WorldProof.type-environment-left-scoped θ~θ′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      generalized-scoped
        (WorldProof.type-environment-right-scoped θ~θ′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (left-tagged⊑ boundary θ-ok V~V′) =
      tagged-scoped θ-ok
        (proj₁ (value-narrowing-scoped V~V′)) ,
      proj₂ (value-narrowing-scoped V~V′)
    value-narrowing-scoped
        (right-tagged⊑ boundary θ′-ok V~V′) =
      proj₁ (value-narrowing-scoped V~V′) ,
      tagged-scoped θ′-ok
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (left-function-proxy⊑ boundary θ-ok V~V′) =
      function-proxy-scoped θ-ok
        (proj₁ (value-narrowing-scoped V~V′)) ,
      proj₂ (value-narrowing-scoped V~V′)
    value-narrowing-scoped
        (right-function-proxy⊑ boundary θ′-ok V~V′) =
      proj₁ (value-narrowing-scoped V~V′) ,
      function-proxy-scoped θ′-ok
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (left-forall-proxy⊑ boundary θ-ok V~V′) =
      forall-proxy-scoped θ-ok
        (proj₁ (value-narrowing-scoped V~V′)) ,
      proj₂ (value-narrowing-scoped V~V′)
    value-narrowing-scoped
        (right-forall-proxy⊑ boundary θ′-ok V~V′) =
      proj₁ (value-narrowing-scoped V~V′) ,
      forall-proxy-scoped θ′-ok
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (left-generalized⊑ boundary θ-ok V~V′) =
      generalized-scoped θ-ok
        (proj₁ (value-narrowing-scoped V~V′)) ,
      proj₂ (value-narrowing-scoped V~V′)
    value-narrowing-scoped
        (right-generalized⊑ boundary θ′-ok V~V′) =
      proj₁ (value-narrowing-scoped V~V′) ,
      generalized-scoped θ′-ok
        (proj₂ (value-narrowing-scoped V~V′))

    environment-narrowing-scoped :
      ∀ {W W′ γ γ′}
        {R : WorldRelation W W′} →
      EnvironmentNarrowing R γ γ′ →
      EnvironmentScoped W γ × EnvironmentScoped W′ γ′
    environment-narrowing-scoped []⊑[]ᵉ =
      []-environment-scoped , []-environment-scoped
    environment-narrowing-scoped (V~V′ ∷⊑∷ᵉ γ~γ′) =
      proj₁ (value-narrowing-scoped V~V′) ∷-environment-scoped
        proj₁ (environment-narrowing-scoped γ~γ′) ,
      proj₂ (value-narrowing-scoped V~V′) ∷-environment-scoped
        proj₂ (environment-narrowing-scoped γ~γ′)
