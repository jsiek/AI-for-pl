module proof.InterpreterValueNarrowingProof where

-- File Charter:
--   * Proves world-extension monotonicity for semantic values and term
--     environments.
--   * Covers every symmetric and explicitly asymmetric value constructor.
--   * Contains no evaluator or reduction argument.

open import Interpreter
open import Narrowing.InterpreterValueNarrowing
open import Narrowing.InterpreterWorldNarrowing
import Narrowing.InterpreterWorldNarrowingProperties as WorldProperties
open import Agda.Builtin.Equality using (refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary using (no; yes)
import proof.InterpreterValueScopeWeakeningProof as ScopeProof

mutual

  replace-name-scoped :
    ∀ {W θ X α} →
    Allocated W α →
    TypeEnvironmentScoped W θ →
    TypeEnvironmentScoped W (replaceName X α θ)
  replace-name-scoped α-ok []-scoped =
    []-scoped
  replace-name-scoped {X = X} {α}
      α-ok (abstract-scoped {X = Y} ∷-scoped θ-ok)
      with X ≟Name Y
  replace-name-scoped {X = X} {α}
      α-ok (abstract-scoped {X = .X} ∷-scoped θ-ok)
      | yes refl =
    seal-scoped α-ok ∷-scoped replace-name-scoped α-ok θ-ok
  replace-name-scoped {X = X} {α}
      α-ok (abstract-scoped {X = Y} ∷-scoped θ-ok)
      | no X≢Y =
    abstract-scoped ∷-scoped replace-name-scoped α-ok θ-ok
  replace-name-scoped α-ok
      (seal-scoped β-ok ∷-scoped θ-ok) =
    seal-scoped β-ok ∷-scoped replace-name-scoped α-ok θ-ok

  substitute-name-scoped :
    ∀ {W V α} →
    (X : Name) →
    Allocated W α →
    ValueScoped W V →
    ValueScoped W (substituteName X α V)
  substitute-name-scoped X α-ok
      (closure-scoped γ-ok θ-ok) =
    closure-scoped γ-ok (replace-name-scoped α-ok θ-ok)
  substitute-name-scoped X α-ok constant-scoped =
    constant-scoped
  substitute-name-scoped X α-ok
      (tagged-scoped θ-ok V-ok) =
    tagged-scoped
      (replace-name-scoped α-ok θ-ok)
      (substitute-name-scoped X α-ok V-ok)
  substitute-name-scoped X α-ok
      (sealed-scoped β-ok V-ok) =
    sealed-scoped β-ok
      (substitute-name-scoped X α-ok V-ok)
  substitute-name-scoped X α-ok
      (function-proxy-scoped θ-ok V-ok) =
    function-proxy-scoped
      (replace-name-scoped α-ok θ-ok)
      (substitute-name-scoped X α-ok V-ok)
  substitute-name-scoped X α-ok
      (type-abstraction-scoped {X = Y} V-ok)
      with X ≟Name Y
  substitute-name-scoped X α-ok
      (type-abstraction-scoped {X = .X} V-ok)
      | yes refl =
    type-abstraction-scoped V-ok
  substitute-name-scoped X α-ok
      (type-abstraction-scoped {X = Y} V-ok)
      | no X≢Y =
    type-abstraction-scoped
      (substitute-name-scoped X α-ok V-ok)
  substitute-name-scoped X α-ok
      (forall-proxy-scoped θ-ok V-ok) =
    forall-proxy-scoped
      (replace-name-scoped α-ok θ-ok)
      (substitute-name-scoped X α-ok V-ok)
  substitute-name-scoped X α-ok
      (generalized-scoped θ-ok V-ok) =
    generalized-scoped
      (replace-name-scoped α-ok θ-ok)
      (substitute-name-scoped X α-ok V-ok)

module ValueNarrowingProof
  (leaves : NarrowingLeaves)
  where

  module Values = ValueNarrowing leaves
  open Values
  open Values.RelatedWorlds

  module WorldProof =
    WorldProperties.WorldNarrowingProperties (TypeNarrowing leaves)

  module ScopeImplementation =
    ScopeProof.ValueScopeWeakeningProof leaves

  type-abstraction-narrowing-weaken :
    ∀ {W W′ U U′ X X′ V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    TypeAbstractionNarrowing R X X′ V V′ →
    TypeAbstractionNarrowing S X X′ V V′
  type-abstraction-narrowing-weaken R≤S
      (related-type-abstraction V-ok V′-ok instantiate) =
    related-type-abstraction
      (ScopeImplementation.value-left-scope-weaken R≤S V-ok)
      (ScopeImplementation.value-right-scope-weaken R≤S V′-ok)
      (λ S≤T A~A′ θ~θ′ →
        instantiate
          (WorldProof.world-extension-trans R≤S S≤T)
          A~A′ θ~θ′)

  left-type-abstraction-narrowing-weaken :
    ∀ {W W′ U U′ X V V′}
      {R : WorldRelation W W′}
      {S : WorldRelation U U′} →
    WorldExtension R S →
    LeftTypeAbstractionNarrowing R X V V′ →
    LeftTypeAbstractionNarrowing S X V V′
  left-type-abstraction-narrowing-weaken R≤S
      (related-left-type-abstraction V-ok V′-ok instantiate) =
    related-left-type-abstraction
      (ScopeImplementation.value-left-scope-weaken R≤S V-ok)
      (ScopeImplementation.value-right-scope-weaken R≤S V′-ok)
      (λ S≤T σ-ok →
        instantiate
          (WorldProof.world-extension-trans R≤S S≤T)
          σ-ok)

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
      closure⊑
        (BodyNarrowingWeaken leaves R≤S N~N′)
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
        (left-dynamic-sealed⊑ dynamic V′-not-sealed V~V′) =
      left-dynamic-sealed⊑
        (WorldProof.left-dynamic-seal-weaken R≤S dynamic)
        V′-not-sealed
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (function-proxy⊑ p~p′ q~q′ θ~θ′ V~V′) =
      function-proxy⊑
        (CoercionNarrowingWeaken leaves R≤S p~p′)
        (CoercionNarrowingWeaken leaves R≤S q~q′)
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (type-abstraction⊑ abstraction) =
      type-abstraction⊑
        (type-abstraction-narrowing-weaken R≤S abstraction)
    value-narrowing-weaken R≤S
        (left-type-abstraction⊑ boundary abstraction) =
      left-type-abstraction⊑ boundary
        (left-type-abstraction-narrowing-weaken
          R≤S abstraction)
    value-narrowing-weaken R≤S
        (forall-proxy⊑ c~c′ θ~θ′ V~V′) =
      forall-proxy⊑
        (CoercionNarrowingWeaken leaves R≤S c~c′)
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (generalized⊑ A~A′ c~c′ θ~θ′ V~V′) =
      generalized⊑ A~A′
        (CoercionNarrowingWeaken leaves R≤S c~c′)
        (WorldProof.type-environment-narrowing-weaken R≤S θ~θ′)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (quotient-value-frame⊑ frame U-ok U′-ok V~V′) =
      quotient-value-frame⊑
        (QuotientValueFrameWeaken leaves R≤S frame)
        (ScopeImplementation.value-left-scope-weaken R≤S U-ok)
        (ScopeImplementation.value-right-scope-weaken R≤S U′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken S≤T
        (left-name-instantiated⊑ R≤S α-ok result-eq V~V′) =
      left-name-instantiated⊑
        (WorldProof.world-extension-trans R≤S S≤T)
        (WorldProof.allocated-left-weaken S≤T α-ok)
        result-eq
        V~V′
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
      left-function-proxy⊑
        (LeftFunctionProxyBoundaryWeaken leaves R≤S boundary)
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-function-proxy⊑ boundary θ′-ok V~V′) =
      right-function-proxy⊑
        (RightFunctionProxyBoundaryWeaken leaves R≤S boundary)
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-forall-proxy⊑ boundary θ-ok V~V′) =
      left-forall-proxy⊑
        (LeftForallProxyBoundaryWeaken leaves R≤S boundary)
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-forall-proxy⊑ boundary θ′-ok V~V′) =
      right-forall-proxy⊑
        (RightForallProxyBoundaryWeaken leaves R≤S boundary)
        (WorldProof.type-environment-right-scope-weaken R≤S θ′-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (left-generalized⊑ boundary θ-ok V~V′) =
      left-generalized⊑
        (LeftGeneralizationBoundaryWeaken leaves R≤S boundary)
        (WorldProof.type-environment-left-scope-weaken R≤S θ-ok)
        (value-narrowing-weaken R≤S V~V′)
    value-narrowing-weaken R≤S
        (right-generalized⊑ boundary θ′-ok V~V′) =
      right-generalized⊑
        (RightGeneralizationBoundaryWeaken leaves R≤S boundary)
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
        (left-dynamic-sealed⊑ dynamic V′-not-sealed V~V′) =
      sealed-scoped
        (WorldProof.left-dynamic-seal-allocated dynamic)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      proj₂ (value-narrowing-scoped V~V′)
    value-narrowing-scoped
        (function-proxy⊑ p~p′ q~q′ θ~θ′ V~V′) =
      function-proxy-scoped
        (WorldProof.type-environment-left-scoped θ~θ′)
        (proj₁ (value-narrowing-scoped V~V′)) ,
      function-proxy-scoped
        (WorldProof.type-environment-right-scoped θ~θ′)
        (proj₂ (value-narrowing-scoped V~V′))
    value-narrowing-scoped
        (type-abstraction⊑ abstraction) =
      type-abstraction-scoped
        (left-body-scoped abstraction) ,
      type-abstraction-scoped
        (right-body-scoped abstraction)
    value-narrowing-scoped
        (left-type-abstraction⊑ boundary abstraction) =
      type-abstraction-scoped
        (left-source-body-scoped abstraction) ,
      right-target-scoped abstraction
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
        (quotient-value-frame⊑ frame U-ok U′-ok V~V′) =
      U-ok , U′-ok
    value-narrowing-scoped
        (left-name-instantiated⊑
          {X = X} R≤S α-ok result-eq V~V′) =
      subst (ValueScoped _)
        result-eq
        (substitute-name-scoped X α-ok
          (ScopeImplementation.value-left-scope-weaken R≤S
            (proj₁ (value-narrowing-scoped V~V′)))) ,
      ScopeImplementation.value-right-scope-weaken R≤S
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
