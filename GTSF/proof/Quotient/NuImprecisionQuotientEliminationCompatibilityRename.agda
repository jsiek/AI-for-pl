module
  proof.Quotient.NuImprecisionQuotientEliminationCompatibilityRename
  where

-- File Charter:
--   * Proves two-sided and source-only type-renaming preservation for paired
--     widening compatibility and the mutually recursive quotient widening
--     and narrowing-elimination compatibility evidence.
--   * Renames function-domain elimination and function-codomain widening
--     evidence in one mutual traversal, so neither live relation depends on
--     a separate compatibility-renaming module.
--   * Handles representative leaves, non-function evidence, quotient-arrow
--     component equations, and target-inert bridges without term imprecision.
--   * Depends only on type, coercion, permutation, and compatibility
--     infrastructure.

open import Agda.Builtin.Equality using (refl)
open import Coercions using (Coercion; renameᶜ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_,_)
open import ForallPermutation using
  (_∣_⊢_⊑ᵖ_⊣_; quotientᵖ)
open import ImprecisionComposition using (ImprecisionShape)
open import ImprecisionWf using
  (ImpAssm; ImpCtx; _∣_⊢_⊑_⊣_)
open import Types using
  (Renameᵗ; Ty; TyCtx; renameᵗ)
open import proof.Core.Permutation.ForallPermutationProperties using
  (≈∀-renameᵗ; ⊑ᵖ-rename-leftᵢ; ⊑ᵖ-rename²ᵢ)
open import proof.Core.Properties.CoercionProperties using
  (renameᶜ-preserves-Inert; renameᶜ-reflects-Inert)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using
  ( imprecision-composition-shape-transport
  ; rename-assm²-∀-leftᵢ
  ; shape-rename
  ; shape-rename-left
  ; ⊑-rename-leftᵢ
  )
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( quotient-arrow-components-rename-left-at
  ; quotient-arrow-components-rename²-at
  ; source-perm-shape-rename
  )
open import proof.Core.Properties.TypeProperties using
  (TyRenameWf; TyRenameWf-ext)
open import proof.Core.Properties.NuImprecisionIndexedRenamingProperties using
  ( rename-assm²ᵢ
  ; rename-assm²-⇑ᵢ
  ; ⊑-renameᵗ²ᵢ
  )
open import QuotientImprecisionCompatibility using
  ( NonFunctionCoercion
  ; NonPairedFunctionCoercions
  ; QuotientNarrowingEliminationCompatible
  ; ReductionClosedPairedWideningCompatible
  ; ReductionClosedQuotientWideningCompatible
  ; compatible-allᴿ
  ; compatible-functionᴿ
  ; compatible-quotient-functionᴿ
  ; compatible-tagᴿ
  ; compatible-target-activeᴿ
  ; compatible-target-inert-bridgeᴿ
  ; compatible-through-non-function-representativesᴿ
  ; function-elimination
  ; non-function-elimination
  ; non-function-generalize
  ; non-function-id
  ; non-function-instantiate
  ; non-function-seal
  ; non-function-sequence
  ; non-function-tag
  ; non-function-universal
  ; non-function-unseal
  ; non-function-untag
  ; source-non-function
  ; target-non-function
  )


reduction-closed-paired-compatible-rename²ᵢ :
  ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ c c′ A A′ B B′
      p q c-shape c′-shape}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ} →
  (hτ : TyRenameWf Δᴸ Θᴸ τ) →
  (hσ : TyRenameWf Δᴿ Θᴿ σ) →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′}
    p q c-shape c′-shape →
  ReductionClosedPairedWideningCompatible
    Ψ Θᴸ Θᴿ (renameᶜ τ c) (renameᶜ σ c′)
    (⊑-renameᵗ²ᵢ assm hτ hσ p)
    (⊑-renameᵗ²ᵢ assm hτ hσ q)
    c-shape c′-shape
reduction-closed-paired-compatible-rename²ᵢ {τ = τ} hτ hσ
    (compatible-tagᴿ G) =
  compatible-tagᴿ (renameᵗ τ G)
reduction-closed-paired-compatible-rename²ᵢ hτ hσ
    (compatible-functionᴿ compatible) =
  compatible-functionᴿ
    (reduction-closed-paired-compatible-rename²ᵢ hτ hσ compatible)
reduction-closed-paired-compatible-rename²ᵢ
    {assm = assm} hτ hσ (compatible-allᴿ compatible) =
  compatible-allᴿ
    (reduction-closed-paired-compatible-rename²ᵢ
      {assm = rename-assm²-⇑ᵢ assm}
      (TyRenameWf-ext hτ) (TyRenameWf-ext hσ) compatible)
reduction-closed-paired-compatible-rename²ᵢ
    {c′ = c′} hτ hσ
    (compatible-target-activeᴿ inert not-inert′) =
  compatible-target-activeᴿ
    (renameᶜ-preserves-Inert _ inert)
    (λ renamed-inert′ →
      not-inert′ (renameᶜ-reflects-Inert _ c′ renamed-inert′))
reduction-closed-paired-compatible-rename²ᵢ
    {c′ = c′} {assm = assm} hτ hσ
    (compatible-target-inert-bridgeᴿ bridge-evidence) =
  compatible-target-inert-bridgeᴿ λ renamed-inert′ →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence
          (renameᶜ-reflects-Inert _ c′ renamed-inert′)
    in
      ⊑-renameᵗ²ᵢ assm hτ hσ bridge ,
      imprecision-composition-shape-transport
        refl (shape-rename assm hτ hσ bridge)
        (shape-rename assm hτ hσ _) source-triangle ,
      imprecision-composition-shape-transport
        (shape-rename assm hτ hσ bridge) refl
        (shape-rename assm hτ hσ _) target-triangle


reduction-closed-paired-compatible-rename-leftᵢ :
  ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ c c′ A A′ B B′
      p q c-shape c′-shape}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
  (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
  ReductionClosedPairedWideningCompatible
    Φ Δᴸ Δᴿ c c′ {A} {A′} {B} {B′}
    p q c-shape c′-shape →
  ReductionClosedPairedWideningCompatible
    Ψ Δᴸ′ Δᴿ (renameᶜ τ c) c′
    (⊑-rename-leftᵢ τ assm hτ p)
    (⊑-rename-leftᵢ τ assm hτ q)
    c-shape c′-shape
reduction-closed-paired-compatible-rename-leftᵢ
    {τ = τ} hτ (compatible-tagᴿ G) =
  compatible-tagᴿ (renameᵗ τ G)
reduction-closed-paired-compatible-rename-leftᵢ
    hτ (compatible-functionᴿ compatible) =
  compatible-functionᴿ
    (reduction-closed-paired-compatible-rename-leftᵢ hτ compatible)
reduction-closed-paired-compatible-rename-leftᵢ
    {assm = assm} hτ (compatible-allᴿ compatible) =
  compatible-allᴿ
    (reduction-closed-paired-compatible-rename-leftᵢ
      {assm = rename-assm²-∀-leftᵢ assm}
      (TyRenameWf-ext hτ) compatible)
reduction-closed-paired-compatible-rename-leftᵢ
    hτ (compatible-target-activeᴿ inert not-inert′) =
  compatible-target-activeᴿ
    (renameᶜ-preserves-Inert _ inert) not-inert′
reduction-closed-paired-compatible-rename-leftᵢ
    {assm = assm} hτ
    (compatible-target-inert-bridgeᴿ bridge-evidence) =
  compatible-target-inert-bridgeᴿ λ inert′ →
    let
      bridge , source-triangle , target-triangle =
        bridge-evidence inert′
    in
      ⊑-rename-leftᵢ _ assm hτ bridge ,
      imprecision-composition-shape-transport
        refl (shape-rename-left assm hτ bridge)
        (shape-rename-left assm hτ _) source-triangle ,
      imprecision-composition-shape-transport
        (shape-rename-left assm hτ bridge) refl
        (shape-rename-left assm hτ _) target-triangle


non-function-coercion-rename :
  ∀ {c} (τ : Renameᵗ) →
  NonFunctionCoercion c →
  NonFunctionCoercion (renameᶜ τ c)
non-function-coercion-rename τ non-function-id =
  non-function-id
non-function-coercion-rename τ non-function-sequence =
  non-function-sequence
non-function-coercion-rename τ non-function-universal =
  non-function-universal
non-function-coercion-rename τ non-function-tag =
  non-function-tag
non-function-coercion-rename τ non-function-untag =
  non-function-untag
non-function-coercion-rename τ non-function-seal =
  non-function-seal
non-function-coercion-rename τ non-function-unseal =
  non-function-unseal
non-function-coercion-rename τ non-function-generalize =
  non-function-generalize
non-function-coercion-rename τ non-function-instantiate =
  non-function-instantiate


non-paired-function-coercions-rename² :
  ∀ {d d′} (τ σ : Renameᵗ) →
  NonPairedFunctionCoercions d d′ →
  NonPairedFunctionCoercions (renameᶜ τ d) (renameᶜ σ d′)
non-paired-function-coercions-rename² τ σ
    (source-non-function non-function) =
  source-non-function
    (non-function-coercion-rename τ non-function)
non-paired-function-coercions-rename² τ σ
    (target-non-function non-function) =
  target-non-function
    (non-function-coercion-rename σ non-function)


non-paired-function-coercions-rename-left :
  ∀ {d d′} (τ : Renameᵗ) →
  NonPairedFunctionCoercions d d′ →
  NonPairedFunctionCoercions (renameᶜ τ d) d′
non-paired-function-coercions-rename-left τ
    (source-non-function non-function) =
  source-non-function
    (non-function-coercion-rename τ non-function)
non-paired-function-coercions-rename-left τ
    (target-non-function non-function) =
  target-non-function non-function


mutual
  reduction-closed-quotient-compatible-rename²ᵢ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ u u′ D D′ A A′
        q p u-shape u′-shape}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ} →
    (hτ : TyRenameWf Δᴸ Θᴸ τ) →
    (hσ : TyRenameWf Δᴿ Θᴿ σ) →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ {D} {D′} {A} {A′}
      q p u-shape u′-shape →
    ReductionClosedQuotientWideningCompatible
      Ψ Θᴸ Θᴿ (renameᶜ τ u) (renameᶜ σ u′)
      (⊑ᵖ-rename²ᵢ assm hτ hσ q)
      (⊑-renameᵗ²ᵢ assm hτ hσ p)
      u-shape u′-shape
  reduction-closed-quotient-compatible-rename²ᵢ
      {τ = τ} {σ = σ} {assm = assm} hτ hσ
      (compatible-through-non-function-representativesᴿ
        non-function source-shape target-shape compatible) =
    compatible-through-non-function-representativesᴿ
      (non-paired-function-coercions-rename²
        τ σ non-function)
      (source-perm-shape-rename {τ = τ} source-shape)
      (source-perm-shape-rename {τ = σ} target-shape)
      (reduction-closed-paired-compatible-rename²ᵢ
        {assm = assm} hτ hσ compatible)
  reduction-closed-quotient-compatible-rename²ᵢ
      {q = q} {assm = assm} hτ hσ
      (compatible-quotient-functionᴿ
        components domain codomain) =
    compatible-quotient-functionᴿ
      (quotient-arrow-components-rename²-at
        {qF = q} components)
      (quotient-narrowing-elimination-compatible-rename²ᵢ
        {assm = assm} hτ hσ domain)
      (reduction-closed-quotient-compatible-rename²ᵢ
        {assm = assm} hτ hσ codomain)

  quotient-narrowing-elimination-compatible-rename²ᵢ :
    ∀ {Φ Ψ Δᴸ Δᴿ Θᴸ Θᴿ τ σ d d′ A A′ D D′
        p q d-shape d′-shape}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ} →
    (hτ : TyRenameWf Δᴸ Θᴸ τ) →
    (hσ : TyRenameWf Δᴿ Θᴿ σ) →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ {A} {A′} {D} {D′}
      p q d-shape d′-shape →
    QuotientNarrowingEliminationCompatible
      Ψ Θᴸ Θᴿ (renameᶜ τ d) (renameᶜ σ d′)
      (⊑-renameᵗ²ᵢ assm hτ hσ p)
      (⊑ᵖ-rename²ᵢ assm hτ hσ q)
      d-shape d′-shape
  quotient-narrowing-elimination-compatible-rename²ᵢ
      {τ = τ} {σ = σ} hτ hσ
      (non-function-elimination non-function) =
    non-function-elimination
      (non-paired-function-coercions-rename²
        τ σ non-function)
  quotient-narrowing-elimination-compatible-rename²ᵢ
      {q = q} {assm = assm} hτ hσ
      (function-elimination components domain codomain) =
    function-elimination
      (quotient-arrow-components-rename²-at
        {qF = q} components)
      (reduction-closed-quotient-compatible-rename²ᵢ
        {assm = assm} hτ hσ domain)
      (quotient-narrowing-elimination-compatible-rename²ᵢ
        {assm = assm} hτ hσ codomain)


mutual
  reduction-closed-quotient-compatible-rename-leftᵢ :
    ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ u u′ D D′ A A′
        q p u-shape u′-shape}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
    ReductionClosedQuotientWideningCompatible
      Φ Δᴸ Δᴿ u u′ {D} {D′} {A} {A′}
      q p u-shape u′-shape →
    ReductionClosedQuotientWideningCompatible
      Ψ Δᴸ′ Δᴿ (renameᶜ τ u) u′
      (⊑ᵖ-rename-leftᵢ τ assm hτ q)
      (⊑-rename-leftᵢ τ assm hτ p)
      u-shape u′-shape
  reduction-closed-quotient-compatible-rename-leftᵢ
      {τ = τ} {assm = assm} hτ
      (compatible-through-non-function-representativesᴿ
        non-function source-shape target-shape compatible) =
    compatible-through-non-function-representativesᴿ
      (non-paired-function-coercions-rename-left
        τ non-function)
      (source-perm-shape-rename {τ = τ} source-shape)
      target-shape
      (reduction-closed-paired-compatible-rename-leftᵢ
        {assm = assm} hτ compatible)
  reduction-closed-quotient-compatible-rename-leftᵢ
      {q = q} {assm = assm} hτ
      (compatible-quotient-functionᴿ
        components domain codomain) =
    compatible-quotient-functionᴿ
      (quotient-arrow-components-rename-left-at
        {qF = q} components)
      (quotient-narrowing-elimination-compatible-rename-leftᵢ
        {assm = assm} hτ domain)
      (reduction-closed-quotient-compatible-rename-leftᵢ
        {assm = assm} hτ codomain)

  quotient-narrowing-elimination-compatible-rename-leftᵢ :
    ∀ {Φ Ψ Δᴸ Δᴸ′ Δᴿ τ d d′ A A′ D D′
        p q d-shape d′-shape}
      {assm : ∀ {a : ImpAssm} →
        a ∈ Φ → rename-assm²ᵢ τ (λ X → X) a ∈ Ψ} →
    (hτ : TyRenameWf Δᴸ Δᴸ′ τ) →
    QuotientNarrowingEliminationCompatible
      Φ Δᴸ Δᴿ d d′ {A} {A′} {D} {D′}
      p q d-shape d′-shape →
    QuotientNarrowingEliminationCompatible
      Ψ Δᴸ′ Δᴿ (renameᶜ τ d) d′
      (⊑-rename-leftᵢ τ assm hτ p)
      (⊑ᵖ-rename-leftᵢ τ assm hτ q)
      d-shape d′-shape
  quotient-narrowing-elimination-compatible-rename-leftᵢ
      {τ = τ} hτ
      (non-function-elimination non-function) =
    non-function-elimination
      (non-paired-function-coercions-rename-left
        τ non-function)
  quotient-narrowing-elimination-compatible-rename-leftᵢ
      {q = q} {assm = assm} hτ
      (function-elimination components domain codomain) =
    function-elimination
      (quotient-arrow-components-rename-left-at
        {qF = q} components)
      (reduction-closed-quotient-compatible-rename-leftᵢ
        {assm = assm} hτ domain)
      (quotient-narrowing-elimination-compatible-rename-leftᵢ
        {assm = assm} hτ codomain)
