module
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibilityRename
  where

-- File Charter:
--   * Preserves recursive quotient-narrowing elimination compatibility under
--     two-sided and source-only type renaming.
--   * Renames non-function coercion evidence and quotient-arrow component
--     equations, then recurses through function codomains.
--   * Reuses the separately stable quotient-widening compatibility transport
--     for each contravariant function-domain obligation.

open import Coercions using (renameᶜ)
open import Data.List.Membership.Propositional using (_∈_)
open import ImprecisionWf using (ImpAssm)
open import Types using (Renameᵗ)
open import
  proof.Core.Permutation.ForallPermutationProperties
  using (⊑ᵖ-rename-leftᵢ; ⊑ᵖ-rename²ᵢ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (⊑-rename-leftᵢ)
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( quotient-arrow-components-rename-left-at
  ; quotient-arrow-components-rename²-at
  )
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibility
  using
  ( NonFunctionCoercion
  ; NonPairedFunctionCoercions
  ; QuotientNarrowingEliminationCompatible
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
open import
  proof.Quotient.NuImprecisionQuotientWideningCompatibilityRename
  using
  ( reduction-closed-quotient-compatible-rename-leftᵢ
  ; reduction-closed-quotient-compatible-rename²ᵢ
  )


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
    (function-elimination components compatible elimination) =
  function-elimination
    (quotient-arrow-components-rename²-at
      {qF = q} components)
    (reduction-closed-quotient-compatible-rename²ᵢ
      {assm = assm} hτ hσ compatible)
    (quotient-narrowing-elimination-compatible-rename²ᵢ
      {assm = assm} hτ hσ elimination)


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
    (function-elimination components compatible elimination) =
  function-elimination
    (quotient-arrow-components-rename-left-at
      {qF = q} components)
    (reduction-closed-quotient-compatible-rename-leftᵢ
      {assm = assm} hτ compatible)
    (quotient-narrowing-elimination-compatible-rename-leftᵢ
      {assm = assm} hτ elimination)
