module proof.Quotient.NuImprecisionPairedDownRenameProof where

-- File Charter:
--   * Proves the generic two-sided and source-only paired quotient-narrowing
--     renaming contracts.
--   * Renames only the type-index square, cast shapes, and recursive
--     elimination compatibility after cast/store transport has been supplied.
--   * Imports no simulation implementation or world/store renaming record.

open import QuotientedTermImprecision using (paired-downᵀ)
open import
  proof.Core.Properties.NuCastImprecisionShapeProperties
  using (cast-shape-rename)
open import
  proof.Core.Properties.NuImprecisionQuotientBoundaryProperties
  using
  ( quotient-boundary-square-rename-left
  ; quotient-boundary-square-rename²
  )
open import
  proof.Quotient.NuImprecisionPairedDownRenameDef
  using (PairedDownRenameLeftᵀ; PairedDownRename²ᵀ)
open import
  proof.Quotient.NuImprecisionQuotientNarrowingEliminationCompatibilityRename
  using
  ( quotient-narrowing-elimination-compatible-rename-leftᵢ
  ; quotient-narrowing-elimination-compatible-rename²ᵢ
  )


paired-down-rename²ᵀ : PairedDownRename²ᵀ
paired-down-rename²ᵀ
    {τ = τ} {σ = σ} {assm = assm} {hτ = hτ} {hσ = hσ}
    M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square compatible =
  paired-downᵀ M⊑M′ mode d⊒
    (cast-shape-rename τ d-shape)
    mode′ d′⊒
    (cast-shape-rename σ d′-shape)
    (quotient-boundary-square-rename²
      {τ = τ} {σ = σ} {assm = assm}
      {hτ = hτ} {hσ = hσ} square)
    (quotient-narrowing-elimination-compatible-rename²ᵢ
      {assm = assm} hτ hσ compatible)


paired-down-rename-leftᵀ : PairedDownRenameLeftᵀ
paired-down-rename-leftᵀ
    {τ = τ} {assm = assm} {hτ = hτ}
    M⊑M′ mode d⊒ d-shape mode′ d′⊒ d′-shape square compatible =
  paired-downᵀ M⊑M′ mode d⊒
    (cast-shape-rename τ d-shape)
    mode′ d′⊒ d′-shape
    (quotient-boundary-square-rename-left
      {τ = τ} {assm = assm} {hτ = hτ} square)
    (quotient-narrowing-elimination-compatible-rename-leftᵢ
      {assm = assm} hτ compatible)
