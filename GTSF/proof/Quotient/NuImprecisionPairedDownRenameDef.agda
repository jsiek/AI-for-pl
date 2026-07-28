module proof.Quotient.NuImprecisionPairedDownRenameDef where

-- File Charter:
--   * Defines the complete two-sided and source-only type-renaming contracts
--     for one paired quotient-narrowing term-imprecision constructor.
--   * Takes already-transported cast modes and narrowing derivations, leaving
--     world/store-specific transport to the canonical Lemma adapter.
--   * Depends only on the live QTI grammar and its type-index, shape, and
--     quotient-elimination invariants.

open import CastImprecisionShape using (_⊢ᶜ_⦂_)
import CastImprecisionShape as CastShape using (narrowing)
open import Coercions using (Coercion; renameᶜ)
open import Data.List.Membership.Propositional using (_∈_)
open import ForallPermutation using (_∣_⊢_⊑ᵖ_⊣_)
open import ImprecisionComposition using (_；⌊_⌋≋ᵖ_；_)
open import ImprecisionWf using
  (ImpAssm; ImpCtx; _∣_⊢_⊑_⊣_)
open import NarrowWiden using (_∣_∣_⊢_∶_⊒_)
open import NuTerms using (Term; renameᵗᵐ; _⟨_⟩)
open import proof.NuCore.Relations.NuImprecisionTermContextDef using
  (CtxImp)
open import proof.Store.Core.NuImprecisionRelationalStoreDef using
  (StoreImp; leftStoreⁱ; rightStoreⁱ)
open import QuotientImprecisionCompatibility using
  (QuotientNarrowingEliminationCompatible; SpineCastMode)
open import QuotientedTermImprecision using
  ( _∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_
  ; _∣_∣_∣_∣_⊢ᴺᵖ_⊑_⦂_⊑ᵖ_∶_
  )
open import TermTyping using (CastMode)
open import Types using (Renameᵗ; Ty; TyCtx; renameᵗ)
open import
  proof.Core.Permutation.ForallPermutationProperties
  using (⊑ᵖ-rename-leftᵢ; ⊑ᵖ-rename²ᵢ)
open import proof.Core.Properties.NuCastImprecisionShapeProperties using
  (⊑-rename-leftᵢ)
open import proof.Core.Properties.TypeProperties using (TyRenameWf)
open import proof.EndpointMLB.Core.MaximalLowerBoundsWf using
  (rename-assm²ᵢ; ⊑-renameᵗ²ᵢ)
PairedDownRename²ᵀ : Set₁
PairedDownRename²ᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴿ Θᴸ Θᴿ : TyCtx}
    {τ σ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ σ a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Θᴸ τ}
    {hσ : TyRenameWf Δᴿ Θᴿ σ}
    {ρ′ : StoreImp Ψ Θᴸ Θᴿ}
    {γ′ : CtxImp Ψ Θᴸ Θᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {d d′ : Coercion} {s s′} {μ μ′} →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ renameᵗᵐ σ M′
    ⦂ renameᵗ τ C ⊑ renameᵗ σ C′
    ∶ ⊑-renameᵗ²ᵢ assm hτ hσ pC →
  SpineCastMode (leftStoreⁱ ρ′) μ →
  μ ∣ Θᴸ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ d ∶ renameᵗ τ C ⊒ renameᵗ τ D →
  CastShape.narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρ′) μ′ →
  μ′ ∣ Θᴿ ∣ rightStoreⁱ ρ′
    ⊢ renameᶜ σ d′ ∶ renameᵗ σ C′ ⊒ renameᵗ σ D′ →
  CastShape.narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  Ψ ∣ Θᴸ ∣ Θᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩)
      ⊑ renameᵗᵐ σ (M′ ⟨ d′ ⟩)
    ⦂ renameᵗ τ D ⊑ᵖ renameᵗ σ D′
    ∶ ⊑ᵖ-rename²ᵢ assm hτ hσ qD


PairedDownRenameLeftᵀ : Set₁
PairedDownRenameLeftᵀ =
  ∀ {Φ Ψ : ImpCtx} {Δᴸ Δᴸ′ Δᴿ : TyCtx}
    {τ : Renameᵗ}
    {assm : ∀ {a : ImpAssm} →
      a ∈ Φ → rename-assm²ᵢ τ (λ X → X) a ∈ Ψ}
    {hτ : TyRenameWf Δᴸ Δᴸ′ τ}
    {ρ′ : StoreImp Ψ Δᴸ′ Δᴿ}
    {γ′ : CtxImp Ψ Δᴸ′ Δᴿ}
    {M M′ : Term} {C C′ D D′ : Ty}
    {pC : Φ ∣ Δᴸ ⊢ C ⊑ C′ ⊣ Δᴿ}
    {qD : Φ ∣ Δᴸ ⊢ D ⊑ᵖ D′ ⊣ Δᴿ}
    {d d′ : Coercion} {s s′} {μ μ′} →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺ renameᵗᵐ τ M ⊑ M′
    ⦂ renameᵗ τ C ⊑ C′ ∶ ⊑-rename-leftᵢ τ assm hτ pC →
  SpineCastMode (leftStoreⁱ ρ′) μ →
  μ ∣ Δᴸ′ ∣ leftStoreⁱ ρ′
    ⊢ renameᶜ τ d ∶ renameᵗ τ C ⊒ renameᵗ τ D →
  CastShape.narrowing ⊢ᶜ d ⦂ s →
  SpineCastMode (rightStoreⁱ ρ′) μ′ →
  μ′ ∣ Δᴿ ∣ rightStoreⁱ ρ′ ⊢ d′ ∶ C′ ⊒ D′ →
  CastShape.narrowing ⊢ᶜ d′ ⦂ s′ →
  s ；⌊ pC ⌋≋ᵖ qD ； s′ →
  QuotientNarrowingEliminationCompatible
    Φ Δᴸ Δᴿ d d′ pC qD s s′ →
  Ψ ∣ Δᴸ′ ∣ Δᴿ ∣ ρ′ ∣ γ′
    ⊢ᴺᵖ renameᵗᵐ τ (M ⟨ d ⟩) ⊑ M′ ⟨ d′ ⟩
    ⦂ renameᵗ τ D ⊑ᵖ D′ ∶ ⊑ᵖ-rename-leftᵢ τ assm hτ qD
