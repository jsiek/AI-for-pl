{-# OPTIONS --safe #-}

module proof.DGG.TargetAliasEdge where

-- File Charter:
--   * Defines the exact one-step target allocation used by an
--     administrative alias boundary.
--   * Records the fresh target name beta, its direct referent alpha, and the
--     shifted endpoint name alpha-plus without following store aliases.
--   * Supports structural lifting beneath type binders and exposes the
--     old-name embedding, referent, freshness, injectivity, and direct-entry
--     laws needed by a boundary-indexed term relation.
--   * Depends only on the trusted target context and store definitions; mode,
--     focus, term imprecision, and concrete fixtures live elsewhere.

open import Data.Fin using (zero; suc)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; cong)

open import Types using (TyVar; ＇_)
open import TyStore using
  (TyStore; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋)
import TermCtx as TC
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Σᵉ; ⇑ᵉᵗ)


private
  fin-suc-injective : ∀ {n} {X Y : TyVar n}
    → suc X ≡ suc Y
    → X ≡ Y
  fin-suc-injective refl = refl


data ExactAliasEdge :
    (C C⁺ : Ctx) → TyVar (Δᵉ C) → TyVar (Δᵉ C⁺)
    → TyVar (Δᵉ C⁺) → Set where

  edge-head : ∀ {Δ} {Σ : TyStore Δ} {Γ : TC.TermCtx Δ}
      {Γ⁺ : TC.TermCtx (Nat.suc Δ)} {alpha : TyVar Δ}
    → Γ⁺ ≡ TC.⇑ᶜ Γ
    → ExactAliasEdge
        ⟨ Δ , Σ , Γ ⟩
        ⟨ Nat.suc Δ , store-bind Σ (＇ alpha) , Γ⁺ ⟩
        alpha zero (suc alpha)

  edge-lift-raw :
      ∀ {Δ Δ⁺} {Σ : TyStore Δ} {Σ⁺ : TyStore Δ⁺}
        {Γ : TC.TermCtx Δ} {Γ⁺ : TC.TermCtx Δ⁺}
        {Γ₁ : TC.TermCtx (Nat.suc Δ)}
        {Γ₂ : TC.TermCtx (Nat.suc Δ⁺)}
        {alpha : TyVar Δ} {beta alpha⁺ : TyVar Δ⁺}
    → ExactAliasEdge
        ⟨ Δ , Σ , Γ ⟩ ⟨ Δ⁺ , Σ⁺ , Γ⁺ ⟩ alpha beta alpha⁺
    → Γ₁ ≡ TC.⇑ᶜ Γ
    → Γ₂ ≡ TC.⇑ᶜ Γ⁺
    → ExactAliasEdge
        ⟨ Nat.suc Δ , store-lift Σ , Γ₁ ⟩
        ⟨ Nat.suc Δ⁺ , store-lift Σ⁺ , Γ₂ ⟩
        (suc alpha) (suc beta) (suc alpha⁺)


liftAliasEdge : ∀ {C C⁺ alpha beta alpha⁺}
  → ExactAliasEdge C C⁺ alpha beta alpha⁺
  → ExactAliasEdge (⇑ᵉᵗ C) (⇑ᵉᵗ C⁺)
      (suc alpha) (suc beta) (suc alpha⁺)
liftAliasEdge edge = edge-lift-raw edge refl refl


edgeEmbed : ∀ {C C⁺ alpha beta alpha⁺}
  → ExactAliasEdge C C⁺ alpha beta alpha⁺
  → TyVar (Δᵉ C) → TyVar (Δᵉ C⁺)
edgeEmbed (edge-head Γ⁺≡) Y = suc Y
edgeEmbed (edge-lift-raw edge Γ₁≡ Γ₂≡) zero = zero
edgeEmbed (edge-lift-raw edge Γ₁≡ Γ₂≡) (suc Y) =
  suc (edgeEmbed edge Y)


edge-alpha : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
  → edgeEmbed edge alpha ≡ alpha⁺
edge-alpha (edge-head Γ⁺≡) = refl
edge-alpha (edge-lift-raw edge Γ₁≡ Γ₂≡) =
  cong suc (edge-alpha edge)


edge-beta-fresh : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺) Y
  → edgeEmbed edge Y ≢ beta
edge-beta-fresh (edge-head Γ⁺≡) Y ()
edge-beta-fresh (edge-lift-raw edge Γ₁≡ Γ₂≡) zero ()
edge-beta-fresh (edge-lift-raw edge Γ₁≡ Γ₂≡) (suc Y) eq =
  edge-beta-fresh edge Y (fin-suc-injective eq)


edgeEmbed-injective : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺) {Y Z}
  → edgeEmbed edge Y ≡ edgeEmbed edge Z
  → Y ≡ Z
edgeEmbed-injective (edge-head Γ⁺≡) eq = fin-suc-injective eq
edgeEmbed-injective (edge-lift-raw edge Γ₁≡ Γ₂≡)
    {zero} {zero} refl = refl
edgeEmbed-injective (edge-lift-raw edge Γ₁≡ Γ₂≡)
    {zero} {suc Z} ()
edgeEmbed-injective (edge-lift-raw edge Γ₁≡ Γ₂≡)
    {suc Y} {zero} ()
edgeEmbed-injective (edge-lift-raw edge Γ₁≡ Γ₂≡)
    {suc Y} {suc Z} eq =
  cong suc (edgeEmbed-injective edge (fin-suc-injective eq))


edge-beta-entry : ∀ {C C⁺ alpha beta alpha⁺}
    (edge : ExactAliasEdge C C⁺ alpha beta alpha⁺)
  → Σᵉ C⁺ ∋ beta ⦂ ＇ alpha⁺
edge-beta-entry (edge-head Γ⁺≡) = Z∋ refl
edge-beta-entry (edge-lift-raw edge Γ₁≡ Γ₂≡) =
  S-lift∋ (edge-beta-entry edge) refl
