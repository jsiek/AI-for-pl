{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxScopedTermClosureProbe where

-- File Charter:
--   * Closes the scoped two-Ctx world under arbitrary repeated term binding
--     while endpoint type/store indices remain fixed.
--   * Defines here/there/tail entry transport by recursion on that same full
--     endpoint relation and derives variable CTI at arbitrary depth.
--   * Leaves universal/type-context lifting outside this fixed-index slice.

open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (_∷_)

open import Types using (Ty; TyVar; ＇_)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open import CastTerms using (Ctx; ⟨_,_,_⟩; Term; `_; _∋ᵗ_⦂_)
open import proof.DGG.TwoCtxWorld
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxAliasFocusModeProbe
open import proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe using
  (boundary-world)


module ScopedTermClosure
    {Cᴸ : Ctx} {Δᴿ} {Σᴿ : TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar (CastTerms.Δᵉ Cᴸ)} {alpha : TyVar Δᴿ}
    (focus : TargetNameFocusᶠ₀ W X alpha)
    {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    (scope : TargetAliasBoundaryᶠ₀ focus
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    (W⁺ : Cᴸ ⊑ᶜ
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    where

  module Mode = AliasFocusModeᶠ₁ focus scope
  open Mode

  data ScopedWorldᶜ (m : TargetModeᶠ₁) : Ctx → Ctx → Set where
    scoped-root :
      ValidTargetModeᶠ₁ m →
      ScopedWorldᶜ m Cᴸ
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩

    scoped-bind : ∀ {Γᴸ′ Γᴿ′}
        {A : Ty (CastTerms.Δᵉ Cᴸ)} {B : Ty (suc Δᴿ)}
      → ScopedWorldᶜ m
          ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩
      → ScopedTypeImprecisionᶠ₁ m A B
      → ScopedWorldᶜ m
          ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , A ∷ Γᴸ′ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , B ∷ Γᴿ′ ⟩

  data ScopedEntryᶜ {m} : ∀ {Γᴸ′ Γᴿ′}
      (S : ScopedWorldᶜ m
        ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩) →
      (x : ℕ) → {A : Ty (CastTerms.Δᵉ Cᴸ)}
      {B : Ty (suc Δᴿ)} →
      ScopedTypeImprecisionᶠ₁ m A B → Set where
    entry-here : ∀ {Γᴸ′ Γᴿ′ A B}
        {S : ScopedWorldᶜ m
          ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩}
        {p : ScopedTypeImprecisionᶠ₁ m A B}
      → ScopedEntryᶜ (scoped-bind S p) zero p

    entry-there : ∀ {Γᴸ′ Γᴿ′ A B x A₀ B₀}
        {S : ScopedWorldᶜ m
          ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
          ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩}
        {p : ScopedTypeImprecisionᶠ₁ m A B}
        {p₀ : ScopedTypeImprecisionᶠ₁ m A₀ B₀}
      → ScopedEntryᶜ S x p
      → ScopedEntryᶜ (scoped-bind S p₀) (suc x) p

  entry-tail : ∀ {m Γᴸ′ Γᴿ′ A B x A₀ B₀}
      {S : ScopedWorldᶜ m
        ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩}
      {p : ScopedTypeImprecisionᶠ₁ m A B}
      {p₀ : ScopedTypeImprecisionᶠ₁ m A₀ B₀}
    → ScopedEntryᶜ (scoped-bind S p₀) (suc x) p
    → ScopedEntryᶜ S x p
  entry-tail (entry-there entry) = entry

  entry-source-lookup : ∀ {m Γᴸ′ Γᴿ′ x A B}
      {S : ScopedWorldᶜ m
        ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩}
      {p : ScopedTypeImprecisionᶠ₁ m A B}
    → ScopedEntryᶜ S x p
    → TC._∋_⦂_ Γᴸ′ x A
  entry-source-lookup entry-here = TC.Z
  entry-source-lookup (entry-there entry) =
    TC.S (entry-source-lookup entry)

  entry-target-lookup : ∀ {m Γᴸ′ Γᴿ′ x A B}
      {S : ScopedWorldᶜ m
        ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩}
      {p : ScopedTypeImprecisionᶠ₁ m A B}
    → ScopedEntryᶜ S x p
    → TC._∋_⦂_ Γᴿ′ x B
  entry-target-lookup entry-here = TC.Z
  entry-target-lookup (entry-there entry) =
    TC.S (entry-target-lookup entry)

  data VariableCTIᶜ {m Γᴸ′ Γᴿ′}
      (S : ScopedWorldᶜ m
        ⟨ CastTerms.Δᵉ Cᴸ , CastTerms.Σᵉ Cᴸ , Γᴸ′ ⟩
        ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ′ ⟩) :
      Term (CastTerms.Δᵉ Cᴸ) → Term (suc Δᴿ) → Set where
    var⊑var : ∀ {x A B} {p : ScopedTypeImprecisionᶠ₁ m A B}
      → ScopedEntryᶜ S x p
      → VariableCTIᶜ S (` x) (` x)


module LambdaClosure = ScopedTermClosure
  strict-lambda-focus strict-lambda-boundary boundary-world

open LambdaClosure
open LambdaClosure.Mode

depth-one = scoped-bind (scoped-root beta-validᶠ₁) beta-X-betaᶠ₁
depth-two = scoped-bind depth-one beta-X-betaᶠ₁

depth-two-here : ScopedEntryᶜ depth-two zero beta-X-betaᶠ₁
depth-two-here = entry-here

depth-two-there : ScopedEntryᶜ depth-two (suc zero) beta-X-betaᶠ₁
depth-two-there = entry-there entry-here

depth-one-again : ScopedEntryᶜ depth-one zero beta-X-betaᶠ₁
depth-one-again = entry-tail depth-two-there

depth-two-variable : VariableCTIᶜ depth-two (` (suc zero)) (` (suc zero))
depth-two-variable = var⊑var depth-two-there
