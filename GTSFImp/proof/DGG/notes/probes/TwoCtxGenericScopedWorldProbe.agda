{-# OPTIONS --safe #-}

module proof.DGG.notes.probes.TwoCtxGenericScopedWorldProbe where

-- File Charter:
--   * Couples alias-focus modes, scoped type precision, and full-Ctx term
--     binding over an arbitrary stable two-Ctx world and exact right bind.
--   * Keeps the ordinary boundary world as provenance and adds no parallel
--     context-imprecision witness.
--   * Instantiates the generic variable leaf for beta := alpha, alpha := star.

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; suc; zero)
import Data.Fin as Fin

open import Types using (Ty; TyVar; ＇_)
open import TyStore using (TyStore; store-bind)
import TermCtx as TC
open import TermCtx using (Z)
open import CastTerms using
  (Ctx; ⟨_,_,_⟩; Δᵉ; Term; `_; _,ᶜ_; _∋ᵗ_⦂_)
open import proof.DGG.TwoCtxWorld
open import
  proof.DGG.notes.probes.TwoCtxAdministrativeAliasFocusProbe
open import proof.DGG.notes.probes.TwoCtxAliasFocusModeProbe
open import proof.DGG.notes.probes.TwoCtxScopedTermBoundaryProbe using
  (boundary-world; source-body-context; target-body-context)


module GenericScopedWorld
    {Cᴸ : Ctx} {Δᴿ} {Σᴿ : TyStore Δᴿ} {Γᴿ : TC.TermCtx Δᴿ}
    {W : Cᴸ ⊑ᶜ ⟨ Δᴿ , Σᴿ , Γᴿ ⟩}
    {X : TyVar (Δᵉ Cᴸ)} {alpha : TyVar Δᴿ}
    (focus : TargetNameFocusᶠ₀ W X alpha)
    {Γᴿ⁺ : TC.TermCtx (suc Δᴿ)}
    (scope : TargetAliasBoundaryᶠ₀ focus
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    (W⁺ : Cᴸ ⊑ᶜ
      ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩)
    where

  module Mode = AliasFocusModeᶠ₁ focus scope
  open Mode

  BoundaryCtx : Ctx
  BoundaryCtx =
    ⟨ suc Δᴿ , store-bind Σᴿ (＇ alpha) , Γᴿ⁺ ⟩

  data ScopedWorldᶜ (m : TargetModeᶠ₁) : Ctx → Ctx → Set where
    scoped-focus :
      ValidTargetModeᶠ₁ m → ScopedWorldᶜ m Cᴸ BoundaryCtx

    scoped-bind-term : ∀
        {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ BoundaryCtx)}
      → ScopedWorldᶜ m Cᴸ BoundaryCtx
      → ScopedTypeImprecisionᶠ₁ m A B
      → ScopedWorldᶜ m (Cᴸ ,ᶜ A) (BoundaryCtx ,ᶜ B)

  stable-scoped-world : ScopedWorldᶜ stable-modeᶠ₁ Cᴸ BoundaryCtx
  stable-scoped-world = scoped-focus stable-validᶠ₁

  push-scoped-world : ∀ {m Y R q}
    → (ok : ValidTargetModeᶠ₁ m)
    → (edge : ExactTargetBoundaryᶠ₁ m Y R q)
    → ScopedWorldᶜ (push-focusᶠ₁ m Y) Cᴸ BoundaryCtx
  push-scoped-world ok edge = scoped-focus (push-validᶠ₁ ok edge)

  data ScopedTermEntryᶜ {m}
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ BoundaryCtx)}
      (p : ScopedTypeImprecisionᶠ₁ m A B)
      (S : ScopedWorldᶜ m (Cᴸ ,ᶜ A) (BoundaryCtx ,ᶜ B)) : Set where
    scoped-entry : ScopedTermEntryᶜ p S

  scoped-entry-here : ∀ {m}
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ BoundaryCtx)}
      {ok : ValidTargetModeᶠ₁ m}
      (p : ScopedTypeImprecisionᶠ₁ m A B)
    → ScopedTermEntryᶜ p
        (scoped-bind-term (scoped-focus ok) p)
  scoped-entry-here p = scoped-entry

  data VariableCTIᶜ {m}
      {A : Ty (Δᵉ Cᴸ)} {B : Ty (Δᵉ BoundaryCtx)}
      {p : ScopedTypeImprecisionᶠ₁ m A B}
      (S : ScopedWorldᶜ m (Cᴸ ,ᶜ A) (BoundaryCtx ,ᶜ B)) :
      Term (Δᵉ Cᴸ) → Term (Δᵉ BoundaryCtx) → Set where
    var⊑varᶜ : ScopedTermEntryᶜ p S
      → VariableCTIᶜ S (` zero) (` zero)

  stable-pending-unavailable : ∀ {Z}
    → TargetVarViewᶠ₁ stable-modeᶠ₁ Fin.zero Z
    → ⊥
  stable-pending-unavailable = stable-new-unavailableᶠ₁


module LambdaScoped = GenericScopedWorld
  strict-lambda-focus strict-lambda-boundary boundary-world

open LambdaScoped
open LambdaScoped.Mode

lambda-beta-body-world : ScopedWorldᶜ beta-modeᶠ₁
  source-body-context target-body-context
lambda-beta-body-world =
  scoped-bind-term (scoped-focus beta-validᶠ₁) beta-X-betaᶠ₁

lambda-beta-entry :
  ScopedTermEntryᶜ beta-X-betaᶠ₁ lambda-beta-body-world
lambda-beta-entry = scoped-entry-here beta-X-betaᶠ₁

lambda-beta-variable :
  VariableCTIᶜ lambda-beta-body-world (` zero) (` zero)
lambda-beta-variable = var⊑varᶜ lambda-beta-entry
