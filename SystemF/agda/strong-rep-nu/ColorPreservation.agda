module strong-rep-nu.ColorPreservation where

-- File Charter:
--   * COLOR PRESERVATION — TWO THEOREMS (Jeremy's ruling, 2026-09-21).
--     Color is about TYPE variables only, so `ColorPreservation`
--     concludes `length (names Δ₂) ≡ length (names Δ₁)`, and it is a
--     COROLLARY of `ScopeMapPreservation`, which pins the whole map:
--     `names Δ₂ ≡ map ρ (names Δ₁)` — same positions, each denoting
--     the same representation variable read through the run's ρ.
--   * A hole's COLOR is its SCOPE MAP, `names Δ` at that hole
--     (strong-rep-nu.Residual §2).  The source is read at Δ and the
--     target at `runCtx rs`, the context the run ENDS at.
--   * Both carry `WfCtx Δ` (spent re-typing the run's middle terms);
--     the `…Closed` forms at `empty` are premise-free beyond the
--     typing.  The proofs are strong-rep-nu.proof.ColorPreservation.
-- Commentary: Commentary.md § ColorPreservation.agda

open import Data.List using ([]; map; length)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-nu.Types using (Ty)
open import strong-rep-nu.Ctx using (Ctxᵗ; names; WfCtx; empty)
open import strong-rep-nu.Terms using (Term; _∣_⊢_⦂_)
open import strong-rep-nu.Reduction using (_⊢_-→*_; runCtx)
open import strong-rep-nu.Residual
open import strong-rep-nu.proof.Ctx using (wf-empty)
import strong-rep-nu.proof.ColorPreservation as Proof

-- THE WELL-FORMEDNESS PREMISE (2026-09-21): the run's intermediate
-- terms are re-typed by `preservation`, which is conditional on
-- `WfCtx Δ`.  Commentary.md § ColorPreservation.agda

ScopeMapPreservation : Set
ScopeMapPreservation = ∀ {Δ : Ctxᵗ} {L L′ : Term} {A : Ty}
  {rs : Δ ⊢ L -→* L′} {C M ρ D N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → Δ ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → names Δ₂ ≡ map ρ (names Δ₁)

scope-map-preservation : ScopeMapPreservation
scope-map-preservation wf ⊢L rs dC dD =
  Proof.residuals-color wf ⊢L rs dC dD

-- The color theorem: a residual position's lexical type-variable scope
-- keeps its size — the v7 reading of `scopeᵗ Δ₁ ≡ scopeᵗ Δ₂`.
ColorPreservation : Set
ColorPreservation = ∀ {Δ : Ctxᵗ} {L L′ : Term} {A : Ty}
  {rs : Δ ⊢ L -→* L′} {C M ρ D N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → Δ ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → length (names Δ₂) ≡ length (names Δ₁)

color-preservation : ColorPreservation
color-preservation wf ⊢L rs dC dD =
  Proof.residuals-color-length wf ⊢L rs dC dD

-- Both, at the empty ambient — the v7-faithful closed forms, premise-
-- free beyond the typing.
ScopeMapPreservationClosed : Set
ScopeMapPreservationClosed = ∀ {L L′ : Term} {A : Ty}
  {rs : empty ⊢ L -→* L′} {C M ρ D N}
  → empty ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → empty ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → names Δ₂ ≡ map ρ (names Δ₁)

scope-map-preservation-closed : ScopeMapPreservationClosed
scope-map-preservation-closed = scope-map-preservation wf-empty

ColorPreservationClosed : Set
ColorPreservationClosed = ∀ {L L′ : Term} {A : Ty}
  {rs : empty ⊢ L -→* L′} {C M ρ D N}
  → empty ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → empty ⊢C C ⊣ Δ₁
  → runCtx rs ⊢C D ⊣ Δ₂
  → length (names Δ₂) ≡ length (names Δ₁)

color-preservation-closed : ColorPreservationClosed
color-preservation-closed = color-preservation wf-empty
