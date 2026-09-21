module strong-rep-store.ColorPreservation where

-- COLOR PRESERVATION — the theorem and the stronger scope-map form it
-- is a corollary of (statement approved by Jeremy and proved
-- 2026-09-21; the proof is strong-rep-store.proof.ColorPreservation).
--
-- TWO THEOREMS (Jeremy's ruling, 2026-09-21).  Color is about TYPE
-- variables only — which ordinary names are live at a hole — not about
-- the representation variables they denote.  So the COLOR THEOREM
-- proper, `ColorPreservation`, concludes
-- `length (names Δ₂) ≡ length (names Δ₁)`, and it is a corollary of
-- the stronger `ScopeMapPreservation`, which pins the whole scope map:
-- `names Δ₂ ≡ map ρ (names Δ₁)` — same positions, each denoting the
-- same representation variable read through the run's renaming ρ.
--
-- THE DESIGN LAW (Jeremy, 2026-09-04, notes/DECISIONS.md): "the color of a
-- non-boundary term should never change during reduction" — reduction
-- never changes which type variables a subterm can see; only boundary
-- syntax moves.  The v7 theorem (strong-v3-design, commit 31fa0918) said
-- it as `scopeᵗ Δ₁ ≡ scopeᵗ Δ₂` for the contexts at a hole and at its
-- residual.
--
-- THE RESTATEMENT.  A hole's COLOR is its SCOPE MAP, `names Δ` at that
-- hole (strong-rep-store.Residual §2): which ordinary type variables are
-- live there and which representation variable each denotes.  A move
-- can rename the representation universe — `Peel` sends its argument
-- past a bind block, `Beta` sends a copy past a `Λ`'s dual — so the
-- scope map is transported along the representation renaming `ρ` the
-- run delivered to the hole, which `Residuals` records.  Everything
-- else is EQUAL: no ordinary position is added, removed or moved, and a
-- name denotes the same representation variable, read through `ρ`.
-- `TyBeta`/`TyPeelR-Λ`'s refinement of an `abstR` slot to `bindR R`
-- changes what a representation variable IS BOUND TO, not which one a
-- name denotes, so it is invisible to the scope map (and `ρ` is `idᵗ`).
--
-- In the named presentation (notes/notes.md): a residual position sees
-- exactly the type variables X it saw before, each standing for the same
-- α — up to the α-renaming of the representation universe that the
-- crossed binders impose.

open import Data.List using ([]; map; length)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-store.Types using (Ty)
open import strong-rep-store.Ctx using (Ctxᵗ; names; WfCtx; empty)
open import strong-rep-store.Terms using (Term; _∣_⊢_⦂_)
open import strong-rep-store.Reduction using (_⊢_-→*_)
open import strong-rep-store.Residual
open import strong-rep-store.proof.Ctx using (wf-empty)
import strong-rep-store.proof.ColorPreservation as Proof

-- THE WELL-FORMEDNESS PREMISE (2026-09-21, added with the proof; the
-- one delta against the reviewed statement).  The run's intermediate
-- terms are re-typed by `preservation`, which is conditional on
-- `WfCtx Δ` — so a run under an arbitrary ambient Δ inherits that
-- premise.  It is the price of decision 5 (stating over any Δ rather
-- than `empty`); `ColorPreservationClosed` below is the v7-faithful
-- closed form, premise-free beyond the typing.

ScopeMapPreservation : Set
ScopeMapPreservation = ∀ {Δ : Ctxᵗ} {L L′ : Term} {A : Ty}
  {rs : Δ ⊢ L -→* L′} {C M ρ D N}
  → WfCtx Δ
  → Δ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → Δ ⊢C C ⊣ Δ₁
  → Δ ⊢C D ⊣ Δ₂
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
  → Δ ⊢C D ⊣ Δ₂
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
  → empty ⊢C D ⊣ Δ₂
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
  → empty ⊢C D ⊣ Δ₂
  → length (names Δ₂) ≡ length (names Δ₁)

color-preservation-closed : ColorPreservationClosed
color-preservation-closed = color-preservation wf-empty
