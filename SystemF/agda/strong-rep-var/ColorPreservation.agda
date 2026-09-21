module strong-rep-var.ColorPreservation where

-- COLOR PRESERVATION — the statement (2026-09-21; proof pending Jeremy's
-- review of the statement, per the standing protocol).
--
-- THE DESIGN LAW (Jeremy, 2026-09-04, notes/DECISIONS.md): "the color of a
-- non-boundary term should never change during reduction" — reduction
-- never changes which type variables a subterm can see; only boundary
-- syntax moves.  The v7 theorem (strong-v3-design, commit 31fa0918) said
-- it as `scopeᵗ Δ₁ ≡ scopeᵗ Δ₂` for the contexts at a hole and at its
-- residual.
--
-- THE RESTATEMENT.  A hole's COLOR is its SCOPE MAP, `names Δ` at that
-- hole (strong-rep-var.Residual §2): which ordinary type variables are
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

open import Data.List using ([]; map)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import strong-rep-var.Types using (Ty)
open import strong-rep-var.Ctx using (Ctxᵗ; names)
open import strong-rep-var.Terms using (Term; _∣_⊢_⦂_)
open import strong-rep-var.Reduction using (_⊢_-→*_)
open import strong-rep-var.Residual

ColorPreservation : Set
ColorPreservation = ∀ {Δ : Ctxᵗ} {L L′ : Term} {A : Ty}
  {rs : Δ ⊢ L -→* L′} {C M ρ D N}
  → Δ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → ∀ {Δ₁ Δ₂ : Ctxᵗ}
  → Δ ⊢C C ⊣ Δ₁
  → Δ ⊢C D ⊣ Δ₂
  → names Δ₂ ≡ map ρ (names Δ₁)
