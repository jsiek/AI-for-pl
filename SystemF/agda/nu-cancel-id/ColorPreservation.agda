module nu-cancel-id.ColorPreservation where

-- File Charter:
--   * COLOR PRESERVATION of νF₁ᶜ, as two theorems, after
--     strong-rep-nu.ColorPreservation.  A hole's COLOR is its SCOPE
--     MAP, `names` of the flags at the hole (nu-cancel-id.Residual §2):
--     the named cells, newest first, so name X denotes the X-th.
--   * `scope-map-preservation`: through a run, a residual's scope map
--     is the original one with ρ applied to each entry: the same names,
--     each denoting the same cell.  ρ only re-indexes cells, which are
--     de Bruijn indices: an allocation puts an unnamed cell below its
--     siblings' cells, and a copy under a `Λ` sits below that `Λ`'s
--     cell, which the copy's hide unnames.  `color-preservation`, its
--     corollary: the number of names in scope is unchanged.
--   * The source is read at Γ and the target at Γ′, the context the run
--     ends at.  Residuals are positions of the contractum
--     (`residuals-sound`).  The proofs are
--     nu-cancel-id.proof.ColorPreservation and nu-cancel-id.proof.Residual.

open import Data.List using ([]; map; length)
open import Data.List.Properties using (length-map)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)

open import nu-cancel-id.Types using (Ty; Renameᵗ)
open import nu-cancel-id.Ctx using (Ctx; flags)
open import nu-cancel-id.Terms using (Term; _∣_⊢_⦂_)
open import nu-cancel-id.Reduction using (_⊢_—↠_⊣_)
open import nu-cancel-id.Residual
  using (TermCtx; plug; Residuals; holeFlags; names)
import nu-cancel-id.proof.ColorPreservation as P
import nu-cancel-id.proof.Residual as R

residuals-sound : ∀ {Γ Γ′ : Ctx} {L L′ : Term}
  {rs : Γ ⊢ L —↠ L′ ⊣ Γ′} {C : TermCtx} {M : Term} {ρ : Renameᵗ}
  {D : TermCtx} {N : Term}
  → Residuals rs C M ρ D N
  → L ≡ plug C M × L′ ≡ plug D N
residuals-sound = R.residuals-sound

scope-map-preservation : ∀ {Γ Γ′ : Ctx} {L L′ : Term} {A : Ty}
  {rs : Γ ⊢ L —↠ L′ ⊣ Γ′} {C : TermCtx} {M : Term} {ρ : Renameᵗ}
  {D : TermCtx} {N : Term}
  → Γ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → names (holeFlags (flags Γ′) D)
    ≡ map ρ (names (holeFlags (flags Γ) C))
scope-map-preservation = P.color*

color-preservation : ∀ {Γ Γ′ : Ctx} {L L′ : Term} {A : Ty}
  {rs : Γ ⊢ L —↠ L′ ⊣ Γ′} {C : TermCtx} {M : Term} {ρ : Renameᵗ}
  {D : TermCtx} {N : Term}
  → Γ ∣ [] ⊢ L ⦂ A
  → Residuals rs C M ρ D N
  → length (names (holeFlags (flags Γ′) D))
    ≡ length (names (holeFlags (flags Γ) C))
color-preservation {Γ = Γ} {C = C} {ρ = ρ} ⊢L rs =
  trans (cong length (P.color* ⊢L rs))
        (length-map ρ (names (holeFlags (flags Γ) C)))
