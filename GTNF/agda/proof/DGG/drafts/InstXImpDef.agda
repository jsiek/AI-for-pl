module proof.DGG.drafts.InstXImpDef where

-- File Charter:
--   * DRAFT STATEMENTS (2026-10-03), NOT APPROVED: `inst_X` preserves
--     `⊑` (PLAN.md §3 `InstX⊑`).  For review (drafts/STATEMENTS.md).
--   * THE ABSTRACT READING.  `InstX V N` reads N under `underΛ Δ` (the
--     left value's abstract rep. var at 0, TermImprecision's charter),
--     so the conclusions are stated at the worlds of the `Λ` rules:
--     `W ⊕²` (both sides opened, as `Λ⊑Λ`'s premise) and `W ⊕ᴸ` (the
--     left alone, as `Λ⊑`'s premise).  The TyBeta consumers then move
--     the result to the REPRESENTED interior of `inst []` (bindR R at 0,
--     the pair (0,0) global): that refinement is a separate transport
--     (STATEMENTS.md, "not in the tree").
--   * DESIGN.MD D28 (2026-10-05) supersedes D11: marks are derived, so
--     no mark is chosen.  The opened name of `W ⊕²` is X⊑X (its new
--     right rep. var is not permitted).  Before D28, `InstXImp2` chose
--     the mark (`∃ m`, a `Λ`-vs-`gen` pair needed X⊑★) and
--     `InstXImpOpenR` concluded at `W ⊕ X⊑★`.  Under D28 an X⊑★ at a
--     joined name needs a grant above (PermissionsR.md §7, M13), so
--     `InstXImpOpenR`'s conclusion at `W ⊕²` is a REVISED, unchecked
--     draft: for review.
--   * `InstXImp2` assumes the two bodies' types are related with the
--     binders matched (`C ⊑ᵂ⟨ W ⊕² ⟩ C′`); without it the statement
--     is false (a `Λ⊑` derivation pairs the RIGHT binder with an inner
--     LEFT binder).  The consumer gets it from ν⊑ν's conversions.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax)

open import Types using (Ty; `∀)
open import Ctx using (Ctxᵗ)
open import Terms using (Term; Value)
open import Reduction using (InstX)
open import ImprecisionWorld
open import TermImprecision using (_∣_⊢_⊑_∶_)

-- both sides instantiate (ν⊑ν × TyBeta on both sides)
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕² ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕² ⟩ C′ ] (W ⊕² ∣ [] ⊢ N ⊑ N′ ∶ q)

-- the left alone instantiates (ν⊑ × TyBeta, the unmatched `ev-L`)
InstXImpL : Set
InstXImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q)

-- the right instantiates into a binder the left has already opened
-- alone (the `Λ⊑` case of InstXImp2): the right's new name joins the
-- left's (before D28 at `X⊑★`; now X⊑X, see the charter)
InstXImpOpenR : Set
InstXImpOpenR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {N V′ N′ : Term}
    {C C′ : Ty} {r : C ⊑ᵂ⟨ W ⊕ᴸ ⟩ `∀ C′}
  → Value V′ → InstX V′ N′
  → W ⊕ᴸ ∣ [] ⊢ N ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕² ⟩ C′ ] (W ⊕² ∣ [] ⊢ N ⊑ N′ ∶ q)
