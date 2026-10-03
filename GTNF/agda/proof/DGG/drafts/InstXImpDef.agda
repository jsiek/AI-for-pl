module proof.DGG.drafts.InstXImpDef where

-- File Charter:
--   * DRAFT STATEMENTS (2026-10-03), NOT APPROVED: `inst_X` preserves
--     `⊑` (PLAN.md §3 `InstX⊑`).  For review (drafts/STATEMENTS.md).
--   * THE ABSTRACT READING.  `InstX V N` reads N under `underΛ Δ` (the
--     left value's abstract rep. var at 0, TermImprecision's charter),
--     so the conclusions are stated at the worlds of the `Λ` rules:
--     `W ⊕ m` (both sides opened, as `Λ⊑Λ`'s premise) and `W ⊕ᴸ` (the
--     left alone, as `Λ⊑`'s premise).  The TyBeta consumers then move
--     the result to the REPRESENTED interior of `inst []` (bindR R at 0,
--     the pair (0,0) global): that refinement is a separate transport
--     (STATEMENTS.md, "not in the tree").
--   * The mark m of the opened name is CHOSEN (D11): a `Λ`-vs-`gen`
--     pair needs `X⊑★`, a `Λ`-vs-`Λ` pair gives `X⊑X`.
--   * `InstXImp2` assumes the two bodies' types are related with the
--     binders matched (`C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′`); without it the statement
--     is false (a `Λ⊑` derivation pairs the RIGHT binder with an inner
--     LEFT binder).  The consumer gets it from ν⊑ν's conversions.
--   * Orientation: the LEFT term is the more precise one.

open import Data.List using ([])
open import Data.Product using (Σ-syntax; ∃-syntax)

open import Types using (Ty; `∀)
open import Ctx using (Ctxᵗ)
open import Terms using (Term; Value)
open import Reduction using (InstX)
open import Imprecision using (VarImp; X⊑X; X⊑★)
open import ImprecisionWorld
open import TermImprecision using (_∣_⊢_⊑_∶_)

-- both sides instantiate (ν⊑ν × TyBeta on both sides)
InstXImp2 : Set
InstXImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V V′ N N′ : Term}
    {C C′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ `∀ C′}
  → C ⊑ᵂ⟨ W ⊕ X⊑X ⟩ C′
  → Value V → Value V′ → InstX V N → InstX V′ N′
  → W ∣ [] ⊢ V ⊑ V′ ∶ r
  → ∃[ m ] Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ m ⟩ C′ ] (W ⊕ m ∣ [] ⊢ N ⊑ N′ ∶ q)

-- the left alone instantiates (ν⊑ × TyBeta, the unmatched `ev-L`)
InstXImpL : Set
InstXImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {V N M′ : Term}
    {C B′ : Ty} {r : `∀ C ⊑ᵂ⟨ W ⟩ B′}
  → Value V → InstX V N
  → W ∣ [] ⊢ V ⊑ M′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ᴸ ⟩ B′ ] (W ⊕ᴸ ∣ [] ⊢ N ⊑ M′ ∶ q)

-- the right instantiates into a binder the left has already opened
-- alone (the `Λ⊑` case of InstXImp2): the right's new name joins the
-- left's, at `X⊑★`
InstXImpOpenR : Set
InstXImpOpenR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {N V′ N′ : Term}
    {C C′ : Ty} {r : C ⊑ᵂ⟨ W ⊕ᴸ ⟩ `∀ C′}
  → Value V′ → InstX V′ N′
  → W ⊕ᴸ ∣ [] ⊢ N ⊑ V′ ∶ r
  → Σ[ q ∈ C ⊑ᵂ⟨ W ⊕ X⊑★ ⟩ C′ ] (W ⊕ X⊑★ ∣ [] ⊢ N ⊑ N′ ∶ q)
