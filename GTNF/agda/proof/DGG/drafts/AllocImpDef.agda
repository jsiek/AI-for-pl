module proof.DGG.drafts.AllocImpDef where

-- File Charter:
--   * DRAFT STATEMENT (2026-10-03), NOT APPROVED: transport of `⊑`
--     along a representation-only renaming of the two sides, and its
--     four corollaries, one per allocating evolution constructor
--     (`ev-L`, `ev-R`, `ev-2`, `ev-L⇔`).  For review (drafts/STATEMENTS.md).
--   * WHY THE GENERAL FORM.  `allocᴸ` alone is not inductive: under
--     `Λ⊑Λ`/`Λ⊑` the shift becomes `renᴹᴿ (extᵗ suc)`, and
--     `allocate R (underΛ Δ) ≠ underΛ (allocate R Δ)`.  So the lemma
--     renames the left universe by any `RepWk ρ` and the right by any
--     `RepWk ρ′` (the same cut as `⊢renᴿ`, proof/TypeSafety/RepWeaken):
--     insertion at depth k is `ρ = extN k suc`, and going under a binder
--     is `extᵗ ρ`.  The worlds are RELATED (`WorldRen`), not computed,
--     because `names (underΛ Δ₁)` and `map (extᵗ ρ) (names (underΛ Δ))`
--     agree only propositionally.
--   * `WorldRen` keeps every position and mark (no rebase), and
--     relates ϱ only on the image of (ρ, ρ′): `alloc²`/`allocᴸ⇔` add a
--     global pair whose left rep. var is not in the image of ρ = suc.
--   * PERMISSIONS (design.md D28, 2026-10-05): the marks are derived
--     (`marksʷ`), so `WorldRen` states that they agree (`wr-marks`, was
--     `wr-μ`) and that κ is renamed with the right side (`wr-κ`, which
--     R1/R2 transport through).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; ★; Renameᵗ)
open import Ctx using (Ctxᵗ; reps; names; RepWk; RVar; _⊢ᴿ_; _∋rep_:=_)
open import Terms using (Term)
open import TermSubst using (renᴹᴿ)
open import Boundary using (renᴮᴿ)
open import ImprecisionWorld
open import TermImprecision using (_∣_⊢_⊑_∶_)

private
  variable
    Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ

------------------------------------------------------------------------
-- Renaming relations (statement-level concepts)
------------------------------------------------------------------------

-- Δ₁ is Δ with its representation universe renamed by ρ; the name
-- map moves pointwise, no ordinary position moves
record CtxRen (ρ : Renameᵗ) (Δ Δ₁ : Ctxᵗ) : Set where
  constructor ctx-ren
  field
    ren-reps  : RepWk ρ (reps Δ) (reps Δ₁)
    ren-names : names Δ₁ ≡ map ρ (names Δ)
open CtxRen public

-- W₁ is W with the left universe renamed by ρ and the right by ρ′:
-- the same center, marks and positions; the paired rep. vars of W are
-- exactly the paired rep. vars of W₁ on the image of (ρ, ρ′)
record WorldRen (ρ ρ′ : Renameᵗ) (W : World Δ Δ′) (W₁ : World Δ₁ Δ′₁)
    : Set where
  constructor world-ren
  field
    wr-left   : CtxRen ρ Δ Δ₁
    wr-right  : CtxRen ρ′ Δ′ Δ′₁
    wr-marks  : marksʷ W₁ ≡ marksʷ W
    wr-κ      : κʷ W₁ ≡ map ρ′ (κʷ W)
    wr-ηᴸ     : ∀ X → emb (ηᴸʷ W₁) X ≡ emb (ηᴸʷ W) X
    wr-ηᴿ     : ∀ X → emb (ηᴿʷ W₁) X ≡ emb (ηᴿʷ W) X
    wr-paired : ∀ {α β}
      → (Paired W₁ (ρ α) (ρ′ β) → Paired W α β)
        × (Paired W α β → Paired W₁ (ρ α) (ρ′ β))
open WorldRen public

-- two term-context imprecisions with the same types (the proofs are
-- at different worlds)
data SameTys {ns ns′ ns₁ ns′₁ n n₁ μ μ₁} {ηᴸ : ns ↪ n} {ηᴿ : ns′ ↪ n}
    {ηᴸ₁ : ns₁ ↪ n₁} {ηᴿ₁ : ns′₁ ↪ n₁}
    : Entries μ ηᴸ ηᴿ → Entries μ₁ ηᴸ₁ ηᴿ₁ → Set where
  same-[] : SameTys [] []
  same-∷  : ∀ {γ γ₁ A A′ p p₁} → SameTys γ γ₁
    → SameTys (ctx-imp A A′ p ∷ γ) (ctx-imp A A′ p₁ ∷ γ₁)

------------------------------------------------------------------------
-- The general statement
------------------------------------------------------------------------

AllocImp : Set
AllocImp = ∀ {Δ Δ′ Δ₁ Δ′₁ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁}
    {γ : CtxImp W} {γ₁ : CtxImp W₁}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → WorldRen ρ ρ′ W W₁
  → SameTys γ γ₁
  → W ∣ γ ⊢ M ⊑ M′ ∶ p
  → Σ[ q ∈ A ⊑ᵂ⟨ W₁ ⟩ A′ ] (W₁ ∣ γ₁ ⊢ renᴹᴿ ρ M ⊑ renᴹᴿ ρ′ M′ ∶ q)

-- the renaming commutes with an interior world (used by the boundary
-- cases of AllocImp, and by the Sim/SimBack frames under boundaries).
-- NOT CLAIMED: `WfWorld Wᵢ₁` (see STATEMENTS.md, AllocImp, misfit).
AllocImpInterior : Set
AllocImpInterior = ∀ {Δ Δ′ Δ₁ Δ′₁ Δᵢ Δ′ᵢ : Ctxᵗ} {ρ ρ′ : Renameᵗ}
    {W : World Δ Δ′} {W₁ : World Δ₁ Δ′₁} {Wᵢ : World Δᵢ Δ′ᵢ} {Θ Θ′}
  → WorldRen ρ ρ′ W W₁
  → Interior W Θ Θ′ Wᵢ
  → Σ[ Δᵢ₁ ∈ Ctxᵗ ] Σ[ Δ′ᵢ₁ ∈ Ctxᵗ ] Σ[ Wᵢ₁ ∈ World Δᵢ₁ Δ′ᵢ₁ ]
      (Interior W₁ (renᴮᴿ ρ Θ) (renᴮᴿ ρ′ Θ′) Wᵢ₁ × WorldRen ρ ρ′ Wᵢ Wᵢ₁)

------------------------------------------------------------------------
-- The four corollaries, in the form EvolveImp consumes: the premises
-- are exactly those the evolution constructor records
------------------------------------------------------------------------

-- ev-L: an unmatched left TyBeta (`↑ᴹ[ new R ] M = renᴹᴿ suc M`)
AllocImpL : Set
AllocImpL = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ R W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ R W ⟩ A′ ]
        (allocᴸ R W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)

-- ev-R: an unmatched right TyBeta
AllocImpR : Set
AllocImpR = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ′ ⊢ᴿ R′
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴿ R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴿ R′ W ⟩ A′ ]
        (allocᴿ R′ W ∣ [] ⊢ M ⊑ renᴹᴿ suc M′ ∶ q)

-- ev-2: a matched pair of TyBetas
AllocImp2 : Set
AllocImp2 = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R R′ : Ty}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′
  → Agree (alloc² R R′ W) zero zero
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (alloc² R R′ W)
    × Σ[ q ∈ A ⊑ᵂ⟨ alloc² R R′ W ⟩ A′ ]
        (alloc² R R′ W ∣ [] ⊢ renᴹᴿ suc M ⊑ renᴹᴿ suc M′ ∶ q)

-- ev-L⇔: the left catches up with a right boundary `[+X^β]`
AllocImpL⇔ : Set
AllocImpL⇔ = ∀ {Δ Δ′ : Ctxᵗ} {W : World Δ Δ′} {R : Ty} {β : RVar}
    {M M′ : Term} {A A′ : Ty} {p : A ⊑ᵂ⟨ W ⟩ A′}
  → reps Δ ⊢ᴿ R
  → Δ′ ∋rep β := ★
  → Agree (allocᴸ⇔ R β W) zero β
  → WfWorld W
  → W ∣ [] ⊢ M ⊑ M′ ∶ p
  → WfWorld (allocᴸ⇔ R β W)
    × Σ[ q ∈ A ⊑ᵂ⟨ allocᴸ⇔ R β W ⟩ A′ ]
        (allocᴸ⇔ R β W ∣ [] ⊢ renᴹᴿ suc M ⊑ M′ ∶ q)
