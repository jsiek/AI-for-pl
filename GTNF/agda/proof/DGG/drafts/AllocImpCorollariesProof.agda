open import proof.DGG.drafts.AllocImpDef using (AllocImp)

module proof.DGG.drafts.AllocImpCorollariesProof (alloc-imp : AllocImp) where

-- File Charter:
--   * DRAFT SKELETON (2026-10-03): the four evolution corollaries of
--     drafts/AllocImpDef from the general `AllocImp`, at γ = [].  Each
--     is AllocImp at (ρ, ρ′) ∈ {(suc, id), (id, suc), (suc, suc)} plus
--     two world facts: the operation is a `WorldRen` (no premise
--     beyond the payload's `⊢ᴿ`, for `repwk-alloc`) and it preserves
--     `WfWorld` (here the constructor's other premises are used).
--   * Orientation: the LEFT term is the more precise one.

open import Data.Nat using (zero; suc)
open import Data.List using ([])
open import Data.Product using (_×_; _,_)

open import Types using (Ty; ★; Renameᵗ)
open import Ctx
open import Terms using (Term)
open import TermSubst using (renᴹᴿ)
open import ImprecisionWorld
open import TermImprecision
open import proof.DGG.Evolve using (NoLeftPartner)
open import proof.DGG.drafts.AllocImpDef

private
  variable
    Δ Δ′ : Ctxᵗ

idʳ : Renameᵗ
idʳ X = X

------------------------------------------------------------------------
-- Glue: each operation is a renaming, and preserves WfWorld
------------------------------------------------------------------------

wr-allocᴸ : ∀ {W : World Δ Δ′} {R} → reps Δ ⊢ᴿ R
  → WorldRen suc idʳ W (allocᴸ R W)
wr-allocᴸ wR = {!!}

wr-allocᴿ : ∀ {W : World Δ Δ′} {R′} → reps Δ′ ⊢ᴿ R′
  → WorldRen idʳ suc W (allocᴿ R′ W)
wr-allocᴿ wR′ = {!!}

-- the new pair (0, 0) is off the image of (suc, suc)
wr-alloc² : ∀ {W : World Δ Δ′} {R R′} → reps Δ ⊢ᴿ R → reps Δ′ ⊢ᴿ R′
  → WorldRen suc suc W (alloc² R R′ W)
wr-alloc² wR wR′ = {!!}

-- the new pair (0, β) is off the image of (suc, id)
wr-allocᴸ⇔ : ∀ {W : World Δ Δ′} {R β} → reps Δ ⊢ᴿ R
  → WorldRen suc idʳ W (allocᴸ⇔ R β W)
wr-allocᴸ⇔ wR = {!!}

wf-allocᴸ : ∀ {W : World Δ Δ′} {R} → WfWorld W → WfWorld (allocᴸ R W)
wf-allocᴸ wf = {!!}

wf-allocᴿ : ∀ {W : World Δ Δ′} {R′} → WfWorld W → WfWorld (allocᴿ R′ W)
wf-allocᴿ wf = {!!}

wf-alloc² : ∀ {W : World Δ Δ′} {R R′}
  → Agree (alloc² R R′ W) zero zero → WfWorld W
  → WfWorld (alloc² R R′ W)
wf-alloc² ag wf = {!!}

wf-allocᴸ⇔ : ∀ {W : World Δ Δ′} {R β}
  → NoLeftPartner W β → Agree (allocᴸ⇔ R β W) zero β → WfWorld W
  → WfWorld (allocᴸ⇔ R β W)
wf-allocᴸ⇔ nlp ag wf = {!!}

------------------------------------------------------------------------
-- The corollaries
------------------------------------------------------------------------

alloc-imp-L : AllocImpL
alloc-imp-L wR wf M⊑ with alloc-imp (wr-allocᴸ wR) same-[] M⊑
alloc-imp-L wR wf M⊑ | q , M₁ =
  wf-allocᴸ wf , q , {!M₁ (renᴹᴿ idʳ M′ ≡ M′)!}

alloc-imp-R : AllocImpR
alloc-imp-R wR′ wf M⊑ with alloc-imp (wr-allocᴿ wR′) same-[] M⊑
alloc-imp-R wR′ wf M⊑ | q , M₁ =
  wf-allocᴿ wf , q , {!M₁ (renᴹᴿ idʳ M ≡ M)!}

alloc-imp-2 : AllocImp2
alloc-imp-2 wR wR′ ag wf M⊑ with alloc-imp (wr-alloc² wR wR′) same-[] M⊑
alloc-imp-2 wR wR′ ag wf M⊑ | q , M₁ = wf-alloc² ag wf , q , M₁

alloc-imp-L⇔ : AllocImpL⇔
alloc-imp-L⇔ {β = β} wR β★ nlp ag wf M⊑
  with alloc-imp (wr-allocᴸ⇔ {β = β} wR) same-[] M⊑
alloc-imp-L⇔ {β = β} wR β★ nlp ag wf M⊑ | q , M₁ =
  wf-allocᴸ⇔ nlp ag wf , q , {!M₁ (renᴹᴿ idʳ M′ ≡ M′)!}
