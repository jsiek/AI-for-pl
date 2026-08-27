{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIBalanceRoleTaggedWorldProbe where

-- File Charter:
--   * Pins the live role-aware World.openFramesᶜ projection after stage 1.
--   * Checks binder/runtime renaming, trusted endpoint geometry, persistent
--     branch sharing, and the primitive wrapper without changing CTI.
--   * Existing production rebases are deliberately all open-frameᶜ here;
--     AlignmentOnlyRebaseInvariantProbe checks the later role refinement.

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import CastTerms using (Ctx; Term; Δᵉ)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World
import proof.DGG.Examples.Example12 as Ex12
import proof.DGG.Examples.TargetIdentityReveal as TReveal
import proof.DGG.Examples.TargetIdentityConceal as TConceal
import proof.DGG.notes.CTIBalancePrimitiveProbe as Primitive


------------------------------------------------------------------------
-- Binder and runtime-allocation renaming equations
------------------------------------------------------------------------

lift-both-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFramesᶜ Δᴸ Δᴿ}
  → renameOpenFramesᶜ Fin.suc Fin.suc ((Xᴸ ↔ᶜ Xᴿ) ∷ frames)
      ≡ (Fin.suc Xᴸ ↔ᶜ Fin.suc Xᴿ) ∷
        renameOpenFramesᶜ Fin.suc Fin.suc frames
lift-both-renaming = refl

lift-left-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFramesᶜ Δᴸ Δᴿ}
  → renameOpenFramesᶜ Fin.suc (λ X → X) ((Xᴸ ↔ᶜ Xᴿ) ∷ frames)
      ≡ (Fin.suc Xᴸ ↔ᶜ Xᴿ) ∷
        renameOpenFramesᶜ Fin.suc (λ X → X) frames
lift-left-renaming = refl

bind-right-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFramesᶜ Δᴸ Δᴿ}
  → renameOpenFramesᶜ (λ X → X) Fin.suc ((Xᴸ ↔ᶜ Xᴿ) ∷ frames)
      ≡ (Xᴸ ↔ᶜ Fin.suc Xᴿ) ∷
        renameOpenFramesᶜ (λ X → X) Fin.suc frames
bind-right-renaming = refl

bind-term-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFramesᶜ Δᴸ Δᴿ}
  → ((Xᴸ ↔ᶜ Xᴿ) ∷ frames) ≡ (Xᴸ ↔ᶜ Xᴿ) ∷ frames
bind-term-renaming = refl


------------------------------------------------------------------------
-- Example 12: C1 and C12
------------------------------------------------------------------------

example12-c1-outside :
  openFramesᶜ Ex12.checkpoint₁-outside-world ≡ []
example12-c1-outside = refl

example12-c1-outer :
  openFramesᶜ Ex12.checkpoint₁-alpha-current ≡
    (zero ↔ᶜ suc zero) ∷ []
example12-c1-outer = refl

example12-c1-inner :
  openFramesᶜ Ex12.checkpoint₁-beta-current ≡
    (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
example12-c1-inner = refl

example12-c12-outside :
  openFramesᶜ Ex12.checkpoint₅-world ≡ []
example12-c12-outside = refl

example12-c12-outer :
  openFramesᶜ Ex12.checkpoint₅-alpha-current ≡
    (zero ↔ᶜ suc (suc zero)) ∷ []
example12-c12-outer = refl

example12-c12-inner :
  openFramesᶜ Ex12.checkpoint₅-beta-current ≡
    (zero ↔ᶜ suc zero) ∷
    (zero ↔ᶜ suc (suc zero)) ∷ []
example12-c12-inner = refl


------------------------------------------------------------------------
-- Stage-1 TargetIdentityReveal allocation geometry
------------------------------------------------------------------------

target-reveal-c1-both-open :
  openFramesᶜ TReveal.checkpoint₁-beta-current ≡
    (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
target-reveal-c1-both-open = refl

target-reveal-allocation-base :
  openFramesᶜ TReveal.checkpoint₃-allocation-world ≡ []
target-reveal-allocation-base = refl

-- Stage 1 marks this existing production rebase open.  The checked
-- alignment-only payload that will remove it from this scan lives in
-- AlignmentOnlyRebaseInvariantProbe.
target-reveal-alpha-stage1-open :
  openFramesᶜ TReveal.checkpoint₃-world ≡
    (zero ↔ᶜ suc zero) ∷ []
target-reveal-alpha-stage1-open = refl

target-reveal-c8-stage1-both-open :
  openFramesᶜ TReveal.checkpoint₃-beta-current ≡
    (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
target-reveal-c8-stage1-both-open = refl


------------------------------------------------------------------------
-- Actual CTI consumers share their one current world's projection
------------------------------------------------------------------------

framesForRelated : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → OpenFramesᶜ (Δᵉ Γᴸ) (Δᵉ Γᴿ)
framesForRelated {γ = γ} related = openFramesᶜ γ

target-conceal-c10-function-branch :
  framesForRelated
    TConceal.checkpoint₆-beta-concealed-argument-imprecision ≡
      (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
target-conceal-c10-function-branch = refl

target-conceal-c10-argument-branch :
  framesForRelated TReveal.checkpoint₈-beta-conceal-imprecision ≡
    (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
target-conceal-c10-argument-branch = refl

primitive-shared-root :
  framesForRelated Primitive.primitive-checkpoint-imprecision ≡
    (zero ↔ᶜ zero) ∷ (zero ↔ᶜ suc zero) ∷ []
primitive-shared-root = refl
