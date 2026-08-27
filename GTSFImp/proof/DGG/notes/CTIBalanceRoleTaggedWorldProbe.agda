{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIBalanceRoleTaggedWorldProbe where

-- File Charter:
--   * Probes the proposed role tag on source-rebase world changes without
--     changing the live World or CTI definitions.
--   * Derives the locally open source-rebase frames from one current world
--     and one role vector indexed by that world's rebase history.
--   * Pins the critical trusted geometries, scope-renaming equations,
--     non-top allocation discharge, branch sharing, and primitive wrapper.

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using (Ty)
open import CastTerms using (Ctx; Term; Δᵉ)
import proof.DGG.CastTermImprecision as CTI
open import proof.DGG.World using
  (_⊑ᶜ_; _⊑ᵀ⟨_⟩_; WorldChange; emptyᶜ; _▻ᶜ_;
   center-changeᶜ; lift-both-changeᶜ; lift-left-changeᶜ;
   bind-left-changeᶜ; bind-right-changeᶜ; bind-both-changeᶜ;
   bind-both-star-changeᶜ; bind-term-changeᶜ;
   rebase-source-changeᶜ; sourceRebaseCountᶜ)
import proof.DGG.Examples.Example12 as Ex12
import proof.DGG.Examples.TargetIdentityReveal as TReveal
import proof.DGG.Examples.TargetIdentityConceal as TConceal
import proof.DGG.notes.CTIBalancePrimitiveProbe as Primitive


------------------------------------------------------------------------
-- Proposed role-enriched rebase history
------------------------------------------------------------------------

data RebaseRole : Set where
  alignment-only open-frame : RebaseRole

-- This vector is the notes-only representation of adding one RebaseRole
-- field to every rebase-source-changeᶜ node.  The newest rebase role is at
-- the head, matching the outer constructor of the current world.
TaggedHistory : ∀ {Γᴸ Γᴿ : Ctx} → Γᴸ ⊑ᶜ Γᴿ → Set
TaggedHistory γ = Vec.Vec RebaseRole (sourceRebaseCountᶜ γ)

record RoleTaggedWorld {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ) : Set where
  constructor role-world
  field
    roles : TaggedHistory γ

tagWorld : ∀ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → TaggedHistory γ
  → RoleTaggedWorld γ
tagWorld γ roles = role-world roles

record RebaseFrame (Δᴸ Δᴿ : ℕ) : Set where
  constructor _↔_
  field
    source-pivot : Fin Δᴸ
    target-pivot : Fin Δᴿ

OpenFrames : ℕ → ℕ → Set
OpenFrames Δᴸ Δᴿ = List (RebaseFrame Δᴸ Δᴿ)

renameFrames : ∀ {Δᴸ Δᴿ Δᴸ′ Δᴿ′}
  → (Fin Δᴸ → Fin Δᴸ′)
  → (Fin Δᴿ → Fin Δᴿ′)
  → OpenFrames Δᴸ Δᴿ
  → OpenFrames Δᴸ′ Δᴿ′
renameFrames renameᴸ renameᴿ [] = []
renameFrames renameᴸ renameᴿ ((Xᴸ ↔ Xᴿ) ∷ frames) =
  (renameᴸ Xᴸ ↔ renameᴿ Xᴿ) ∷ renameFrames renameᴸ renameᴿ frames

deriveOpenFrames : ∀ {Γᴸ Γᴿ : Ctx} (γ : Γᴸ ⊑ᶜ Γᴿ)
  → TaggedHistory γ
  → OpenFrames (Δᵉ Γᴸ) (Δᵉ Γᴿ)
deriveOpenFrames emptyᶜ Vec.[] = []
deriveOpenFrames (γ ▻ᶜ center-changeᶜ) roles =
  deriveOpenFrames γ roles
deriveOpenFrames (γ ▻ᶜ lift-both-changeᶜ v eqᴸ eqᴿ) roles =
  renameFrames Fin.suc Fin.suc (deriveOpenFrames γ roles)
deriveOpenFrames (γ ▻ᶜ lift-left-changeᶜ eqᴸ) roles =
  renameFrames Fin.suc (λ X → X) (deriveOpenFrames γ roles)
deriveOpenFrames (γ ▻ᶜ bind-left-changeᶜ A eqᴸ) roles =
  renameFrames Fin.suc (λ X → X) (deriveOpenFrames γ roles)
deriveOpenFrames (γ ▻ᶜ bind-right-changeᶜ B fresh eqᴿ) roles =
  renameFrames (λ X → X) Fin.suc (deriveOpenFrames γ roles)
deriveOpenFrames (γ ▻ᶜ bind-both-changeᶜ p eqᴸ eqᴿ) roles =
  renameFrames Fin.suc Fin.suc (deriveOpenFrames γ roles)
deriveOpenFrames
    (γ ▻ᶜ bind-both-star-changeᶜ p A≢★ eqᴸ eqᴿ) roles =
  renameFrames Fin.suc Fin.suc (deriveOpenFrames γ roles)
deriveOpenFrames (γ ▻ᶜ bind-term-changeᶜ p) roles =
  deriveOpenFrames γ roles
deriveOpenFrames
    (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented)
    (alignment-only Vec.∷ roles) =
  deriveOpenFrames γ roles
deriveOpenFrames
    (γ ▻ᶜ rebase-source-changeᶜ Xᴸ Xᴿ ok represented)
    (open-frame Vec.∷ roles) =
  (Xᴸ ↔ Xᴿ) ∷ deriveOpenFrames γ roles

openFramesOf : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
  → RoleTaggedWorld γ
  → OpenFrames (Δᵉ Γᴸ) (Δᵉ Γᴿ)
openFramesOf {γ = γ} (role-world roles) = deriveOpenFrames γ roles

-- This adapter checks that a trusted CTI derivation's own current world is
-- enough to select its role-tagged history.  The CTI evidence contributes no
-- second stack: frame recovery depends only on that one current world.
framesForRelated : ∀ {Γᴸ Γᴿ : Ctx} {γ : Γᴸ ⊑ᶜ Γᴿ}
    {M : Term (Δᵉ Γᴸ)} {M′ : Term (Δᵉ Γᴿ)}
    {A : Ty (Δᵉ Γᴸ)} {B : Ty (Δᵉ Γᴿ)} {p : A ⊑ᵀ⟨ γ ⟩ B}
  → RoleTaggedWorld γ
  → γ CTI.⊢² M ⊑ M′ ∶ p
  → OpenFrames (Δᵉ Γᴸ) (Δᵉ Γᴿ)
framesForRelated tagged related = openFramesOf tagged


------------------------------------------------------------------------
-- Binder and runtime-allocation renaming equations
------------------------------------------------------------------------

lift-both-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFrames Δᴸ Δᴿ}
  → renameFrames Fin.suc Fin.suc ((Xᴸ ↔ Xᴿ) ∷ frames)
      ≡ (Fin.suc Xᴸ ↔ Fin.suc Xᴿ) ∷
        renameFrames Fin.suc Fin.suc frames
lift-both-renaming = refl

lift-left-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFrames Δᴸ Δᴿ}
  → renameFrames Fin.suc (λ X → X) ((Xᴸ ↔ Xᴿ) ∷ frames)
      ≡ (Fin.suc Xᴸ ↔ Xᴿ) ∷
        renameFrames Fin.suc (λ X → X) frames
lift-left-renaming = refl

bind-right-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFrames Δᴸ Δᴿ}
  → renameFrames (λ X → X) Fin.suc ((Xᴸ ↔ Xᴿ) ∷ frames)
      ≡ (Xᴸ ↔ Fin.suc Xᴿ) ∷
        renameFrames (λ X → X) Fin.suc frames
bind-right-renaming = refl

bind-term-renaming : ∀ {Δᴸ Δᴿ} {Xᴸ : Fin Δᴸ} {Xᴿ : Fin Δᴿ}
    {frames : OpenFrames Δᴸ Δᴿ}
  → ((Xᴸ ↔ Xᴿ) ∷ frames) ≡ (Xᴸ ↔ Xᴿ) ∷ frames
bind-term-renaming = refl


------------------------------------------------------------------------
-- Example 12: C1 and C12
------------------------------------------------------------------------

example12-c1-outside :
  openFramesOf
    (tagWorld Ex12.checkpoint₁-outside-world Vec.[]) ≡ []
example12-c1-outside = refl

example12-c1-outer :
  openFramesOf
    (tagWorld Ex12.checkpoint₁-alpha-current
      (open-frame Vec.∷ Vec.[])) ≡ (zero ↔ suc zero) ∷ []
example12-c1-outer = refl

example12-c1-inner :
  openFramesOf
    (tagWorld Ex12.checkpoint₁-beta-current
      (open-frame Vec.∷ open-frame Vec.∷ Vec.[])) ≡
      (zero ↔ zero) ∷ (zero ↔ suc zero) ∷ []
example12-c1-inner = refl

example12-c12-outside :
  openFramesOf (tagWorld Ex12.checkpoint₅-world Vec.[]) ≡ []
example12-c12-outside = refl

example12-c12-outer :
  openFramesOf
    (tagWorld Ex12.checkpoint₅-alpha-current
      (open-frame Vec.∷ Vec.[])) ≡
      (zero ↔ suc (suc zero)) ∷ []
example12-c12-outer = refl

example12-c12-inner :
  openFramesOf
    (tagWorld Ex12.checkpoint₅-beta-current
      (open-frame Vec.∷ open-frame Vec.∷ Vec.[])) ≡
      (zero ↔ suc zero) ∷
      (zero ↔ suc (suc zero)) ∷ []
example12-c12-inner = refl


------------------------------------------------------------------------
-- TargetIdentityReveal: allocation discharge and C8
------------------------------------------------------------------------

target-reveal-c1-both-open :
  openFramesOf
    (tagWorld TReveal.checkpoint₁-beta-current
      (open-frame Vec.∷ open-frame Vec.∷ Vec.[])) ≡
      (zero ↔ zero) ∷ (zero ↔ suc zero) ∷ []
target-reveal-c1-both-open = refl

-- The source allocation rebuilds from checkpoint₁-world.  Its alpha rebase
-- is still needed for endpoint alignment, but no longer represents an open
-- target-only frame.  The newer beta rebase remains open.  Thus allocation
-- discharges the non-top alpha frame without pretending to pop beta first.
target-reveal-allocation-base :
  openFramesOf
    (tagWorld TReveal.checkpoint₃-allocation-world Vec.[]) ≡ []
target-reveal-allocation-base = refl

target-reveal-alpha-alignment-only :
  openFramesOf
    (tagWorld TReveal.checkpoint₃-world
      (alignment-only Vec.∷ Vec.[])) ≡ []
target-reveal-alpha-alignment-only = refl

target-reveal-c8-beta-open :
  openFramesOf
    (tagWorld TReveal.checkpoint₃-beta-current
      (open-frame Vec.∷ alignment-only Vec.∷ Vec.[])) ≡
      (zero ↔ zero) ∷ []
target-reveal-c8-beta-open = refl


------------------------------------------------------------------------
-- TargetIdentityConceal branch sharing and the primitive wrapper
------------------------------------------------------------------------

target-conceal-c10-function-branch :
  framesForRelated
    (tagWorld TReveal.checkpoint₃-beta-current
      (open-frame Vec.∷ alignment-only Vec.∷ Vec.[]))
    TConceal.checkpoint₆-beta-concealed-argument-imprecision ≡
      (zero ↔ zero) ∷ []
target-conceal-c10-function-branch = refl

target-conceal-c10-argument-branch :
  framesForRelated
    (tagWorld TReveal.checkpoint₃-beta-current
      (open-frame Vec.∷ alignment-only Vec.∷ Vec.[]))
    TReveal.checkpoint₈-beta-conceal-imprecision ≡
      (zero ↔ zero) ∷ []
target-conceal-c10-argument-branch = refl

-- Importing the strict primitive probe above checks its source typing,
-- compilation, evaluation to 43, and CTI checkpoint.  Both primitive
-- operands receive the same persistent ambient history; only the left one
-- traverses the live conceal.
primitive-left-branch :
  framesForRelated
    (tagWorld TReveal.checkpoint₃-beta-current
      (open-frame Vec.∷ alignment-only Vec.∷ Vec.[]))
    Primitive.primitive-checkpoint-imprecision ≡
      (zero ↔ zero) ∷ []
primitive-left-branch = refl

primitive-right-branch :
  framesForRelated
    (tagWorld TReveal.checkpoint₃-beta-current
      (open-frame Vec.∷ alignment-only Vec.∷ Vec.[]))
    Primitive.primitive-checkpoint-imprecision ≡
      (zero ↔ zero) ∷ []
primitive-right-branch = refl
