{-# OPTIONS --safe #-}

module proof.DGG.notes.CTIBalanceTrustedAudit where

-- File Charter:
--   * Pins the endpoint pivot pairs used by every distinct trusted-example
--     source-rebase construction.
--   * Checks the nontrivial LIFO traces from Example 12 and the two target
--     identity examples without changing the live CTI relation.
--   * Records the ambient frame stacks required at application branches.

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import CastTerms using (Ctx; Δᵉ)
open import proof.DGG.World using (_⊑ᶜ_)
open import proof.DGG.SourceRebase using
  (SourceRebaseᶜ; source-rebase-now)
import proof.DGG.Examples.Example12 as Ex12
import proof.DGG.Examples.TargetIdentityReveal as TReveal
import proof.DGG.Examples.TargetIdentityConceal as TConceal
open import proof.DGG.ImpLadder using (impLadderDefault)


------------------------------------------------------------------------
-- The proposed local frame representation
------------------------------------------------------------------------

record RebaseFrame (Δᴸ Δᴿ : ℕ) : Set where
  constructor _↔_
  field
    source-pivot : Fin Δᴸ
    target-pivot : Fin Δᴿ

OpenFrames : ℕ → ℕ → Set
OpenFrames Δᴸ Δᴿ = List (RebaseFrame Δᴸ Δᴿ)

frameOf : ∀ {Γᴸ Γᴿ : Ctx} {γ γᵖ : Γᴸ ⊑ᶜ Γᴿ}
    {Xᴸ Xᴿ}
  → SourceRebaseᶜ γ γᵖ Xᴸ Xᴿ
  → RebaseFrame (Δᵉ Γᴸ) (Δᵉ Γᴿ)
frameOf {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} rebase = Xᴸ ↔ Xᴿ


------------------------------------------------------------------------
-- Actual endpoint pairs before and after runtime allocation
------------------------------------------------------------------------

example12-before-outer : RebaseFrame 1 2
example12-before-outer =
  frameOf {γ = Ex12.checkpoint₁-outside-world}
    (source-rebase-now {γ = Ex12.checkpoint₁-outside-world}
    {Xᴸ = zero} {Xᴿ = suc zero} Ex12.checkpoint₁-alpha-ok
    Ex12.checkpoint₁-alpha-representation)

example12-before-outer-pinned :
  example12-before-outer ≡ zero ↔ suc zero
example12-before-outer-pinned = refl

example12-before-inner : RebaseFrame 1 2
example12-before-inner =
  frameOf {γ = Ex12.checkpoint₁-alpha-current}
    (source-rebase-now {γ = Ex12.checkpoint₁-alpha-current}
    {Xᴸ = zero} {Xᴿ = zero} Ex12.checkpoint₁-beta-ok
    Ex12.checkpoint₁-beta-representation)

example12-before-inner-pinned :
  example12-before-inner ≡ zero ↔ zero
example12-before-inner-pinned = refl

example12-after-outer : RebaseFrame 1 3
example12-after-outer =
  frameOf {γ = Ex12.checkpoint₅-world}
    (source-rebase-now {γ = Ex12.checkpoint₅-world}
    {Xᴸ = zero} {Xᴿ = suc (suc zero)} Ex12.checkpoint₅-alpha-ok
    Ex12.checkpoint₅-alpha-representation)

example12-after-outer-pinned :
  example12-after-outer ≡ zero ↔ suc (suc zero)
example12-after-outer-pinned = refl

example12-after-inner : RebaseFrame 1 3
example12-after-inner =
  frameOf {γ = Ex12.checkpoint₅-alpha-current}
    (source-rebase-now {γ = Ex12.checkpoint₅-alpha-current}
    {Xᴸ = zero} {Xᴿ = suc zero} Ex12.checkpoint₅-beta-ok
    Ex12.checkpoint₅-beta-representation)

example12-after-inner-pinned :
  example12-after-inner ≡ zero ↔ suc zero
example12-after-inner-pinned = refl

target-reveal-before-outer : RebaseFrame 1 2
target-reveal-before-outer =
  frameOf {γ = TReveal.checkpoint₁-outside-world}
    (source-rebase-now {γ = TReveal.checkpoint₁-outside-world}
    {Xᴸ = zero} {Xᴿ = suc zero} TReveal.checkpoint₁-alpha-ok
    TReveal.checkpoint₁-alpha-representation)

target-reveal-before-outer-pinned :
  target-reveal-before-outer ≡ zero ↔ suc zero
target-reveal-before-outer-pinned = refl

target-reveal-before-inner : RebaseFrame 1 2
target-reveal-before-inner =
  frameOf {γ = TReveal.checkpoint₁-alpha-current}
    (source-rebase-now {γ = TReveal.checkpoint₁-alpha-current}
    {Xᴸ = zero} {Xᴿ = zero} TReveal.checkpoint₁-beta-ok
    TReveal.checkpoint₁-beta-representation)

target-reveal-before-inner-pinned :
  target-reveal-before-inner ≡ zero ↔ zero
target-reveal-before-inner-pinned = refl

target-reveal-after-inner : RebaseFrame 1 2
target-reveal-after-inner =
  frameOf {γ = TReveal.checkpoint₃-world}
    (source-rebase-now {γ = TReveal.checkpoint₃-world}
    {Xᴸ = zero} {Xᴿ = zero} TReveal.checkpoint₃-beta-ok
    TReveal.checkpoint₃-beta-representation)

target-reveal-after-inner-pinned :
  target-reveal-after-inner ≡ zero ↔ zero
target-reveal-after-inner-pinned = refl


------------------------------------------------------------------------
-- LIFO traces forced by the trusted constructors
------------------------------------------------------------------------

infix 3 _—[_]→_

data _—[_]→_ {Δᴸ Δᴿ : ℕ} :
    OpenFrames Δᴸ Δᴿ → RebaseFrame Δᴸ Δᴿ →
    OpenFrames Δᴸ Δᴿ → Set where
  push : ∀ {frames frame}
    → frames —[ frame ]→ frame ∷ frames
  pop : ∀ {frames frame}
    → frame ∷ frames —[ frame ]→ frames

example12-checkpoint12-open-outer :
  [] —[ example12-after-outer ]→ example12-after-outer ∷ []
example12-checkpoint12-open-outer = push

example12-checkpoint12-open-inner :
  example12-after-outer ∷ [] —[ example12-after-inner ]→
    example12-after-inner ∷ example12-after-outer ∷ []
example12-checkpoint12-open-inner = push

example12-checkpoint12-close-inner :
  example12-after-inner ∷ example12-after-outer ∷ []
    —[ example12-after-inner ]→ example12-after-outer ∷ []
example12-checkpoint12-close-inner = pop

example12-checkpoint12-close-outer :
  example12-after-outer ∷ [] —[ example12-after-outer ]→ []
example12-checkpoint12-close-outer = pop

target-conceal-checkpoint6-open-inner :
  [] —[ target-reveal-after-inner ]→ target-reveal-after-inner ∷ []
target-conceal-checkpoint6-open-inner = push

target-conceal-checkpoint6-close-inner :
  target-reveal-after-inner ∷ [] —[ target-reveal-after-inner ]→ []
target-conceal-checkpoint6-close-inner = pop


------------------------------------------------------------------------
-- Application branch sharing in TargetIdentityReveal
------------------------------------------------------------------------

target-reveal-checkpoint7-application-root : OpenFrames 1 2
target-reveal-checkpoint7-application-root = []

target-reveal-checkpoint7-function-body : OpenFrames 1 2
target-reveal-checkpoint7-function-body =
  target-reveal-after-inner ∷ target-reveal-checkpoint7-application-root

target-reveal-checkpoint7-argument-root : OpenFrames 1 2
target-reveal-checkpoint7-argument-root =
  target-reveal-checkpoint7-application-root

target-reveal-checkpoint8-application-root : OpenFrames 1 2
target-reveal-checkpoint8-application-root =
  target-reveal-after-inner ∷ []

target-reveal-checkpoint8-function-root : OpenFrames 1 2
target-reveal-checkpoint8-function-root =
  target-reveal-checkpoint8-application-root

target-reveal-checkpoint8-argument-root : OpenFrames 1 2
target-reveal-checkpoint8-argument-root =
  target-reveal-checkpoint8-application-root

target-reveal-checkpoint8-conceal-body : OpenFrames 1 2
target-reveal-checkpoint8-conceal-body = []

target-reveal-checkpoint8-pop :
  target-reveal-checkpoint8-argument-root
    —[ target-reveal-after-inner ]→
  target-reveal-checkpoint8-conceal-body
target-reveal-checkpoint8-pop = pop


------------------------------------------------------------------------
-- Higher-order branch duplication in TargetIdentityConceal
------------------------------------------------------------------------

target-conceal-checkpoint10-application-root : OpenFrames 1 2
target-conceal-checkpoint10-application-root =
  target-reveal-after-inner ∷ []

target-conceal-checkpoint10-function-root : OpenFrames 1 2
target-conceal-checkpoint10-function-root =
  target-conceal-checkpoint10-application-root

target-conceal-checkpoint10-argument-root : OpenFrames 1 2
target-conceal-checkpoint10-argument-root =
  target-conceal-checkpoint10-application-root

target-conceal-checkpoint10-function-pop :
  target-conceal-checkpoint10-function-root
    —[ target-reveal-after-inner ]→ []
target-conceal-checkpoint10-function-pop = pop

target-conceal-checkpoint10-argument-pop :
  target-conceal-checkpoint10-argument-root
    —[ target-reveal-after-inner ]→ []
target-conceal-checkpoint10-argument-pop = pop


------------------------------------------------------------------------
-- Generated evidence for the non-obvious cases
------------------------------------------------------------------------

target-reveal-checkpoint8-focused-ladder : String
target-reveal-checkpoint8-focused-ladder =
  impLadderDefault TReveal.checkpoint₈-beta-conceal-imprecision

target-conceal-checkpoint6-focused-ladder : String
target-conceal-checkpoint6-focused-ladder =
  impLadderDefault TConceal.checkpoint₆-beta-result-imprecision

target-conceal-checkpoint10-function-ladder : String
target-conceal-checkpoint10-function-ladder =
  impLadderDefault
    TConceal.checkpoint₆-beta-concealed-argument-imprecision

target-conceal-checkpoint10-argument-ladder : String
target-conceal-checkpoint10-argument-ladder =
  impLadderDefault TReveal.checkpoint₈-beta-conceal-imprecision
