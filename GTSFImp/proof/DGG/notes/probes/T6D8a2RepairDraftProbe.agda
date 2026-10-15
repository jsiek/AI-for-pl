module T6D8a2RepairDraftProbe where

-- File Charter:
--   * Statement-only repair draft for the D8a2 term-substitution wrapper
--     transport blocker.
--   * Records the before surface, the boundary-stack supplied-evidence
--     repair surface, and the amended theorem as type-checked `Set`
--     declarations.
--   * Provides no implementation, inhabitants, postulates, holes, or imports
--     from this scratch module into the live DGG development.

open import Data.Maybe using (Maybe)

open import Types using (Ty; TyCtx; TyVar)
open import CastTerms using (Term; Subst; subst)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.CatchupToMorePreciseDef using
  (CatchupBoundary; CatchupBoundaryKind)
open CTI2 using
  ( World
  ; CtxImp
  ; ctx-imp
  ; SameCtx
  ; _∋ʷ_⦂_
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


record TermSubstRelDirect {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γ δ : CtxImp W)
    (σᴸ : Subst Δᴸ)
    (σᴿ : Subst Δᴿ) : Set where
  field
    lookup : ∀ {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
      → γ ∋ʷ x ⦂ ctx-imp A B p
      → W ∣ δ ⊢² σᴸ x ⊑ σᴿ x ∶ p


⊢²-term-subst-directᵀ : Set
⊢²-term-subst-directᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermSubstRelDirect W γ δ σᴸ σᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² subst σᴸ M ⊑ subst σᴿ M′ ∶ p


record BoundaryNode {Δᴸ Δᴿ Δ} : Set₁ where
  constructor boundary-node
  field
    world : World Δᴸ Δᴿ Δ
    source-ctx : CtxImp world
    image-ctx : CtxImp world

open BoundaryNode public


data BoundaryStackReachable {Δᴸ Δᴿ Δ}
    (root : BoundaryNode {Δᴸ} {Δᴿ} {Δ}) :
    BoundaryNode {Δᴸ} {Δᴿ} {Δ} → Set₁ where
  reachable-root :
      ---------------------------------
      BoundaryStackReachable root root

  reachable-boundary : ∀ {node node′ kind Xᴸ? Xᴿ?}
    → BoundaryStackReachable root node
    → CatchupBoundary kind Xᴸ? Xᴿ?
        (world node) (world node′)
    → SameCtx (source-ctx node) (source-ctx node′)
    → SameCtx (image-ctx node) (image-ctx node′)
      ---------------------------------------------
    → BoundaryStackReachable root node′


record TermSubstRelBoundary {Δᴸ Δᴿ Δ}
    (root : BoundaryNode {Δᴸ} {Δᴿ} {Δ})
    (σᴸ : Subst Δᴸ)
    (σᴿ : Subst Δᴿ) : Set₁ where
  field
    lookup :
      ∀ {node : BoundaryNode {Δᴸ} {Δᴿ} {Δ}}
      → BoundaryStackReachable root node
      → ∀ {x A B} {p : A ⊑ᵂ⟨ world node ⟩ B}
      → source-ctx node ∋ʷ x ⦂ ctx-imp A B p
      → world node ∣ image-ctx node ⊢² σᴸ x ⊑ σᴿ x ∶ p


⊢²-term-subst-boundaryᵀ : Set₁
⊢²-term-subst-boundaryᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ δ : CtxImp W}
    {σᴸ : Subst Δᴸ} {σᴿ : Subst Δᴿ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → TermSubstRelBoundary (boundary-node W γ δ) σᴸ σᴿ
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → W ∣ δ ⊢² subst σᴸ M ⊑ subst σᴿ M′ ∶ p
