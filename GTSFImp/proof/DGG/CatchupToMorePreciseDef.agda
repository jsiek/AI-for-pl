module proof.DGG.CatchupToMorePreciseDef where

-- File Charter:
--   * States target catch-up relative to an enclosing parked world.
--   * The active relation may live at that world or across a source reveal or
--     conceal boundary; catch-up evolves both worlds and replays the boundary.
--   * The less precise target reaches a related value, with no blame case.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Product using (_×_; Σ-syntax)

open import Types using (Ty; TyCtx)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.Catchup.StructuralWorldExtendDef
  using (StructuralWorldExtendᴿ)
open CTI2 using
  ( World
  ; ImpEnvMono
  ; RebaseAtᴸ
  ; RebaseAtᴿ
  ; TagRebaseAtᴸ
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


data CatchupBoundaryKind : Set where
  same-boundary : CatchupBoundaryKind
  source-reveal-boundary : CatchupBoundaryKind
  source-conceal-boundary : CatchupBoundaryKind
  target-reveal-boundary : CatchupBoundaryKind
  target-conceal-boundary : CatchupBoundaryKind


data CatchupBoundary {Δᴸ Δᴿ Δ} :
    CatchupBoundaryKind →
    World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ → Set where

  boundary-refl : ∀ {W}
      -------------------------------
    → CatchupBoundary same-boundary W W

  boundary-source-reveal : ∀ {W Wᵖ Xᴸ?}
    → ImpEnvMono W Wᵖ
    → RebaseAtᴸ W Wᵖ Xᴸ?
      -----------------------------------
    → CatchupBoundary source-reveal-boundary W Wᵖ

  boundary-source-conceal : ∀ {W Wᵖ Xᴸ? Xᴿ?}
    → ImpEnvMono W Wᵖ
    → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      ------------------------------------
    → CatchupBoundary source-conceal-boundary W Wᵖ

  boundary-target-reveal : ∀ {W Wᵖ Xᴿ?}
    → ImpEnvMono W Wᵖ
    → RebaseAtᴿ W Wᵖ Xᴿ?
      -----------------------------------
    → CatchupBoundary target-reveal-boundary W Wᵖ

  boundary-target-conceal : ∀ {W Wᵖ Xᴿ?}
    → ImpEnvMono W Wᵖ
    → RebaseAtᴿ Wᵖ W Xᴿ?
      -----------------------------------
    → CatchupBoundary target-conceal-boundary W Wᵖ


CatchupToMorePrecise : Set₁
CatchupToMorePrecise =
  ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → CatchupBoundary kind W Wᵖ
  → Wᵖ ∣ [] ⊢² V ⊑ M′ ∶ p
  → Value V
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ Wᵖ′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ boundary′ ∈ CatchupBoundary kind W′ Wᵖ′ ]
    Σ[ q ∈ A ⊑ᵂ⟨ Wᵖ′ ⟩ applyTys χsᴿ B ]
      (M′ —↠[ χsᴿ ] V′) × Value V′ ×
      ParkedEvolve Reduction.[] χsᴿ W W′ ×
      StructuralWorldExtendᴿ χsᴿ Wᵖ Wᵖ′ ×
      (Wᵖ′ ∣ [] ⊢² V ⊑ V′ ∶ q)
