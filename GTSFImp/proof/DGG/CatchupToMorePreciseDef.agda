module proof.DGG.CatchupToMorePreciseDef where

-- File Charter:
--   * States target catch-up relative to an enclosing parked world.
--   * The active relation may live at that world or across a source reveal or
--     conceal boundary; catch-up evolves both worlds and replays the boundary.
--   * Boundary indices preserve the source pivot and map the target pivot
--     through the target store-change trace.
--   * ValueCatchupResult exposes the related target value together with the
--     structural histories for the enclosing and premise worlds.
--   * The less precise target reaches a related value, with no blame case.
--   * Contains no catch-up proof.

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar)
open import CastTerms using (Term; Value)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.Catchup.StructuralWorldExtendDef
  using (StructuralWorldExtendᴿ)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
  using (mapPivotChanges)
open CTI2 using
  ( World
  ; ImpEnvMono
  ; RebaseAtᴸ
  ; RebaseAtᴿ
  ; TagRebaseAtᴸ
  ; rebase-idᴸ
  ; rebase-varᴸ
  ; rebase-onlyᴸ
  ; rebase-idᴿ
  ; rebase-varᴿ
  ; tag-rebase-idᴸ
  ; tag-rebase-varᴸ
  ; tag-rebase-onlyᴸ
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


data CatchupBoundaryKind : Set where
  same-boundary : CatchupBoundaryKind
  source-reveal-boundary : CatchupBoundaryKind
  source-conceal-boundary : CatchupBoundaryKind
  target-reveal-boundary : CatchupBoundaryKind
  target-conceal-boundary : CatchupBoundaryKind


targetPivotᴸ : ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ?}
  → RebaseAtᴸ W Wᵖ Xᴸ?
  → Maybe (TyVar Δᴿ)
targetPivotᴸ rebase-idᴸ = nothing
targetPivotᴸ (rebase-varᴸ {Xᴿ = Xᴿ} rebase) = just Xᴿ
targetPivotᴸ (rebase-onlyᴸ to-star disaligned represented) = nothing


sourcePivotᴿ : ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ} {Xᴿ?}
  → RebaseAtᴿ W Wᵖ Xᴿ?
  → Maybe (TyVar Δᴸ)
sourcePivotᴿ rebase-idᴿ = nothing
sourcePivotᴿ (rebase-varᴿ {Xᴸ = Xᴸ} rebase) = just Xᴸ


toTagRebaseAtᴸ : ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (rebase : RebaseAtᴸ W Wᵖ Xᴸ?)
  → TagRebaseAtᴸ W Wᵖ Xᴸ? (targetPivotᴸ rebase)
toTagRebaseAtᴸ rebase-idᴸ = tag-rebase-idᴸ
toTagRebaseAtᴸ (rebase-varᴸ rebase) = tag-rebase-varᴸ rebase
toTagRebaseAtᴸ (rebase-onlyᴸ to-star disaligned represented) =
  tag-rebase-onlyᴸ to-star disaligned represented


toTagRebaseAtᴿ : ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ} {Xᴿ?}
  → (rebase : RebaseAtᴿ W Wᵖ Xᴿ?)
  → TagRebaseAtᴸ W Wᵖ (sourcePivotᴿ rebase) Xᴿ?
toTagRebaseAtᴿ rebase-idᴿ = tag-rebase-idᴸ
toTagRebaseAtᴿ (rebase-varᴿ rebase) = tag-rebase-varᴸ rebase


data CatchupBoundary {Δᴸ Δᴿ Δ} :
    CatchupBoundaryKind →
    Maybe (TyVar Δᴸ) → Maybe (TyVar Δᴿ) →
    World Δᴸ Δᴿ Δ → World Δᴸ Δᴿ Δ → Set where

  boundary-refl : ∀ {W}
      -------------------------------
    → CatchupBoundary same-boundary nothing nothing W W

  boundary-source-reveal : ∀ {W Wᵖ Xᴸ? Xᴿ?}
    → ImpEnvMono W Wᵖ
    → TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
      -----------------------------------
    → CatchupBoundary source-reveal-boundary Xᴸ? Xᴿ? W Wᵖ

  boundary-source-conceal : ∀ {W Wᵖ Xᴸ? Xᴿ?}
    → ImpEnvMono W Wᵖ
    → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      ------------------------------------
    → CatchupBoundary source-conceal-boundary Xᴸ? Xᴿ? W Wᵖ

  boundary-target-reveal : ∀ {W Wᵖ Xᴸ? Xᴿ?}
    → ImpEnvMono W Wᵖ
    → TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
      -----------------------------------
    → CatchupBoundary target-reveal-boundary Xᴸ? Xᴿ? W Wᵖ

  boundary-target-conceal : ∀ {W Wᵖ Xᴸ? Xᴿ?}
    → ImpEnvMono W Wᵖ
    → TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      -----------------------------------
    → CatchupBoundary target-conceal-boundary Xᴸ? Xᴿ? W Wᵖ


ValueCatchupResult : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → Set₁
ValueCatchupResult {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {W = W} {Wᵖ = Wᵖ}
    {kind = kind}
    {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?} {V = V} {M′ = M′}
    {A = A} {B = B} =
  Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χsᴿ ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ V′ ∈ Term Δᴿ′ ] Σ[ Δ′ ∈ TyCtx ]
    Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ Wᵖ′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ Xᴿ′? ∈ Maybe (TyVar Δᴿ′) ]
    Σ[ boundary′ ∈ CatchupBoundary kind Xᴸ? Xᴿ′? W′ Wᵖ′ ]
    Σ[ q ∈ A ⊑ᵂ⟨ Wᵖ′ ⟩ applyTys χsᴿ B ]
      Xᴿ′? ≡ mapPivotChanges χsᴿ Xᴿ? ×
      (M′ —↠[ χsᴿ ] V′) × Value V′ ×
      ParkedEvolve Reduction.[] χsᴿ W W′ ×
      StructuralWorldExtendᴿ χsᴿ W W′ ×
      StructuralWorldExtendᴿ χsᴿ Wᵖ Wᵖ′ ×
      (Wᵖ′ ∣ [] ⊢² V ⊑ V′ ∶ q)


CatchupToMorePrecise : Set₁
CatchupToMorePrecise =
  ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → CatchupBoundary kind Xᴸ? Xᴿ? W Wᵖ
  → Wᵖ ∣ [] ⊢² V ⊑ M′ ∶ p
  → Value V
  → ValueCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = kind}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {V = V} {M′ = M′} {A = A} {B = B}
