T9 proposal: boundary-general left catch-up surface

Date: 2026-08-17

Reason
------

`CatchupToLessPrecise` is fixed and must remain the public top-down DGG
surface.  Its current statement has only one world:

  ParkedWorld W
  W ∣ [] ⊢² M ⊑ V′ ∶ p
  Value V′

Target-only reveal/conceal CTI2 heads immediately expose a premise relation in
a different rebase world:

  ⊑reveal²  : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p -> W ∣ γ ⊢² M ⊑ M′ ↑ c′ ∶ q
  ⊑conceal² : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p -> W ∣ γ ⊢² M ⊑ M′ ↓ c′ ∶ q

`ParkedEvolve` records store changes, not zero-store rebasing.  Therefore a
recursive call directly at `W′` cannot produce the required evolution from
the enclosing `W`.  The right-side surface solves this with
`CatchupBoundary`; the left proof needs the same boundary shape but with
source-store evolution and a blame branch.

Before context
--------------

Existing public surface:

```agda
CatchupToLessPrecise : Set
CatchupToLessPrecise =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ B}
  → ParkedWorld W
  → W ∣ [] ⊢² M ⊑ V′ ∶ p
  → Value V′
  → ...
```

Existing right boundary result:

```agda
ValueCatchupResult
  {W = W} {Wᵖ = Wᵖ}
  {kind = kind} {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
```

It evolves target pivots with:

```agda
Xᴿ′? ≡ mapPivotChanges χsᴿ Xᴿ?
```

After context
-------------

Add a new Def module, for example:

  `proof/DGG/Catchup/LeftBoundaryCatchupDef.agda`

It may import the existing `CatchupBoundary` and `CatchupBoundaryKind` from
`CatchupToMorePreciseDef.agda`; no public Def file has to change.

Proposed statement
------------------

```agda
module proof.DGG.Catchup.LeftBoundaryCatchupDef where

open import Data.List using ([])
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; Σ-syntax)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types using (Ty; TyCtx; TyVar)
open import CastTerms using (Term; Value; blame)
open import Reduction using (StoreChanges; applyTys; _—↠[_]_)
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedWorld; ParkedEvolve)
open import proof.DGG.Catchup.StructuralWorldExtendDef
  using (mapPivotChanges)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupBoundaryKind; CatchupBoundary)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

LeftCatchupResult : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → Set₁
LeftCatchupResult {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {W = W} {Wᵖ = Wᵖ}
    {kind = kind} {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
    {M = M} {V′ = V′} {A = A} {B = B} =
  (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
   Σ[ V ∈ Term Δᴸ′ ] Σ[ Δ′ ∈ TyCtx ]
   Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
   Σ[ Wᵖ′ ∈ World Δᴸ′ Δᴿ Δ′ ]
   Σ[ Xᴸ′? ∈ Maybe (TyVar Δᴸ′) ]
   Σ[ boundary′ ∈ CatchupBoundary kind Xᴸ′? Xᴿ? W′ Wᵖ′ ]
   Σ[ q ∈ applyTys χsᴸ A ⊑ᵂ⟨ Wᵖ′ ⟩ B ]
     Xᴸ′? ≡ mapPivotChanges χsᴸ Xᴸ? ×
     (M —↠[ χsᴸ ] V) × Value V ×
     ParkedEvolve χsᴸ R.[] W W′ ×
     ParkedEvolve χsᴸ R.[] Wᵖ Wᵖ′ ×
     (Wᵖ′ ∣ [] ⊢² V ⊑ V′ ∶ q))
  ⊎
  (Σ[ Δᴸ′ ∈ TyCtx ] Σ[ χsᴸ ∈ StoreChanges Δᴸ Δᴸ′ ]
   Σ[ Δ′ ∈ TyCtx ]
   Σ[ W′ ∈ World Δᴸ′ Δᴿ Δ′ ]
   Σ[ Wᵖ′ ∈ World Δᴸ′ Δᴿ Δ′ ]
   Σ[ Xᴸ′? ∈ Maybe (TyVar Δᴸ′) ]
   Σ[ boundary′ ∈ CatchupBoundary kind Xᴸ′? Xᴿ? W′ Wᵖ′ ]
     Xᴸ′? ≡ mapPivotChanges χsᴸ Xᴸ? ×
     (M —↠[ χsᴸ ] blame) ×
     ParkedEvolve χsᴸ R.[] W W′ ×
     ParkedEvolve χsᴸ R.[] Wᵖ Wᵖ′)

CatchupToLessPreciseBoundary : Set₁
CatchupToLessPreciseBoundary =
  ∀ {Δᴸ Δᴿ Δ} {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A ⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → CatchupBoundary kind Xᴸ? Xᴿ? W Wᵖ
  → Wᵖ ∣ [] ⊢² M ⊑ V′ ∶ p
  → Value V′
  → LeftCatchupResult
      {W = W} {Wᵖ = Wᵖ} {kind = kind}
      {Xᴸ? = Xᴸ?} {Xᴿ? = Xᴿ?}
      {M = M} {V′ = V′} {A = A} {B = B}
```

Notes
-----

The result carries `ParkedEvolve` for both the enclosing world and premise
world.  This is intentionally stronger than the right public result because
there is no left analogue of `StructuralWorldExtendᴿ` today.

If later a structural left extension is introduced, this result can be
strengthened internally and erased to the same public `CatchupToLessPrecise`
surface.

Adapter to the fixed public surface
-----------------------------------

```agda
left-boundary-catchup→catchup-to-less-precise :
  CatchupToLessPreciseBoundary → CatchupToLessPrecise
```

The adapter instantiates `kind = same-boundary`,
`Xᴸ? = nothing`, `Xᴿ? = nothing`, `Wᵖ = W`, and
`boundary = boundary-refl`, then erases `Wᵖ′` and `boundary′`.
