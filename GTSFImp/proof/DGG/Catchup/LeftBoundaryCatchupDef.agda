module proof.DGG.Catchup.LeftBoundaryCatchupDef where

-- File Charter:
--   * States boundary-general source catch-up for the less-precise target
--     value case.
--   * The source may reach a related value or blame; target store changes are
--     empty.
--   * Carries both enclosing-world and premise-world parked evolution so
--     source reveal/conceal boundaries can be replayed by proof workers.
--   * Contains no catch-up proof.

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
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
  using (mapPivotChanges)
open import proof.DGG.CatchupToMorePreciseDef
  using (CatchupBoundary; CatchupBoundaryKind)
open import proof.DGG.Parked.ParkedWorldDef
  using (ParkedEvolve; ParkedWorld)
open CTI2 using (World; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


LeftCatchupResult : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {kind : CatchupBoundaryKind}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {M : Term Δᴸ} {V′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → Set
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


CatchupToLessPreciseBoundary : Set
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
