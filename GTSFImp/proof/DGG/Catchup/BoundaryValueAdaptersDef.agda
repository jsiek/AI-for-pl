module proof.DGG.Catchup.BoundaryValueAdaptersDef where

-- File Charter:
--   * States provenance factories for transporting structural target
--     extensions across an enclosing source boundary.
--   * Keeps forward and backward tag-rebase replay distinct.
--   * Contains no catch-up or replay proof.

open import Data.List using ([])
open import Data.Maybe using (Maybe)

open import Types using (Ty; TyVar)
open import CastTerms using (Term; Value)
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open import proof.DGG.Parked.ParkedWorldDef using (ParkedWorld)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef using
  (StructuralTagRebaseAtᴸReplay;
   StructuralTagRebaseAtᴸPullbackReplay)
open import proof.DGG.Catchup.StructuralCatchupRightDef using
  (StructuralCatchupRightResult)


StructuralForwardBoundaryReplayFactory : Set₁
StructuralForwardBoundaryReplayFactory =
  ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?)
  → (rel : Wᵖ CTI2.∣ [] ⊢² V ⊑ M′ ∶ p)
  → Value V
  → (child : StructuralCatchupRightResult Wᵖ [] V M′ p)
  → StructuralTagRebaseAtᴸReplay
      (StructuralCatchupRightResult.structural-ext child) rb


StructuralBackwardBoundaryReplayFactory : Set₁
StructuralBackwardBoundaryReplayFactory =
  ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {V : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
  → ParkedWorld W
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → (rel : Wᵖ CTI2.∣ [] ⊢² V ⊑ M′ ∶ p)
  → Value V
  → (child : StructuralCatchupRightResult Wᵖ [] V M′ p)
  → StructuralTagRebaseAtᴸPullbackReplay
      (StructuralCatchupRightResult.structural-ext child) rb
