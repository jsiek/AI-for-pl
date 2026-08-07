module proof.DGG.Parked.ParkedWorldDef where

-- File Charter:
--   * Defines parked worlds as the initial compile worlds closed under
--     paired, source-only, and target-only parked allocation.
--   * Defines two-sided parked evolution indexed by source and target
--     store-change traces.
--   * States the transport, geometry, and right-extension bridge theorems
--     consumed by later DGG proof tracks.

open import Data.Empty using (⊥)
open import Data.Fin using (zero)
import Data.Fin as Fin
import Data.Nat as Nat
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types using (Ty; TyCtx; TyVar)
open import TyStore using (TyStore)
open import Consistency using (toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑X; X⊑★)
open import Reduction using (StoreChanges; []; _∷_; keep; bind)
import Reduction as R
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.ExtraCastRight2 as ECR

open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_)


infixl 7 _▶ᵛ_

_▶ᵛ_ : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → TyVar Δ
  → TyVar Δ′
[] ▶ᵛ X = X
(χ ∷ χs) ▶ᵛ X = χs ▶ᵛ (R.applyVar χ X)


data ParkedWorld : ∀ {Δᴸ Δᴿ Δ}
    → World Δᴸ Δᴿ Δ
    → Set where

  parked-initial : ∀ {Δ} {μ : ImpEnv Δ} {Σ : TyStore Δ}
      -----------------------------------
    → ParkedWorld (CPI2.initialWorld μ Σ)

  parked-both-bind : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    → ParkedWorld W
      ----------------------------------------------------------
    → ParkedWorld (CTI2.bothBindWorld X⊑X W A B)

  parked-left-bind : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ}
    → ParkedWorld W
      ------------------------------------------------
    → ParkedWorld (CTI2.leftOnlyWorld X⊑★ W A)

  parked-right-bind : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    → ParkedWorld W
      -----------------------------------------------
    → ParkedWorld (CTI2.rightOnlyWorld W B)


data ParkedEvolve : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    → StoreChanges Δᴸ Δᴸ′
    → StoreChanges Δᴿ Δᴿ′
    → World Δᴸ Δᴿ Δ
    → World Δᴸ′ Δᴿ′ Δ′
    → Set where

  evolve-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
      --------------------------
    → ParkedEvolve [] [] W W

  evolve-keepᴸ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
      {χsᴸ : StoreChanges Δᴸ Δᴸ′}
      {χsᴿ : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    → ParkedEvolve χsᴸ χsᴿ W W′
      ---------------------------------------------
    → ParkedEvolve (keep ∷ χsᴸ) χsᴿ W W′

  evolve-keepᴿ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
      {χsᴸ : StoreChanges Δᴸ Δᴸ′}
      {χsᴿ : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    → ParkedEvolve χsᴸ χsᴿ W W′
      ---------------------------------------------
    → ParkedEvolve χsᴸ (keep ∷ χsᴿ) W W′

  evolve-both-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
      {χsᴸ : StoreChanges (Nat.suc Δᴸ) Δᴸ′}
      {χsᴿ : StoreChanges (Nat.suc Δᴿ) Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W′ : World Δᴸ′ Δᴿ′ Δ′}
      {A : Ty Δᴸ} {B : Ty Δᴿ}
    → ParkedEvolve χsᴸ χsᴿ
        (CTI2.bothBindWorld X⊑X W A B) W′
      ---------------------------------------------------
    → ParkedEvolve (bind A ∷ χsᴸ) (bind B ∷ χsᴿ) W W′

  evolve-left-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
      {χsᴸ : StoreChanges (Nat.suc Δᴸ) Δᴸ′}
      {χsᴿ : StoreChanges Δᴿ Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W′ : World Δᴸ′ Δᴿ′ Δ′}
      {A : Ty Δᴸ}
    → ParkedEvolve χsᴸ χsᴿ (CTI2.leftOnlyWorld X⊑★ W A) W′
      ---------------------------------------------
    → ParkedEvolve (bind A ∷ χsᴸ) χsᴿ W W′

  evolve-right-bind : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
      {χsᴸ : StoreChanges Δᴸ Δᴸ′}
      {χsᴿ : StoreChanges (Nat.suc Δᴿ) Δᴿ′}
      {W : World Δᴸ Δᴿ Δ}
      {W′ : World Δᴸ′ Δᴿ′ Δ′}
      {B : Ty Δᴿ}
    → ParkedEvolve χsᴸ χsᴿ (CTI2.rightOnlyWorld W B) W′
      ---------------------------------------------
    → ParkedEvolve χsᴸ (bind B ∷ χsᴿ) W W′


centerVarᴾ : ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → ParkedEvolve χsᴸ χsᴿ W W′
  → TyVar Δ
  → TyVar Δ′
centerVarᴾ evolve-refl Z = Z
centerVarᴾ (evolve-keepᴸ evol) Z = centerVarᴾ evol Z
centerVarᴾ (evolve-keepᴿ evol) Z = centerVarᴾ evol Z
centerVarᴾ (evolve-both-bind evol) Z = centerVarᴾ evol (Fin.suc Z)
centerVarᴾ (evolve-left-bind evol) Z = centerVarᴾ evol (Fin.suc Z)
centerVarᴾ (evolve-right-bind evol) Z = centerVarᴾ evol (Fin.suc Z)


ParkedWorldClosedᵀ : Set
ParkedWorldClosedᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → ParkedWorld W
  → ParkedEvolve χsᴸ χsᴿ W W′
  → ParkedWorld W′


Transport⊑ᴾᵀ : Set
Transport⊑ᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → ParkedEvolve χsᴸ χsᴿ W W′
  → A ⊑ᵂ⟨ W ⟩ B
  → R.applyTys χsᴸ A ⊑ᵂ⟨ W′ ⟩ R.applyTys χsᴿ B


MapCtxᴾᵀ : Set
MapCtxᴾᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → ParkedEvolve χsᴸ χsᴿ W W′
  → CtxImp W
  → CtxImp W′


ParkedTargetStableᵀ : Set
ParkedTargetStableᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
  → (evol : ParkedEvolve χsᴸ χsᴿ W W′)
  → (Y : TyVar Δᴿ)
  → toRenameᵗ (CTI2.ηᴿʷ W′) (χsᴿ ▶ᵛ Y)
      ≡ centerVarᴾ evol (toRenameᵗ (CTI2.ηᴿʷ W) Y)


ParkedTargetIdentityᵀ : Set
ParkedTargetIdentityᵀ =
  ∀ {Δᴸ Δ} {W : World Δᴸ Δ Δ}
  → ParkedWorld W
  → (Y : TyVar Δ)
  → toRenameᵗ (CTI2.ηᴿʷ W) Y ≡ Y


ParkedFreshBothᴸᵀ : Set
ParkedFreshBothᴸᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges (Nat.suc Δᴸ) Δᴸ′}
    {χsᴿ : StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (evol : ParkedEvolve χsᴸ χsᴿ
      (CTI2.bothBindWorld X⊑X W A B) W′
    )
  → toRenameᵗ (CTI2.ηᴸʷ W′) (χsᴸ ▶ᵛ zero)
      ≡ centerVarᴾ evol zero


ParkedFreshBothᴿᵀ : Set
ParkedFreshBothᴿᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges (Nat.suc Δᴸ) Δᴸ′}
    {χsᴿ : StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (evol : ParkedEvolve χsᴸ χsᴿ
      (CTI2.bothBindWorld X⊑X W A B) W′
    )
  → toRenameᵗ (CTI2.ηᴿʷ W′) (χsᴿ ▶ᵛ zero)
      ≡ centerVarᴾ evol zero


ParkedFreshRightᴿᵀ : Set
ParkedFreshRightᴿᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges Δᴸ Δᴸ′}
    {χsᴿ : StoreChanges (Nat.suc Δᴿ) Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {B : Ty Δᴿ}
  → (evol : ParkedEvolve χsᴸ χsᴿ (CTI2.rightOnlyWorld W B) W′)
  → toRenameᵗ (CTI2.ηᴿʷ W′) (χsᴿ ▶ᵛ zero)
      ≡ centerVarᴾ evol zero


ParkedFreshLeftᴸᵀ : Set
ParkedFreshLeftᴸᵀ =
  ∀ {Δᴸ Δᴸ′ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴸ : StoreChanges (Nat.suc Δᴸ) Δᴸ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ′ Δᴿ′ Δ′}
    {A : Ty Δᴸ}
  → (evol : ParkedEvolve χsᴸ χsᴿ (CTI2.leftOnlyWorld X⊑★ W A) W′)
  → toRenameᵗ (CTI2.ηᴸʷ W′) (χsᴸ ▶ᵛ zero)
      ≡ centerVarᴾ evol zero


ParkedFreshZeroᵀ : Set
ParkedFreshZeroᵀ =
  ParkedFreshBothᴸᵀ × ParkedFreshBothᴿᵀ ×
  ParkedFreshLeftᴸᵀ × ParkedFreshRightᴿᵀ


ParkedNoCrossingᵀ : Set
ParkedNoCrossingᵀ =
  ∀ {Δᴸ Δ}
    {W W′ : World Δᴸ Δ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δ}
  → ParkedWorld W
  → ParkedWorld W′
  → CTI2.RebaseAt W′ W Xᴸ Xᴿ
  → toRenameᵗ (CTI2.ηᴿʷ W′) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
  → ⊥


RightOnlyParked→WorldExtendᴿᵀ : Set
RightOnlyParked→WorldExtendᴿᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ParkedEvolve [] χsᴿ W W′
  → ECR.WorldExtendᴿ χsᴿ W W′


WorldExtendᴿ→RightOnlyParkedᵀ : Set
WorldExtendᴿ→RightOnlyParkedᵀ =
  ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χsᴿ : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ} {W′ : World Δᴸ Δᴿ′ Δ′}
  → ECR.WorldExtendᴿ χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′
  → ParkedEvolve [] χsᴿ W W′
