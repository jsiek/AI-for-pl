module proof.DGG.GroundingMint where

-- File Charter:
--   * Documents the LG-2 minting surface for compile-preserves-imprecision².
--   * Records which compile-recursion worlds are target-occupied: initial
--     identity worlds occupy every center, matched type binders occupy the
--     fresh center, and source-only binders leave only their dynamic fresh
--     source center unoccupied.
--   * Reuses CompilePreservesImprecision2 for the compiled term-imprecision
--     theorem; this file only surfaces the occupancy facts around it.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Types
open import Consistency using (toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑X; X⊑★)
import proof.DGG.CtxImp as CTI2
open import proof.TypeInTermSubst using (toRename-id-eq)

------------------------------------------------------------------------
-- Initial compile world occupancy
------------------------------------------------------------------------

initialWorld-occupied : ∀ {Δ} {μ : ImpEnv Δ}
  → (Z : TyVar Δ)
  → CTI2.Occupied (CTI2.initialWorld μ) Z
initialWorld-occupied {μ = μ} Z =
  Z , trans
    (cong (λ η → toRenameᵗ η Z) (CTI2.initialWorld-ηᴿ μ))
    (toRename-id-eq Z)

initialWorld-no-see-through-empty : ∀ {Δ} {μ : ImpEnv Δ}
  → (X : TyVar Δ)
  → CTI2.NoTargetOccupantAtSource (CTI2.initialWorld μ) X
  → ⊥
initialWorld-no-see-through-empty {μ = μ} X no-target =
  no-target
    (initialWorld-occupied {μ = μ}
      (toRenameᵗ (CTI2.ηᴸʷ (CTI2.initialWorld μ)) X))

------------------------------------------------------------------------
-- Compile-recursion world image
------------------------------------------------------------------------

data CompileImageWorld : ∀ {Δᴸ Δᴿ Δ}
    → CTI2.World Δᴸ Δᴿ Δ
    → Set where
  compile-image-initial : ∀ {Δ}
      {μ : ImpEnv Δ}
      -------------------------------------------------
    → CompileImageWorld (CTI2.initialWorld μ)

  compile-image-liftBoth : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
    → CompileImageWorld W
      ---------------------------------------------------------
    → CompileImageWorld (CTI2.liftWorldBoth X⊑X W)

  compile-image-liftLeft : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
    → CompileImageWorld W
      ---------------------------------------------------------
    → CompileImageWorld (CTI2.liftWorldLeft W)

compile-image-target-occupied : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CompileImageWorld W
  → (Y : TyVar Δᴿ)
  → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴿʷ W) Y)
compile-image-target-occupied img Y = Y , refl

compile-image-precise-source-occupied : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CompileImageWorld W
  → (X : TyVar Δᴸ)
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑X
  → CTI2.Occupied W (toRenameᵗ (CTI2.ηᴸʷ W) X)
compile-image-precise-source-occupied
    (compile-image-initial {μ = μ}) X precise =
  initialWorld-occupied {μ = μ}
    (toRenameᵗ (CTI2.ηᴸʷ (CTI2.initialWorld μ)) X)
compile-image-precise-source-occupied (compile-image-liftBoth img)
    zero precise =
  zero , refl
compile-image-precise-source-occupied (compile-image-liftBoth img)
    (suc X) precise
    with compile-image-precise-source-occupied img X precise
compile-image-precise-source-occupied (compile-image-liftBoth img)
    (suc X) precise | Y , target-eq =
  suc Y , cong suc target-eq
compile-image-precise-source-occupied (compile-image-liftLeft img)
    zero ()
compile-image-precise-source-occupied (compile-image-liftLeft img)
    (suc X) precise
    with compile-image-precise-source-occupied img X precise
compile-image-precise-source-occupied (compile-image-liftLeft img)
    (suc X) precise | Y , target-eq =
  Y , cong suc target-eq

compile-image-source-only-fresh-no-target : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CompileImageWorld W
  → CTI2.NoTargetOccupantAtSource (CTI2.liftWorldLeft W) zero
compile-image-source-only-fresh-no-target img (Y , ())

compile-image-precise-see-through-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CompileImageWorld W
  → (X : TyVar Δᴸ)
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) X) ≡ X⊑X
  → CTI2.NoTargetOccupantAtSource W X
  → ⊥
compile-image-precise-see-through-empty img X precise no-target =
  no-target (compile-image-precise-source-occupied img X precise)

------------------------------------------------------------------------
-- Canonical minting connection
------------------------------------------------------------------------

-- The minting connection is the canonical
-- CPI2.compile-preserves-imprecision² theorem. Its image-side occupancy facts
-- are the theorems in this file: initialWorld-occupied, the CompileImageWorld
-- invariant, and the see-through emptiness theorems above.
