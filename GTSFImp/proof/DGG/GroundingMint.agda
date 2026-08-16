module proof.DGG.GroundingMint where

-- File Charter:
--   * States the LG-2 minting surface for compile-preserves-imprecision².
--   * Records which compile-recursion worlds are target-occupied: initial
--     identity worlds occupy every center, matched type binders occupy the
--     fresh center, and source-only binders leave only their dynamic fresh
--     source center unoccupied.
--   * Reuses CompilePreservesImprecision2 for the compiled term-imprecision
--     theorem; this file only surfaces the occupancy facts around it.

open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Types
open import TyStore using (TyStore)
open import Consistency using (toRenameᵗ)
open import Imprecision using (ImpEnv; X⊑X; X⊑★)
open import GradualTerms using (GTerm)
import GradualTermImprecision as GTI
open import Compile using (compile)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.CompilePreservesImprecision2 as CPI2
open import proof.TypeInTermSubst using (toRename-id-eq)

------------------------------------------------------------------------
-- Initial compile world occupancy
------------------------------------------------------------------------

initialWorld-occupied : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (Z : TyVar Δ)
  → CTI2.Occupied (CPI2.initialWorld μ Σ) Z
initialWorld-occupied Z = Z , toRename-id-eq Z

initialWorld-no-see-through-empty : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → (X : TyVar Δ)
  → CTI2.NoTargetOccupantAtSource (CPI2.initialWorld μ Σ) X
  → ⊥
initialWorld-no-see-through-empty {μ = μ} {Σ = Σ} X no-target =
  no-target
    (initialWorld-occupied {μ = μ} {Σ = Σ}
      (toRenameᵗ (CTI2.ηᴸʷ (CPI2.initialWorld μ Σ)) X))

------------------------------------------------------------------------
-- Compile-recursion world image
------------------------------------------------------------------------

data CompileImageWorld : ∀ {Δᴸ Δᴿ Δ}
    → CTI2.World Δᴸ Δᴿ Δ
    → Set where
  compile-image-initial : ∀ {Δ}
      {μ : ImpEnv Δ} {Σ : TyStore Δ}
      -------------------------------------------------
    → CompileImageWorld (CPI2.initialWorld μ Σ)

  compile-image-liftBoth : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
    → CompileImageWorld W
      ---------------------------------------------------------
    → CompileImageWorld (CTI2.liftWorldBoth X⊑X W)

  compile-image-liftLeft : ∀ {Δᴸ Δᴿ Δ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
    → CompileImageWorld W
      ---------------------------------------------------------
    → CompileImageWorld (CTI2.liftWorldLeft X⊑★ W)

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
    (compile-image-initial {μ = μ} {Σ = Σ}) X precise =
  initialWorld-occupied {μ = μ} {Σ = Σ}
    (toRenameᵗ (CTI2.ηᴸʷ (CPI2.initialWorld μ Σ)) X)
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
  → CTI2.NoTargetOccupantAtSource (CTI2.liftWorldLeft X⊑★ W) zero
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
-- Minting theorem
------------------------------------------------------------------------

compile-mints-cti² : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
    {γ : GTI.CtxImp μ} {M M′ : GTerm Δ} {A B p}
  → (M⊑M′ : μ GTI.∣ γ ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p)
  → CPI2.initialWorld μ Σ ∣ CPI2.initialCtx {Σ = Σ} γ ⊢²
      proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-source-typing M⊑M′))
      ⊑ proj₁ (compile {Σ = Σ}
        (GTI.gradual-term-imprecision-target-typing M⊑M′))
      ∶ CPI2.initial-⊑ {Σ = Σ} p
compile-mints-cti² =
  CPI2.compile-preserves-imprecision²

compile-minting-initial-image : ∀ {Δ}
    {μ : ImpEnv Δ} {Σ : TyStore Δ}
  → CompileImageWorld (CPI2.initialWorld μ Σ)
compile-minting-initial-image = compile-image-initial
