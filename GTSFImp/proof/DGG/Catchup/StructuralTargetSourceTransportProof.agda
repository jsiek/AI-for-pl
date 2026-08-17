module proof.DGG.Catchup.StructuralTargetSourceTransportProof where

-- File Charter:
--   * Transports completed target packages through source-only world changes.
--   * Keeps the target reduction and final value unchanged.

open import Data.Nat using (suc)

open import Types using (Ty)
open import Imprecision using (VarImp)
open import CastTerms using (Term)
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftDef
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralWorldLiftLeftProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef


structural-target-lift-left : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {V : Term Δᴿ}
    {B E : Ty Δᴿ} {spine : InstantiationSpine B E}
  → (v : VarImp)
  → StructuralTargetInstantiationPackage W V spine
  → StructuralTargetInstantiationPackage (CTI2.liftWorldLeft v W)
      V spine
structural-target-lift-left v pkg = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ pkg
  ; χs = StructuralTargetInstantiationPackage.χs pkg
  ; Δ′ = suc (StructuralTargetInstantiationPackage.Δ′ pkg)
  ; W′ = CTI2.liftWorldLeft v
      (StructuralTargetInstantiationPackage.W′ pkg)
  ; structural-ext = structural-lift-left
      (StructuralTargetInstantiationPackage.structural-ext pkg) v
  ; final = StructuralTargetInstantiationPackage.final pkg
  ; final-value = StructuralTargetInstantiationPackage.final-value pkg
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction pkg
  }


structural-target-smart-lift-left : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {V : Term Δᴿ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → StructuralTargetInstantiationPackage W V spine
  → StructuralTargetInstantiationPackage Wᵐ V spine
structural-target-smart-lift-left liftW pkg
    with structural-smart-liftᴸ
      (StructuralTargetInstantiationPackage.structural-ext pkg) liftW
structural-target-smart-lift-left liftW pkg
    | record { premise-plan = planᵐ } = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ pkg
  ; χs = StructuralTargetInstantiationPackage.χs pkg
  ; Δ′ = _
  ; W′ = _
  ; structural-ext = planᵐ
  ; final = StructuralTargetInstantiationPackage.final pkg
  ; final-value = StructuralTargetInstantiationPackage.final-value pkg
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction pkg
  }


structural-target-rebase-left : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ?} {V : Term Δᴿ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → StructuralTargetInstantiationPackage W V spine
  → StructuralTargetInstantiationPackage Wᵖ V spine
structural-target-rebase-left rb pkg
    with structural-rebase-atᴸ
      (StructuralTargetInstantiationPackage.structural-ext pkg) rb
structural-target-rebase-left rb pkg
    | record { premise-plan = planᵖ } = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ pkg
  ; χs = StructuralTargetInstantiationPackage.χs pkg
  ; Δ′ = _
  ; W′ = _
  ; structural-ext = planᵖ
  ; final = StructuralTargetInstantiationPackage.final pkg
  ; final-value = StructuralTargetInstantiationPackage.final-value pkg
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction pkg
  }


structural-target-tag-rebase-left : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? Xᴿ?} {V : Term Δᴿ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
  → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → StructuralTargetInstantiationPackage W V spine
  → StructuralTargetInstantiationPackage Wᵖ V spine
structural-target-tag-rebase-left rb pkg
    with structural-tag-rebase-atᴸ
      (StructuralTargetInstantiationPackage.structural-ext pkg) rb
structural-target-tag-rebase-left rb pkg
    | record { premise-plan = planᵖ } = record
  { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ pkg
  ; χs = StructuralTargetInstantiationPackage.χs pkg
  ; Δ′ = _
  ; W′ = _
  ; structural-ext = planᵖ
  ; final = StructuralTargetInstantiationPackage.final pkg
  ; final-value = StructuralTargetInstantiationPackage.final-value pkg
  ; post-reduction =
      StructuralTargetInstantiationPackage.post-reduction pkg
  }
