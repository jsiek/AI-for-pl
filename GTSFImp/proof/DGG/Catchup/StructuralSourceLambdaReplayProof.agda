module proof.DGG.Catchup.StructuralSourceLambdaReplayProof where

-- File Charter:
--   * Replays ordinary and smart source-Λ rules at a structural endpoint.
--   * Consumes the caller's known target-normalization trace.

import Data.Fin as Fin
open import Data.Nat using (suc)

open import Types using (Ty; NonVar; _∈ᵗ_; `∀)
open import Imprecision using (X⊑★)
open import CastTerms using (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; Λ_)
open import Reduction using (StoreChanges; applyTys)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldLiftLeftProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftDef
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof


structural-Λ-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
    {U : Term (suc Δᴸ)} {F : Term Δᴿ′}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B}
    {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
  → Value U
  → ⟨ Δᴿ′ , CTI2.targetStoreʷ W′ ,
        CTI2.tgtCtxʷ
          (ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ) ⟩
      ⊢ F ⦂ applyTys χs B
  → CTI2.liftWorldLeft X⊑★ W′ CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ (structural-lift-left plan X⊑★)) γᴸ
      ⊢² U ⊑ F ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (structural-lift-left plan X⊑★)) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² Λ U ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-Λ-replay plan Anv z∈A liftγ vU F⊢ rel =
  CTI2.Λ⊑² Anv z∈A
    (mapCtxᴿ-liftCtxᴸ
      (structural-world-extendᴿ plan)
      (structural-world-extendᴿ (structural-lift-left plan X⊑★))
      liftγ)
    vU F⊢ rel (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)


structural-smart-Λ-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
    {U : Term (suc Δᴸ)} {F : Term Δᴿ′}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ B}
    {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → Value U
  → ⟨ Δᴿ′ , CTI2.targetStoreʷ W′ ,
        CTI2.tgtCtxʷ
          (ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ) ⟩
      ⊢ F ⦂ applyTys χs B
  → let child = structural-smart-liftᴸ plan liftW
        planᵐ = StructuralSmartLiftᴸResult.premise-plan child
     in StructuralSmartLiftᴸResult.Wᵐ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵐ) γᵐ
          ⊢² U ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵐ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² Λ U ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-smart-Λ-replay plan Anv z∈A liftW liftγ vU F⊢ rel
    with structural-smart-liftᴸ plan liftW
structural-smart-Λ-replay plan Anv z∈A liftW liftγ vU F⊢ rel
    | record { premise-plan = planᵐ ; post-lift = liftW′ } =
  CTI2.Λ⊑²-smart-comma Anv z∈A liftW′
    (mapCtxᴿ-smartLiftCtxᴸ
      (structural-world-extendᴿ plan)
      (structural-world-extendᴿ planᵐ) liftγ)
    vU F⊢ rel (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)
