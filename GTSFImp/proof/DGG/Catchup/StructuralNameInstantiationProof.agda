module proof.DGG.Catchup.StructuralNameInstantiationProof where

-- File Charter:
--   * Implements the structural worker for named target instantiation.
--   * Uses cast mass as the primary accessibility measure.
--   * Replays source wrappers only after target normalization is known.

import Data.Fin as Fin
import Data.List as List
open import Data.Nat using (suc; _<_)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar; NonVar; _∈ᵗ_; ＇_; `∀; _[_]ᵗ)
open import Imprecision using (X⊑★)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩; _↑_; _↓_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastProof
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetSourceTransportProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralSourceLambdaReplayProof
open import proof.DGG.Catchup.StructuralSourceRebaseReplayProof
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


StructuralNameInstantiationAccᵀ : Set₁
StructuralNameInstantiationAccᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralNamePostPlan W A E q
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → (vV : Value V)
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → Acc _<_ (pendingCastMass vV
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralTargetInstantiationPackage.W′ target CTI2.∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        γ
      ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          q


StructuralNameInstantiationEqualᵀ : Set₁
StructuralNameInstantiationEqualᵀ =
  StructuralNameInstantiationAccᵀ


StructuralNameInstantiationStrictᵀ : Set₁
StructuralNameInstantiationStrictᵀ =
  StructuralNameInstantiationAccᵀ


liftCtxᴸ-target-ctx : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft v W)}
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.tgtCtxʷ γ′ ≡ CTI2.tgtCtxʷ γ
liftCtxᴸ-target-ctx CTI2.liftᴸ-[] = refl
liftCtxᴸ-target-ctx (CTI2.liftᴸ-∷ liftγ) =
  cong (_ List.∷_) (liftCtxᴸ-target-ctx liftγ)


structural-name-cast-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {U V : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {ν : Env∼ Δᴸ}
      {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
      {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
    → (plan : StructuralNamePostPlan W A′ E q)
    → (c : ν ⊢ A ∼ A′)
    → Inert c
    → W CTI2.∣ γ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² U ⟨ c ⟩ ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-cast-equal worker plan c inert prem vU vN view spine
    acc target
    with StructuralNamePostPlan.cast-child plan c
structural-name-cast-equal worker plan c inert prem vU vN view spine
    acc target | q₀ , child-plan =
  structural-inert-cast-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    c inert
    (worker child-plan prem vU vN view spine acc target)


structural-name-plain-Λ-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
      {U : Term (suc Δᴸ)} {N : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
      {p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ `∀ B}
      {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
    → (plan : StructuralNamePostPlan W (`∀ A) E q)
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
    → CTI2.liftWorldLeft X⊑★ W CTI2.∣ γᴸ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² Λ U ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-plain-Λ-equal worker {γ = γ} {γᴸ = γᴸ}
    plan Anv z∈A liftγ prem vU vN view spine acc target
    with StructuralNamePostPlan.plain-Λ-child plan refl
structural-name-plain-Λ-equal worker {γ = γ} {γᴸ = γᴸ}
    plan Anv z∈A liftγ prem vU vN view spine acc target
    | q₀ , child-plan =
  structural-Λ-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    Anv z∈A liftγ vU target⊢ child-rel
  where
  targetᴸ = structural-target-lift-left X⊑★ target

  child-rel =
    worker child-plan prem vU vN view spine acc targetᴸ

  liftγ′ =
    mapCtxᴿ-liftCtxᴸ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext targetᴸ))
      liftγ

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (liftCtxᴸ-target-ctx liftγ′)
      (CTI2T.target-typing² child-rel)


structural-name-reveal-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {Δᴸ Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
      {U : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ?}
      {c : Conv↑ Δᴸ A A′}
      {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
      {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
    → (plan : StructuralNamePostPlan W A′ E q)
    → CTI2.ImpEnvMono W Wᵖ
    → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
    → Wᵖ CTI2.∣ γᵖ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² U ↑ c ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-reveal-equal worker {c = c} plan mono rb sc c⊢
    prem vU vN view spine acc target
    with StructuralNamePostPlan.reveal-child plan {c = c} rb
structural-name-reveal-equal worker {c = c} plan mono rb sc c⊢
    prem vU vN view spine acc target | q₀ , child-plan =
  structural-reveal-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    mono rb sc c⊢
    (worker child-plan prem vU vN view spine acc
      (structural-target-rebase-left rb target))
