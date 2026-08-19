module proof.DGG.notes.M5StructuralNamePostPlanScratch where

-- File Charter:
--   * Calibrates NS-4 stage 1b statement shapes for structural named
--     instantiation.
--   * Checks that source-wrapper recursion threads the caller's target trace
--     into premise worlds before replay.
--   * This notes-only module is not imported by All.agda.

open import Data.Maybe using (Maybe)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ＇_; `∀; _[_]ᵗ)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩; _↑_; _↓_)
open import Reduction using (StoreChanges; applyTys)
open import Imprecision using (X⊑★)
import Conversion as Conv
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.InstInversionDef using
  (InstSpineDescentPackage)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralInstantiationDescentDef using
  (StructuralInstantiationDescentPackage)
open import proof.DGG.Catchup.StructuralInstantiationDescentProof using
  (erase-structural-descent)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldLiftLeftProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralTargetSourceTransportProof
  using
    (structural-target-lift-left; structural-target-smart-lift-left;
     structural-target-rebase-left; structural-target-tag-rebase-left)
open import proof.DGG.Catchup.StructuralValueInstantiationCastProof
  using (structural-inert-cast-replay)
open import proof.DGG.Catchup.StructuralSourceLambdaReplayProof
  using (structural-Λ-replay; structural-smart-Λ-replay)
open import proof.DGG.Catchup.StructuralSourceRebaseReplayProof
  using (structural-reveal-replay; structural-conceal-replay)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)


StructuralFinalRelation : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (γ : CTI2.CtxImp W)
    (M : Term Δᴸ) {V : Term Δᴿ}
    {A : Ty Δᴸ} {B E : Ty Δᴿ}
    {spine : InstantiationSpine B E}
    (target : StructuralTargetInstantiationPackage W V spine)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) → Set
StructuralFinalRelation γ M target q =
  StructuralTargetInstantiationPackage.W′ target CTIR.∣
    ECR.mapCtxᴿ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      γ
    ⊢² M ⊑ StructuralTargetInstantiationPackage.final target ∶
      ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralTargetInstantiationPackage.structural-ext target))
        q


record StructuralNamePostPlan {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ) (E : Ty Δᴿ)
    (q : A CTI2.⊑ᵂ⟨ W ⟩ E) : Set₁ where
  inductive
  field
    cast-child : ∀ {A₀ : Ty Δᴸ} {ν : Env∼ Δᴸ}
      → ν ⊢ A₀ ∼ A
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ W ⟩ E ]
          StructuralNamePostPlan W A₀ E q₀

    plain-Λ-child : ∀ {A₀ : Ty (suc Δᴸ)}
      → A ≡ `∀ A₀
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ E ]
          StructuralNamePostPlan
            (CTI2.liftWorldLeft X⊑★ W) A₀ E q₀

    smart-Λ-child : ∀ {Δᵐ} {A₀ : Ty (suc Δᴸ)}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
      → A ≡ `∀ A₀
      → CTI2.SmartCommaLiftᴸ W Wᵐ
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵐ ⟩ E ]
          StructuralNamePostPlan Wᵐ A₀ E q₀

    reveal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ?}
        {c : Conv↑ Δᴸ A₀ A}
      → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀

    conceal-child : ∀ {A₀ : Ty Δᴸ} {Wᵖ Xᴸ? Xᴿ?}
        {c : Conv↓ Δᴸ A₀ A}
      → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → Σ[ q₀ ∈ A₀ CTI2.⊑ᵂ⟨ Wᵖ ⟩ E ]
          StructuralNamePostPlan Wᵖ A₀ E q₀


StructuralNameInstantiationPlanᵀ : Set₁
StructuralNameInstantiationPlanᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralNamePostPlan W A E q
  → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → StructuralFinalRelation γ M target q


postulate
  package-from-plan-worker : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {M : Term Δᴸ} {V : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
        {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
      → StructuralNamePostPlan W A E q
      → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
      → Value M
      → Value V
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralInstantiationDescentPackage W γ M V
          (name-type-app-frame B X refl refl ▻ⁱ spine) q

  plan-cast-cell : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {ν : Env∼ Δᴸ}
        {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → (plan : StructuralNamePostPlan W A′ E q)
      → (c : ν ⊢ A ∼ A′)
      → Inert c
      → W CTIR.∣ γ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ⟨ c ⟩) target q

  plan-plain-Λ-cell : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
        {U : Term (suc Δᴸ)} {V : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ `∀ B}
        {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
      → (plan : StructuralNamePostPlan W (`∀ A) E q)
      → NonVar A
      → Fin.zero ∈ᵗ A
      → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
      → CTI2.liftWorldLeft X⊑★ W CTIR.∣ γᴸ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (Λ U) target q

  plan-smart-Λ-cell : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ Δᵐ}
        {W : CTI2.World Δᴸ Δᴿ Δ}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
        {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
        {U : Term (suc Δᴸ)} {V : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ `∀ B}
        {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
      → (plan : StructuralNamePostPlan W (`∀ A) E q)
      → NonVar A
      → Fin.zero ∈ᵗ A
      → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
      → CTI2.SmartLiftCtxᴸ γ γᵐ
      → Wᵐ CTIR.∣ γᵐ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (Λ U) target q

  plan-reveal-cell : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ}
        {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ?}
        {c : Conv↑ Δᴸ A A′}
        {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → (plan : StructuralNamePostPlan W A′ E q)
      → CTI2.ImpEnvMono W Wᵖ
      → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
      → CTI2.SameCtx γ γᵖ
      → CTI2.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
      → Wᵖ CTIR.∣ γᵖ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ↑ c) target q

  plan-conceal-cell : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ}
        {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ? Xᴿ?}
        {c : Conv↓ Δᴸ A A′}
        {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → (plan : StructuralNamePostPlan W A′ E q)
      → CTI2.ImpEnvMono W Wᵖ
      → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
      → CTI2.SameCtx γ γᵖ
      → CTI2.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
      → CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? V
      → Wᵖ CTIR.∣ γᵖ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ↓ c) target q


StructuralNameInstantiationEndpointᵀ : Set₁
StructuralNameInstantiationEndpointᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → Σ[ q ∈ A CTI2.⊑ᵂ⟨ W ⟩ E ]
      StructuralFinalRelation γ M target q


EndpointRootContractᵀ : Set₁
EndpointRootContractᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → StructuralNameInstantiationEndpointᵀ
  → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → (target : StructuralTargetInstantiationPackage W V
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → InstSpineDescentPackage W γ M
      (applyInstantiationSpine V
        (name-type-app-frame B X refl refl ▻ⁱ spine)) q


postulate
  endpoint-cast-cell : StructuralNameInstantiationEndpointᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {ν : Env∼ Δᴸ}
        {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → (c : ν ⊢ A ∼ A′)
      → Inert c
      → W CTIR.∣ γ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ⟨ c ⟩) target q

  endpoint-plain-Λ-cell : StructuralNameInstantiationEndpointᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
        {U : Term (suc Δᴸ)} {V : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ `∀ B}
        {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
      → NonVar A
      → Fin.zero ∈ᵗ A
      → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
      → CTI2.liftWorldLeft X⊑★ W CTIR.∣ γᴸ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (Λ U) target q

  endpoint-smart-Λ-cell : StructuralNameInstantiationEndpointᵀ
    → ∀ {Δᴸ Δᴿ Δ Δᵐ}
        {W : CTI2.World Δᴸ Δᴿ Δ}
        {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
        {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
        {U : Term (suc Δᴸ)} {V : Term Δᴿ}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ `∀ B}
        {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
      → NonVar A
      → Fin.zero ∈ᵗ A
      → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
      → CTI2.SmartLiftCtxᴸ γ γᵐ
      → Wᵐ CTIR.∣ γᵐ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (Λ U) target q

  endpoint-reveal-cell : StructuralNameInstantiationEndpointᵀ
    → ∀ {Δᴸ Δᴿ Δ}
        {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ?}
        {c : Conv↑ Δᴸ A A′}
        {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → CTI2.ImpEnvMono W Wᵖ
      → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
      → CTI2.SameCtx γ γᵖ
      → CTI2.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
      → Wᵖ CTIR.∣ γᵖ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ↑ c) target q

  endpoint-conceal-cell : StructuralNameInstantiationEndpointᵀ
    → ∀ {Δᴸ Δᴿ Δ}
        {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
        {U : Term Δᴸ} {V : Term Δᴿ}
        {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ? Xᴿ?}
        {c : Conv↓ Δᴸ A A′}
        {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
        {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
      → CTI2.ImpEnvMono W Wᵖ
      → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
      → CTI2.SameCtx γ γᵖ
      → CTI2.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
      → CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? V
      → Wᵖ CTIR.∣ γᵖ ⊢² U ⊑ V ∶ p
      → Value U
      → (vV : Value V)
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → StructuralFinalRelation γ (U ↓ c) target q

  plan-root-contract : StructuralNameInstantiationPlanᵀ
    → ∀ {Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
        {γ : CTI2.CtxImp W}
        {M : Term Δᴸ} {V : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
        {E : Ty Δᴿ} {X : TyVar Δᴿ}
        {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
        {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
      → StructuralNamePostPlan W A E q
      → W CTIR.∣ γ ⊢² M ⊑ V ∶ p
      → Value M
      → Value V
      → AllValueView V
      → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
      → (target : StructuralTargetInstantiationPackage W V
          (name-type-app-frame B X refl refl ▻ⁱ spine))
      → InstSpineDescentPackage W γ M
          (applyInstantiationSpine V
            (name-type-app-frame B X refl refl ▻ⁱ spine)) q
