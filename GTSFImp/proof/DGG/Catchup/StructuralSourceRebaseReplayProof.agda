module proof.DGG.Catchup.StructuralSourceRebaseReplayProof where

-- File Charter:
--   * Replays source reveal and conceal at structural trace endpoints.
--   * Uses transformed rebases, contexts, typing, and monotonicity evidence.

open import Data.Maybe using (Maybe; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to subst≡)
open import Types using (Ty; TyVar)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; _↑_; _↓_)
open import Reduction using (StoreChanges)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof
open import proof.DGG.Catchup.StructuralTermProvenanceDef
open import proof.DGG.Catchup.StructuralTermReplayProof

mapPivotChanges-nothing-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTX.World Δᴸ Δᴿ Δ} {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
  → StructuralWorldExtendᴿ χs W W′
  → mapPivotChanges χs nothing ≡ nothing
mapPivotChanges-nothing-replay structural-[] = refl
mapPivotChanges-nothing-replay (structural-keep plan) =
  mapPivotChanges-nothing-replay plan
mapPivotChanges-nothing-replay (structural-bind ins follows plan) =
  mapPivotChanges-nothing-replay plan

structural-reveal-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {c : Conv↑ Δᴸ A A′}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → (replay : StructuralRebaseAtᴸReplay plan rb)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
  → let child = structural-rebase-atᴸ plan rb replay
        planᵖ = StructuralRebaseAtᴸResult.premise-plan child
     in StructuralRebaseAtᴸResult.Wᵖ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
          ⊢² M ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ↑ c ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-reveal-replay plan mono rb replay sc c⊢ rel
    with structural-rebase-atᴸ plan rb replay
structural-reveal-replay plan mono rb replay sc c⊢ rel
    | record { premise-plan = planᵖ ; post-rebase = rb′
             ; post-mono = mono′ } =
  CTI2.reveal⊑² (mono′ mono) rb′
    (mapCtxᴿ-sameCtx
      (structural-world-extendᴿ plan)
      (structural-world-extendᴿ planᵖ) sc)
    (structural-source-reveal plan c⊢) rel
    (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)


structural-conceal-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
    {c : Conv↓ Δᴸ A A′}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? nothing)
  → (replay : StructuralTagRebaseAtᴸReplay plan rb)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
  → let child = structural-tag-rebase-atᴸ plan rb replay
        planᵖ = StructuralTagRebaseAtᴸResult.premise-plan child
     in StructuralTagRebaseAtᴸResult.Wᵖ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
          ⊢² M ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ↓ c ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-conceal-replay plan mono rb replay sc c⊢ rel
    with structural-tag-rebase-atᴸ plan rb replay
structural-conceal-replay plan mono rb replay sc c⊢ rel
    | record { premise-plan = planᵖ ; post-rebase = rb′
             ; post-mono = mono′ } =
  CTI2.conceal⊑² (mono′ mono)
    (subst≡ (λ pivot → CTX.TagRebaseAtᴸ _ _ _ pivot)
      (mapPivotChanges-nothing-replay plan) rb′)
    (mapCtxᴿ-sameCtx
      (structural-world-extendᴿ plan)
      (structural-world-extendᴿ planᵖ) sc)
    (structural-source-conceal plan c⊢) rel
    (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)


structural-reveal-replay-with-provenance : ∀
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {c : Conv↑ Δᴸ A A′}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → (sc : CTX.SameCtx γ γᵖ)
  → (c⊢ : CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c)
  → (prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p)
  → (provenance : StructuralTermProvenance plan
      (CTI2.reveal⊑² mono rb sc c⊢ prem q))
  → let child = structural-rebase-atᴸ plan rb
          (structural-reveal-replay-provenance plan provenance)
        planᵖ = StructuralRebaseAtᴸResult.premise-plan child
     in StructuralRebaseAtᴸResult.Wᵖ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
          ⊢² M ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ↑ c ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-reveal-replay-with-provenance plan mono rb sc c⊢ prem
    provenance rel =
  structural-reveal-replay plan mono rb replay sc c⊢ rel
  where
  replay = structural-reveal-replay-provenance plan provenance


structural-conceal-replay-with-provenance : ∀
    {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ′ Δ′}
    {γ : CTX.CtxImp W} {γᵖ : CTX.CtxImp Wᵖ}
    {M : Term Δᴸ} {N : Term Δᴿ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ?}
    {c : Conv↓ Δᴸ A A′}
    {p : A CTX.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTX.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTX.ImpEnvMono W Wᵖ)
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? nothing)
  → (sc : CTX.SameCtx γ γᵖ)
  → (c⊢ : CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c)
  → (prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ N ∶ p)
  → (provenance : StructuralTermProvenance plan
      (CTI2.conceal⊑² mono rb sc c⊢ prem q))
  → let child = structural-tag-rebase-atᴸ plan rb
          (structural-conceal-replay-provenance plan provenance)
        planᵖ = StructuralTagRebaseAtᴸResult.premise-plan child
     in StructuralTagRebaseAtᴸResult.Wᵖ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
          ⊢² M ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ↓ c ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-conceal-replay-with-provenance plan mono rb sc c⊢ prem
    provenance rel =
  structural-conceal-replay plan mono rb replay sc c⊢ rel
  where
  replay = structural-conceal-replay-provenance plan provenance
