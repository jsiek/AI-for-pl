module proof.DGG.Catchup.StructuralSourceRebaseReplayProof where

-- File Charter:
--   * Replays source reveal and conceal at structural trace endpoints.
--   * Uses transformed rebases, contexts, typing, and monotonicity evidence.

open import Data.Maybe using (Maybe)

open import Types using (Ty; TyVar)
open import Conversion using (Conv↑; Conv↓)
open import CastTerms using (Term; _↑_; _↓_)
open import Reduction using (StoreChanges)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldRebaseProof
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof


structural-reveal-replay : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
    {M : Term Δᴸ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? : Maybe (TyVar Δᴸ)}
    {c : Conv↑ Δᴸ A A′}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTI2.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
  → let child = structural-rebase-atᴸ plan rb
        planᵖ = StructuralRebaseAtᴸResult.premise-plan child
     in StructuralRebaseAtᴸResult.Wᵖ′ child CTI2.∣
          ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
          ⊢² M ⊑ F ∶
            ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
  → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
      ⊢² M ↑ c ⊑ F ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-reveal-replay plan mono rb sc c⊢ rel
    with structural-rebase-atᴸ plan rb
structural-reveal-replay plan mono rb sc c⊢ rel
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
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
    {M : Term Δᴸ} {F : Term Δᴿ′}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {Xᴸ? Xᴿ?}
    {c : Conv↓ Δᴸ A A′}
    {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ B}
    {q : A′ CTI2.⊑ᵂ⟨ W ⟩ B}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → CTI2.SameCtx γ γᵖ
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
  → let child = structural-tag-rebase-atᴸ plan rb
        planᵖ = StructuralTagRebaseAtᴸResult.premise-plan child
     in CTI2.SourceConcealPartnerOK
          (StructuralTagRebaseAtᴸResult.Wᵖ′ child) M c
          (mapPivotChanges χs Xᴿ?) F
        → StructuralTagRebaseAtᴸResult.Wᵖ′ child CTI2.∣
            ECR.mapCtxᴿ (structural-world-extendᴿ planᵖ) γᵖ
            ⊢² M ⊑ F ∶
              ECR.transport⊑ᵂ (structural-world-extendᴿ planᵖ) p
        → W′ CTI2.∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
            ⊢² M ↓ c ⊑ F ∶
              ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q
structural-conceal-replay plan mono rb sc c⊢ ok rel
    with structural-tag-rebase-atᴸ plan rb
structural-conceal-replay plan mono rb sc c⊢ ok rel
    | record { premise-plan = planᵖ ; post-rebase = rb′
             ; post-mono = mono′ } =
  CTI2.conceal⊑² ok (mono′ mono) rb′
    (mapCtxᴿ-sameCtx
      (structural-world-extendᴿ plan)
      (structural-world-extendᴿ planᵖ) sc)
    (structural-source-conceal plan c⊢) rel
    (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) _)
