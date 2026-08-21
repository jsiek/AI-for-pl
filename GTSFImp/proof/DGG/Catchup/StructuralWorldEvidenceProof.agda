module proof.DGG.Catchup.StructuralWorldEvidenceProof where

-- File Charter:
--   * Transports contexts and generator-indexed conversion typing along
--     structural traces.
--   * Preserves direct representation membership and generator positions
--     needed to replay the nine conversion-wrapper cases.

import Data.Fin as Fin
import Data.List as List
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar)
open import TyStore using (TyStore; _∋_⦂_)
open import Consistency using (_↪ᵗ_)
open import Conversion using
  (Conv↑; Conv↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges; applyTys)
open import proof.TypeInTermSubst using
  (StoreRename-suc-bind; StoreRename-id; reveal-renameᵗ; conceal-renameᵗ;
   reveal-rename-id; conceal-rename-id; renameᵗ-id;
   renameᵗ-pointwise-id)
open import proof.ImprecisionConsistency using (fin-suc-injective)
import proof.DGG.CtxImp as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.Reduction as PR
open import proof.DGG.ConversionPivotAlignment using
  (revealGeneratorPosition; concealGeneratorPosition;
   revealGeneratorPosition-store-transport;
   concealGeneratorPosition-store-transport;
   revealGeneratorPosition-unique; concealGeneratorPosition-unique)
open import proof.DGG.Catchup.StructuralWorldExtendDef


reveal-representation-transport : ∀ {Δ} {Σ : TyStore Δ} {X}
    {R R′ A B : Ty Δ} {c : Conv↑ Δ A B}
  → R ≡ R′
  → Σ ⊢↑[ X ⦂ R ] c
  → Σ ⊢↑[ X ⦂ R′ ] c
reveal-representation-transport refl c⊢ = c⊢


conceal-representation-transport : ∀ {Δ} {Σ : TyStore Δ} {X}
    {R R′ A B : Ty Δ} {c : Conv↓ Δ A B}
  → R ≡ R′
  → Σ ⊢↓[ X ⦂ R ] c
  → Σ ⊢↓[ X ⦂ R′ ] c
conceal-representation-transport refl c⊢ = c⊢


reveal-representation-transport-position : ∀ {Δ}
    {Σ : TyStore Δ} {X} {R R′ A B : Ty Δ} {c : Conv↑ Δ A B}
  → (eq : R ≡ R′)
  → (c⊢ : Σ ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (reveal-representation-transport eq c⊢)
      ≡ revealGeneratorPosition c⊢
reveal-representation-transport-position refl c⊢ = refl


conceal-representation-transport-position : ∀ {Δ}
    {Σ : TyStore Δ} {X} {R R′ A B : Ty Δ} {c : Conv↓ Δ A B}
  → (eq : R ≡ R′)
  → (c⊢ : Σ ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (conceal-representation-transport eq c⊢)
      ≡ concealGeneratorPosition c⊢
conceal-representation-transport-position refl c⊢ = refl


reveal-endpoint-transport : ∀ {Δ} {Σ : TyStore Δ} {X R}
    {A₀ A₁ B₀ B₁ : Ty Δ} {c : Conv↑ Δ A₀ B₀}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → Σ ⊢↑[ X ⦂ R ] c
  → Σ ⊢↑[ X ⦂ R ]
      subst≡ (Conv↑ Δ A₁) eqB
        (subst≡ (λ A → Conv↑ Δ A B₀) eqA c)
reveal-endpoint-transport refl refl c⊢ = c⊢


conceal-endpoint-transport : ∀ {Δ} {Σ : TyStore Δ} {X R}
    {A₀ A₁ B₀ B₁ : Ty Δ} {c : Conv↓ Δ A₀ B₀}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → Σ ⊢↓[ X ⦂ R ] c
  → Σ ⊢↓[ X ⦂ R ]
      subst≡ (Conv↓ Δ A₁) eqB
        (subst≡ (λ A → Conv↓ Δ A B₀) eqA c)
conceal-endpoint-transport refl refl c⊢ = c⊢


reveal-endpoint-transport-position : ∀ {Δ} {Σ : TyStore Δ} {X R}
    {A₀ A₁ B₀ B₁ : Ty Δ} {c : Conv↑ Δ A₀ B₀}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → (c⊢ : Σ ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (reveal-endpoint-transport eqA eqB c⊢)
      ≡ revealGeneratorPosition c⊢
reveal-endpoint-transport-position refl refl c⊢ = refl


conceal-endpoint-transport-position : ∀ {Δ}
    {Σ : TyStore Δ} {X R} {A₀ A₁ B₀ B₁ : Ty Δ}
    {c : Conv↓ Δ A₀ B₀}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → (c⊢ : Σ ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (conceal-endpoint-transport eqA eqB c⊢)
      ≡ concealGeneratorPosition c⊢
conceal-endpoint-transport-position refl refl c⊢ = refl


reveal-rename-id-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
    {c : Conv↑ Δ A B}
  → (c⊢ : Σ ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (reveal-rename-id c⊢)
      ≡ revealGeneratorPosition c⊢
reveal-rename-id-position {R = R} c⊢ =
  trans
    (revealGeneratorPosition-unique (reveal-rename-id c⊢)
      (reveal-representation-transport (renameᵗ-id R)
        (reveal-renameᵗ (λ eq → eq) StoreRename-id c⊢)))
    (trans
      (reveal-representation-transport-position (renameᵗ-id R)
        (reveal-renameᵗ (λ eq → eq) StoreRename-id c⊢))
      (TE.reveal-rename-position (λ eq → eq) StoreRename-id c⊢))


conceal-rename-id-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
    {c : Conv↓ Δ A B}
  → (c⊢ : Σ ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (conceal-rename-id c⊢)
      ≡ concealGeneratorPosition c⊢
conceal-rename-id-position {R = R} c⊢ =
  trans
    (concealGeneratorPosition-unique (conceal-rename-id c⊢)
      (conceal-representation-transport (renameᵗ-id R)
        (conceal-renameᵗ (λ eq → eq) StoreRename-id c⊢)))
    (trans
      (conceal-representation-transport-position (renameᵗ-id R)
        (conceal-renameᵗ (λ eq → eq) StoreRename-id c⊢))
      (TE.conceal-rename-position (λ eq → eq) StoreRename-id c⊢))


normalize-reveal-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
    {c : Conv↑ Δ A B}
  → (c⊢ : Σ ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (PR.normalizeReveal-⊢↑ c⊢)
      ≡ revealGeneratorPosition c⊢
normalize-reveal-position {A = A} {B = B} c⊢ =
  trans
    (revealGeneratorPosition-unique (PR.normalizeReveal-⊢↑ c⊢)
      (reveal-endpoint-transport eqA eqB (reveal-rename-id c⊢)))
    (trans
      (reveal-endpoint-transport-position eqA eqB
        (reveal-rename-id c⊢))
      (reveal-rename-id-position c⊢))
  where
  eqA = renameᵗ-pointwise-id (λ X → X) A (λ X → refl)
  eqB = renameᵗ-pointwise-id (λ X → X) B (λ X → refl)


normalize-conceal-position : ∀ {Δ} {Σ : TyStore Δ} {X R A B}
    {c : Conv↓ Δ A B}
  → (c⊢ : Σ ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (PR.normalizeConceal-⊢↓ c⊢)
      ≡ concealGeneratorPosition c⊢
normalize-conceal-position {A = A} {B = B} c⊢ =
  trans
    (concealGeneratorPosition-unique (PR.normalizeConceal-⊢↓ c⊢)
      (conceal-endpoint-transport eqA eqB (conceal-rename-id c⊢)))
    (trans
      (conceal-endpoint-transport-position eqA eqB
        (conceal-rename-id c⊢))
      (conceal-rename-id-position c⊢))
  where
  eqA = renameᵗ-pointwise-id (λ X → X) A (λ X → refl)
  eqB = renameᵗ-pointwise-id (λ X → X) B (λ X → refl)


mapCtxᴿ-sameCtx : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δᵖ Δ′ Δᵖ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δᵖ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵖ′ : CTI2.World Δᴸ Δᴿ′ Δᵖ′}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᵖ : ECR.WorldExtendᴿ χs Wᵖ Wᵖ′)
  → CTI2.SameCtx γ γᵖ
  → CTI2.SameCtx (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᵖ γᵖ)
mapCtxᴿ-sameCtx ext extᵖ CTI2.same-[] = CTI2.same-[]
mapCtxᴿ-sameCtx ext extᵖ (CTI2.same-∷ sc) =
  CTI2.same-∷ (mapCtxᴿ-sameCtx ext extᵖ sc)


mapCtxᴿ-liftCtxᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft W)}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᴸ : ECR.WorldExtendᴿ χs
      (CTI2.liftWorldLeft W)
      (CTI2.liftWorldLeft W′))
  → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
  → CTI2.LiftCtxᴸ X⊑★
      (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᴸ γᴸ)
mapCtxᴿ-liftCtxᴸ ext extᴸ CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftCtxᴸ ext extᴸ (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftCtxᴸ ext extᴸ liftγ)


mapCtxᴿ-smartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ Δᵐ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {Wᵐ′ : CTI2.World (suc Δᴸ) Δᴿ′ Δᵐ′}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᵐ : ECR.WorldExtendᴿ χs Wᵐ Wᵐ′)
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext γ) (ECR.mapCtxᴿ extᵐ γᵐ)
mapCtxᴿ-smartLiftCtxᴸ ext extᵐ CTI2.smart-lift-[] =
  CTI2.smart-lift-[]
mapCtxᴿ-smartLiftCtxᴸ ext extᵐ (CTI2.smart-lift-∷ liftγ) =
  CTI2.smart-lift-∷ (mapCtxᴿ-smartLiftCtxᴸ ext extᵐ liftγ)


liftCtxᴸ-target-ctx : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft W)}
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.tgtCtxʷ γ′ ≡ CTI2.tgtCtxʷ γ
liftCtxᴸ-target-ctx CTI2.liftᴸ-[] = refl
liftCtxᴸ-target-ctx (CTI2.liftᴸ-∷ liftγ) =
  cong (_ List.∷_) (liftCtxᴸ-target-ctx liftγ)


smartCommaLift-target-store : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → CTI2.targetStoreʷ Wᵐ ≡ CTI2.targetStoreʷ W
smartCommaLift-target-store (CTI2.smart-fresh-behind guard) =
  CTI2.SmartFreshBehindGuard.targetStore-same guard
smartCommaLift-target-store (CTI2.smart-merge-alias guard) =
  CTI2.SmartAliasMergeGuard.targetStore-same guard


smartLiftCtxᴸ-target-ctx : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → CTI2.SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
  → CTI2.tgtCtxʷ γᵐ ≡ CTI2.tgtCtxʷ γ
smartLiftCtxᴸ-target-ctx CTI2.smart-lift-[] = refl
smartLiftCtxᴸ-target-ctx (CTI2.smart-lift-∷ liftγ) =
  cong (_ List.∷_) (smartLiftCtxᴸ-target-ctx liftγ)


structural-source-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W ⊢↑[ X ⦂ R ] c
  → CTI2.sourceStoreʷ W′ ⊢↑[ X ⦂ R ] c
structural-source-reveal structural-[] c⊢ = c⊢
structural-source-reveal (structural-keep plan) c⊢ =
  structural-source-reveal plan c⊢
structural-source-reveal (structural-bind ins follows plan) c⊢ =
  structural-source-reveal plan (TE.source-reveal-insert ins c⊢)


structural-source-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W ⊢↓[ X ⦂ R ] c
  → CTI2.sourceStoreʷ W′ ⊢↓[ X ⦂ R ] c
structural-source-conceal structural-[] c⊢ = c⊢
structural-source-conceal (structural-keep plan) c⊢ =
  structural-source-conceal plan c⊢
structural-source-conceal (structural-bind ins follows plan) c⊢ =
  structural-source-conceal plan (TE.source-conceal-insert ins c⊢)


source-reveal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {rho : Δᴿ ↪ᵗ Δᴿ′} {pi : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → (ins : TE.TargetInsert rho pi W W′)
  → (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (TE.source-reveal-insert ins c⊢)
      ≡ revealGeneratorPosition c⊢
source-reveal-insert-position ins c⊢ =
  revealGeneratorPosition-store-transport
    (sym (TE.sourceStore-kept ins)) c⊢


source-conceal-insert-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {rho : Δᴿ ↪ᵗ Δᴿ′} {pi : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → (ins : TE.TargetInsert rho pi W W′)
  → (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (TE.source-conceal-insert ins c⊢)
      ≡ concealGeneratorPosition c⊢
source-conceal-insert-position ins c⊢ =
  concealGeneratorPosition-store-transport
    (sym (TE.sourceStore-kept ins)) c⊢


structural-source-reveal-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {chi : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → (plan : StructuralWorldExtendᴿ chi W W′)
  → (c⊢ : CTI2.sourceStoreʷ W ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (structural-source-reveal plan c⊢)
      ≡ revealGeneratorPosition c⊢
structural-source-reveal-position structural-[] c⊢ = refl
structural-source-reveal-position (structural-keep plan) c⊢ =
  structural-source-reveal-position plan c⊢
structural-source-reveal-position
    (structural-bind ins follows plan) c⊢ =
  trans
    (structural-source-reveal-position plan
      (TE.source-reveal-insert ins c⊢))
    (source-reveal-insert-position ins c⊢)


structural-source-conceal-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {chi : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴸ} {R A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → (plan : StructuralWorldExtendᴿ chi W W′)
  → (c⊢ : CTI2.sourceStoreʷ W ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (structural-source-conceal plan c⊢)
      ≡ concealGeneratorPosition c⊢
structural-source-conceal-position structural-[] c⊢ = refl
structural-source-conceal-position (structural-keep plan) c⊢ =
  structural-source-conceal-position plan c⊢
structural-source-conceal-position
    (structural-bind ins follows plan) c⊢ =
  trans
    (structural-source-conceal-position plan
      (TE.source-conceal-insert ins c⊢))
    (source-conceal-insert-position ins c⊢)


structural-target-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W ⊢↑[ X ⦂ R ] c
  → CTI2.targetStoreʷ W′
      ⊢↑[ mapVarChanges χs X ⦂ applyTys χs R ] PR.applyReveals χs c
structural-target-reveal structural-[] c⊢ = c⊢
structural-target-reveal (structural-keep plan) c⊢ =
  structural-target-reveal plan (PR.normalizeReveal-⊢↑ c⊢)
structural-target-reveal {X = X} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-reveal plan
    (subst≡ (λ Σ → Σ ⊢↑[ Fin.suc X ⦂ _ ] _)
      (sym follows)
      (reveal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢))


structural-target-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W ⊢↓[ X ⦂ R ] c
  → CTI2.targetStoreʷ W′
      ⊢↓[ mapVarChanges χs X ⦂ applyTys χs R ] PR.applyConceals χs c
structural-target-conceal structural-[] c⊢ = c⊢
structural-target-conceal (structural-keep plan) c⊢ =
  structural-target-conceal plan (PR.normalizeConceal-⊢↓ c⊢)
structural-target-conceal {X = X} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-conceal plan
    (subst≡ (λ Σ → Σ ⊢↓[ Fin.suc X ⦂ _ ] _)
      (sym follows)
      (conceal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢))


structural-target-member : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {chi : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R : Ty Δᴿ}
  → StructuralWorldExtendᴿ chi W W′
  → CTI2.targetStoreʷ W ∋ X ⦂ R
  → CTI2.targetStoreʷ W′ ∋ mapVarChanges chi X ⦂ applyTys chi R
structural-target-member structural-[] member = member
structural-target-member (structural-keep plan) member =
  structural-target-member plan member
structural-target-member {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) member =
  structural-target-member plan
    (subst≡ (λ Sigma → Sigma ∋ Fin.suc X ⦂ _)
      (sym follows) (StoreRename-suc-bind member))


structural-target-reveal-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {chi : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
  → (plan : StructuralWorldExtendᴿ chi W W′)
  → (c⊢ : CTI2.targetStoreʷ W ⊢↑[ X ⦂ R ] c)
  → revealGeneratorPosition (structural-target-reveal plan c⊢)
      ≡ revealGeneratorPosition c⊢
structural-target-reveal-position structural-[] c⊢ = refl
structural-target-reveal-position (structural-keep plan) c⊢ =
  trans
    (structural-target-reveal-position plan
      (PR.normalizeReveal-⊢↑ c⊢))
    (normalize-reveal-position c⊢)
structural-target-reveal-position {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  trans
    (structural-target-reveal-position plan renamed)
    (trans
      (revealGeneratorPosition-store-transport (sym follows) shifted)
      (TE.reveal-rename-position fin-suc-injective
        StoreRename-suc-bind c⊢))
  where
  shifted = reveal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢
  renamed = subst≡ (λ Sigma → Sigma ⊢↑[ Fin.suc X ⦂ _ ] _)
    (sym follows) shifted


structural-target-conceal-position : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {chi : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {R A B : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
  → (plan : StructuralWorldExtendᴿ chi W W′)
  → (c⊢ : CTI2.targetStoreʷ W ⊢↓[ X ⦂ R ] c)
  → concealGeneratorPosition (structural-target-conceal plan c⊢)
      ≡ concealGeneratorPosition c⊢
structural-target-conceal-position structural-[] c⊢ = refl
structural-target-conceal-position (structural-keep plan) c⊢ =
  trans
    (structural-target-conceal-position plan
      (PR.normalizeConceal-⊢↓ c⊢))
    (normalize-conceal-position c⊢)
structural-target-conceal-position {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  trans
    (structural-target-conceal-position plan renamed)
    (trans
      (concealGeneratorPosition-store-transport (sym follows) shifted)
      (TE.conceal-rename-position fin-suc-injective
        StoreRename-suc-bind c⊢))
  where
  shifted = conceal-renameᵗ fin-suc-injective StoreRename-suc-bind c⊢
  renamed = subst≡ (λ Sigma → Sigma ⊢↓[ Fin.suc X ⦂ _ ] _)
    (sym follows) shifted
