module proof.DGG.Catchup.StructuralWorldEvidenceProof where

-- File Charter:
--   * Transports wrapper contexts and conversion typing along traces.
--   * Supplies shared endpoint evidence for structural relation replay.

import Data.Fin as Fin
import Data.List as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
  renaming (subst to subst≡)

open import Types using (Ty; TyVar)
open import TyStore using (TyStore)
open import Consistency using (wk↪ᵗ; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; rename↑; rename↓)
open import Imprecision using (X⊑★)
open import Reduction using (StoreChanges)
open import proof.TypeInTermSubst using
  (StoreRename-id; StoreRename-suc-bind; renameᵗ-pointwise-id;
   toRename-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.Reduction as PR
open import proof.DGG.Catchup.StructuralWorldExtendDef


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
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
  → (ext : ECR.WorldExtendᴿ χs W W′)
  → (extᴸ : ECR.WorldExtendᴿ χs
      (CTI2.liftWorldLeft X⊑★ W)
      (CTI2.liftWorldLeft X⊑★ W′))
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
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft v W)}
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


mapPivot-wk-eq : ∀ {Δ} (X? : Maybe (TyVar Δ))
  → TE.mapPivot Fin.suc X?
      ≡ TE.mapPivot (toRenameᵗ wk↪ᵗ) X?
mapPivot-wk-eq nothing = refl
mapPivot-wk-eq (just X) = cong just (sym (toRename-wk-eq X))


mapPivot-id : ∀ {Δ} (X? : Maybe (TyVar Δ))
  → TE.mapPivot (λ X → X) X? ≡ X?
mapPivot-id nothing = refl
mapPivot-id (just X) = refl


revealˣ-subst : ∀ {Δ} {Σ : TyStore Δ} {X? : Maybe (TyVar Δ)}
    {A₀ A₁ B₀ B₁ : Ty Δ}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → ∀ {d : Conv↑ Δ A₀ B₀}
  → Σ CTI2.⊢↑[ X? ] d
  → Σ CTI2.⊢↑[ X? ]
      subst≡ (Conv↑ _ A₁) eqB
        (subst≡ (λ A′ → Conv↑ _ A′ B₀) eqA d)
revealˣ-subst refl refl d⊢ = d⊢


concealˣ-subst : ∀ {Δ} {Σ : TyStore Δ} {X? : Maybe (TyVar Δ)}
    {A₀ A₁ B₀ B₁ : Ty Δ}
  → (eqA : A₀ ≡ A₁)
  → (eqB : B₀ ≡ B₁)
  → ∀ {d : Conv↓ Δ A₀ B₀}
  → Σ CTI2.⊢↓[ X? ] d
  → Σ CTI2.⊢↓[ X? ]
      subst≡ (Conv↓ _ A₁) eqB
        (subst≡ (λ A′ → Conv↓ _ A′ B₀) eqA d)
concealˣ-subst refl refl d⊢ = d⊢


normalizeRevealˣ : ∀ {Δ} {Σ : TyStore Δ} {X? : Maybe (TyVar Δ)}
    {A B : Ty Δ} {c : Conv↑ Δ A B}
  → Σ CTI2.⊢↑[ X? ] c
  → Σ CTI2.⊢↑[ X? ] PR.normalizeReveal c
normalizeRevealˣ {Σ = Σ} {X? = X?} {A = A} {B = B} {c = c} c⊢ =
  revealˣ-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl))
    (subst≡ (λ pivot → Σ CTI2.⊢↑[ pivot ] rename↑ (λ X → X) c)
      (mapPivot-id X?) (TE.reveal-renameˣ StoreRename-id c⊢))


normalizeConcealˣ : ∀ {Δ} {Σ : TyStore Δ} {X? : Maybe (TyVar Δ)}
    {A B : Ty Δ} {c : Conv↓ Δ A B}
  → Σ CTI2.⊢↓[ X? ] c
  → Σ CTI2.⊢↓[ X? ] PR.normalizeConceal c
normalizeConcealˣ {Σ = Σ} {X? = X?} {A = A} {B = B} {c = c} c⊢ =
  concealˣ-subst (renameᵗ-pointwise-id _ A (λ X → refl))
    (renameᵗ-pointwise-id _ B (λ X → refl))
    (subst≡ (λ pivot → Σ CTI2.⊢↓[ pivot ] rename↓ (λ X → X) c)
      (mapPivot-id X?) (TE.conceal-renameˣ StoreRename-id c⊢))


structural-source-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↑ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ X? ] c
  → CTI2.sourceStoreʷ W′ CTI2.⊢↑[ X? ] c
structural-source-reveal structural-[] c⊢ = c⊢
structural-source-reveal (structural-keep plan) c⊢ =
  structural-source-reveal plan c⊢
structural-source-reveal (structural-bind ins follows plan) c⊢ =
  structural-source-reveal plan (TE.source-reveal-insert ins c⊢)


structural-source-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴸ)} {A B : Ty Δᴸ}
    {c : Conv↓ Δᴸ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ X? ] c
  → CTI2.sourceStoreʷ W′ CTI2.⊢↓[ X? ] c
structural-source-conceal structural-[] c⊢ = c⊢
structural-source-conceal (structural-keep plan) c⊢ =
  structural-source-conceal plan c⊢
structural-source-conceal (structural-bind ins follows plan) c⊢ =
  structural-source-conceal plan (TE.source-conceal-insert ins c⊢)


structural-target-reveal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴿ)} {A B : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W CTI2.⊢↑[ X? ] c
  → CTI2.targetStoreʷ W′ CTI2.⊢↑[ mapPivotChanges χs X? ]
      PR.applyReveals χs c
structural-target-reveal structural-[] c⊢ = c⊢
structural-target-reveal (structural-keep plan) c⊢ =
  structural-target-reveal plan (normalizeRevealˣ c⊢)
structural-target-reveal {X? = X?} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-reveal plan
    (subst≡
      (λ pivot → CTI2.targetStoreʷ W₁ CTI2.⊢↑[ pivot ]
        rename↑ Fin.suc c)
      (mapPivot-wk-eq X?)
      (subst≡
        (λ Σ → Σ CTI2.⊢↑[ TE.mapPivot Fin.suc X? ] rename↑ Fin.suc c)
        (sym follows)
        (TE.reveal-renameˣ StoreRename-suc-bind c⊢)))


structural-target-conceal : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {X? : Maybe (TyVar Δᴿ)} {A B : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTI2.targetStoreʷ W CTI2.⊢↓[ X? ] c
  → CTI2.targetStoreʷ W′ CTI2.⊢↓[ mapPivotChanges χs X? ]
      PR.applyConceals χs c
structural-target-conceal structural-[] c⊢ = c⊢
structural-target-conceal (structural-keep plan) c⊢ =
  structural-target-conceal plan (normalizeConcealˣ c⊢)
structural-target-conceal {X? = X?} {c = c}
    (structural-bind {W₁ = W₁} ins follows plan) c⊢ =
  structural-target-conceal plan
    (subst≡
      (λ pivot → CTI2.targetStoreʷ W₁ CTI2.⊢↓[ pivot ]
        rename↓ Fin.suc c)
      (mapPivot-wk-eq X?)
      (subst≡
        (λ Σ → Σ CTI2.⊢↓[ TE.mapPivot Fin.suc X? ] rename↓ Fin.suc c)
        (sym follows)
        (TE.conceal-renameˣ StoreRename-suc-bind c⊢)))
