module proof.DGG.Catchup.StructuralNameInstantiationProof where

-- File Charter:
--   * Implements the structural worker for named target instantiation.
--   * Uses cast mass as the primary accessibility measure.
--   * Replays source wrappers only after target normalization is known.

import Data.Fin as Fin
import Data.List as List
import Data.Nat.Induction as NatInduction
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc; _<_; _+_)
open import Data.Nat.Properties using (+-assoc; n<1+n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
import Data.Product.Relation.Binary.Lex.Strict as ProductLex
open import Data.Sum.Base using (inj₁; inj₂)
import Induction.WellFounded as WF
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; ⇑ᵗ; _[_]ᵗ;
   renameᵗ)
open import Imprecision using (X⊑★)
open import Consistency using
  (Env∼; _↪ᵗ_; wk↪ᵗ; keep; toRenameᵗ; _⊢_∼_; inst_; ↑ᶜ_;
   close-instᶜ; ∀ᶜ_; gen_)
open import Conversion using (Conv↑; Conv↓)
import CastTerms as CT
open import CastTerms using
  (Term; Value; Inert; GenSafe; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩;
   _↑_; _↓_; _⦂∀_[_]; renameᵗᵐ; ⇑ᵗᵐ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; bind; applyStores; applyTy;
   _—→[_]_; _—↠[_]_; ↠-refl; ↠-step; pure-step;
   β-Λ; β-∀; β-gen; β-inst; id-reveal; id-conceal; conceal-reveal)
open import proof.TypeInTermSubst using
  (renameᵗ-wk-eq; renameᵗᵐ-preserves-Value)
open import proof.TypeSafety.Preservation using
  (applyBody-open-zero; replace-zero-open)
import proof.TypeSafety.Progress as Prog
import proof.Imprecision as PI
import proof.Consistency as PC
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.DGG.Inversion.SpineValueProof as SpineValueProof
open import proof.DGG.Catchup.InstInversionDef using
  (StructuralValueInstantiationᵀ)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (FuelStepSurface; Catchup⁻Embedᵀ; inst-alloc-decreaseᵀ; castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef
open import proof.DGG.Catchup.StructuralValueInstantiationCastMassDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankDef
open import proof.DGG.Catchup.StructuralValueInstantiationRankProof
  using
    (_<ʳ_; rank-name<; rank-exp<; rank-length<;
     lambda-rank-decreases; reveal-rank-decreases;
     conceal-rank-decreases; cast-frame-rank-decreases;
     reveal-frame-value-rank-decreases;
     conceal-frame-value-rank-decreases;
     reveal-frame-id-rank-decreases;
     reveal-frame-conceal-rank-decreases;
     conceal-frame-id-rank-decreases)
open import proof.DGG.Catchup.StructuralValueInstantiationCastProof
open import proof.DGG.Catchup.StructuralValueInstantiationAllCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationGenCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationInstCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationPendingCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationSpineCastMassProof
open import proof.DGG.Catchup.StructuralValueInstantiationValueCastMassProof
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
open import proof.DGG.Catchup.StructuralWorldEvidenceProof
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof
open import proof.DGG.Catchup.StructuralTargetInstantiationDef
open import proof.DGG.Catchup.StructuralTargetInstantiationProof
open import proof.DGG.Catchup.StructuralFrameOutcomeDef
open import proof.DGG.Catchup.StructuralFrameOutcomeProof
open import proof.DGG.Catchup.StructuralTargetFrameAbsorptionDef
open import proof.DGG.Catchup.StructuralSpineTypingDef
open import proof.DGG.Catchup.StructuralTargetSourceTransportProof
open import proof.DGG.Catchup.StructuralTargetFrameDecompositionProof
open import proof.DGG.Catchup.StructuralTargetPeelSupportProof
  using (value-no-step)
open import proof.DGG.Catchup.StructuralTargetInstPeelProof
open import proof.DGG.Catchup.StructuralTargetLambdaPeelProof
open import proof.DGG.Catchup.StructuralTargetAllPeelProof
open import proof.DGG.Catchup.StructuralTargetGenPeelProof
open import proof.DGG.Catchup.StructuralTargetRevealPeelProof
open import proof.DGG.Catchup.StructuralTargetConcealPeelProof
open import proof.DGG.Catchup.StructuralInstantiationDescentDef
open import proof.DGG.Catchup.StructuralInstantiationDescentProof
open import proof.DGG.Catchup.StructuralSourceLambdaReplayProof
open import proof.DGG.Catchup.StructuralSourceRebaseReplayProof
open import proof.DGG.Catchup.StructuralAllDescentProof
open import proof.DGG.Catchup.StructuralGenDescentProof
open import proof.DGG.Catchup.StructuralInstDescentProof
open import proof.DGG.Catchup.StructuralValueInstantiationReductionProof
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal;
   allv-conceal)


StructuralValueSpineInstantiationAccᵀ : Set₁
StructuralValueSpineInstantiationAccᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {C₀ E : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ C₀}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → (vV : Value V)
  → (spine : InstantiationSpine C₀ E)
  → TargetFrameAbsorptionChain W γ A spine q
  → SpineTypedʷ {fuel = fuel} W spine
  → Acc _<_ (pendingCastMass vV spine)
  → Acc _<ʳ_ (pendingRank vV spine)
  → (target : StructuralTargetInstantiationPackage W V spine)
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


StructuralNameInstantiationAccᵀ : Set₁
StructuralNameInstantiationAccᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {E : Ty Δᴿ} {X : TyVar Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {q : A CTI2.⊑ᵂ⟨ W ⟩ E}
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A E q)
  → StructuralNameChainPlan {fuel = fuel} W γ A E q plan
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → Value M
  → (vV : Value V)
  → AllValueView V
  → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
  → TargetFrameAbsorptionChain W γ A
      (name-type-app-frame B X refl refl ▻ⁱ spine) q
  → SpineTypedʷ {fuel = fuel} W
      (name-type-app-frame B X refl refl ▻ⁱ spine)
  → Acc _<_ (pendingCastMass vV
      (name-type-app-frame B X refl refl ▻ⁱ spine))
  → Acc _<ʳ_ (pendingRank vV
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
  StructuralValueSpineInstantiationAccᵀ


StructuralNameInstantiationStrictᵀ : Set₁
StructuralNameInstantiationStrictᵀ =
  StructuralValueSpineInstantiationAccᵀ


acc-smaller : ∀ {A : Set} {R : A → A → Set} {x y}
  → Acc R y
  → R x y
  → Acc R x
acc-smaller (WF.acc smaller) lt = smaller lt


acc-transport : ∀ {A : Set} {R : A → A → Set} {x y}
  → x ≡ y
  → Acc R x
  → Acc R y
acc-transport refl accessible = accessible


rel-⊑-unique : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ q
rel-⊑-unique {W = W} {γ = γ} {p = p} {q = q} rel =
  subst≡ (λ r → W CTI2.∣ γ ⊢² _ ⊑ _ ∶ r)
    (PI.⊑-unique p q) rel


RankTuple : Set
RankTuple = ℕ × (ℕ × ℕ)


rank-tuple : InstantiationRank → RankTuple
rank-tuple (inst-rank names exp length) = names , (exp , length)


_<ʳlex_ : RankTuple → RankTuple → Set
_<ʳlex_ =
  ProductLex.×-Lex _≡_ _<_
    (ProductLex.×-Lex _≡_ _<_ _<_)


rank<→lex : ∀ {r r′}
  → r <ʳ r′
  → rank-tuple r <ʳlex rank-tuple r′
rank<→lex (rank-name< names<) = inj₁ names<
rank<→lex (rank-exp< names≡ exp<) =
  inj₂ (names≡ , inj₁ exp<)
rank<→lex (rank-length< names≡ exp≡ length<) =
  inj₂ (names≡ , inj₂ (exp≡ , length<))


rank-lex-wf : WF.WellFounded _<ʳlex_
rank-lex-wf =
  ProductLex.×-wellFounded NatInduction.<-wellFounded
    (ProductLex.×-wellFounded NatInduction.<-wellFounded
      NatInduction.<-wellFounded)


rank-access-from-lex : ∀ r
  → Acc _<ʳlex_ (rank-tuple r)
  → Acc _<ʳ_ r
rank-access-from-lex r (WF.acc smaller) =
  WF.acc λ {r′} r′<r →
    rank-access-from-lex r′ (smaller (rank<→lex r′<r))


rank-access : ∀ r → Acc _<ʳ_ r
rank-access r = rank-access-from-lex r (rank-lex-wf (rank-tuple r))


all-view→all-value-view : ∀ {Δ} {B : Ty (suc Δ)} {V : Term Δ}
  → Prog.AllView B V
  → AllValueView V
all-view→all-value-view (Prog.av-Λ vV refl) =
  allv-Λ vV refl
all-view→all-value-view (Prog.av-∀ vV refl) =
  allv-∀ vV refl
all-view→all-value-view (Prog.av-gen vV A≢★ safe refl) =
  allv-gen vV A≢★ safe refl
all-view→all-value-view (Prog.av-reveal vV refl) =
  allv-reveal vV refl
all-view→all-value-view (Prog.av-conceal vV refl) =
  allv-conceal vV refl


relation-all-value-view : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → AllValueView V
relation-all-value-view vV rel =
  all-view→all-value-view
    (Prog.canonical-∀ vV (CTI2T.target-typing² rel))


target-empty-final-relation : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p q : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → Value V
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → (target : StructuralTargetInstantiationPackage W V ([]ⁱ {A = B}))
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
target-empty-final-relation {W = W} {γ = γ} vV rel target
    with StructuralTargetInstantiationPackage.post-reduction target
target-empty-final-relation {W = W} {γ = γ} vV rel target
    | ↠-refl
    with StructuralTargetInstantiationPackage.structural-ext target
target-empty-final-relation {W = W} {γ = γ} vV rel target
    | ↠-refl | structural-[] =
  subst≡
    (λ γ′ → W CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
    (sym (ECR.mapCtxᴿ-same γ))
    (rel-⊑-unique rel)
target-empty-final-relation vV rel target | ↠-step step rest =
  ⊥-elim (value-no-step vV step)


mapCtx-target-insert-bind : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {R : Ty Δᴿ}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → (follows : CTI2.targetStoreʷ W′ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W))
  → (γ : CTI2.CtxImp W)
  → ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ ≡
      TE.mapCtxᵀ ins γ
mapCtx-target-insert-bind ins follows List.[] = refl
mapCtx-target-insert-bind {W′ = W′} {R = R} ins follows
    (CTI2.ctx-imp A B p List.∷ γ) =
  cong₂ List._∷_ entry-eq (mapCtx-target-insert-bind ins follows γ)
  where
  ext = target-insert-bind-world-extendᴿ ins follows

  entry-eq :
      CTI2.ctx-imp A (⇑ᵗ B) (ECR.transport⊑ᵂ ext p) ≡
      CTI2.ctx-imp A (renameᵗ (toRenameᵗ wk↪ᵗ) B)
        (TE.transport⊑ᵂ ins p)
  entry-eq =
    TE.ctx-imp-target-eq {W = W′}
      {A = A} {B = ⇑ᵗ B}
      {B′ = renameᵗ (toRenameᵗ wk↪ᵗ) B}
      {p = ECR.transport⊑ᵂ ext p}
      {q = TE.transport⊑ᵂ ins p}
      (sym (renameᵗ-wk-eq B))


target-insert-bind-relation : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {R : Ty Δᴿ}
    {γ : CTI2.CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → (follows : CTI2.targetStoreʷ W′ ≡
      applyStores (bind R ∷ []) (CTI2.targetStoreʷ W))
  → W CTI2.∣ γ ⊢² M ⊑ V ∶ p
  → W′ CTI2.∣
      ECR.mapCtxᴿ (target-insert-bind-world-extendᴿ ins follows) γ
      ⊢² M ⊑ renameᵗᵐ wk↪ᵗ V ∶
        ECR.transport⊑ᵂ (target-insert-bind-world-extendᴿ ins follows) p
target-insert-bind-relation {γ = γ} {B = B} {p = p}
    ins follows rel =
  subst≡
    (λ γ′ → _ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶
      ECR.transport⊑ᵂ ext p)
    (sym (mapCtx-target-insert-bind ins follows γ))
    (TE.⊢²-retargetᴿ {q = ECR.transport⊑ᵂ ext p}
      (renameᵗ-wk-eq B) (TE.⊢²-target-insert ins rel))
  where
  ext = target-insert-bind-world-extendᴿ ins follows


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


structural-name-cast-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {U V : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {ν : Env∼ Δᴸ}
      {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
      {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A′ E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A′ E q plan
    → (c : ν ⊢ A ∼ A′)
    → Inert c
    → W CTI2.∣ γ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ A′
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ʳ_ (pendingRank vN
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
structural-name-cast-equal worker {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan c inert
    prem vU vN view spine chain typed acc rank target
    with StructuralNamePostPlan.cast-child plan c
       | StructuralNameChainPlan.cast-child chain-plan c chain typed
structural-name-cast-equal worker {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan c inert
    prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-inert-cast-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    c inert
    (worker fuel-step catchup⁻-embed inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed acc rank target)


structural-name-plain-Λ-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ} {W : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W}
      {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft X⊑★ W)}
      {U : Term (suc Δᴸ)} {N : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
      {p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ `∀ B}
      {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W (`∀ A) E q)
    → StructuralNameChainPlan {fuel = fuel} W γ (`∀ A) E q plan
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTI2.LiftCtxᴸ X⊑★ γ γᴸ
    → CTI2.liftWorldLeft X⊑★ W CTI2.∣ γᴸ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ (`∀ A)
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ʳ_ (pendingRank vN
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
    {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan Anv z∈A
    liftγ prem vU vN view spine chain typed acc rank target
    with StructuralNamePostPlan.plain-Λ-child plan refl
       | StructuralNameChainPlan.plain-Λ-child chain-plan refl liftγ
           chain typed
structural-name-plain-Λ-equal worker {γ = γ} {γᴸ = γᴸ}
    {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan Anv z∈A
    liftγ prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-Λ-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    Anv z∈A liftγ vU target⊢ child-rel
  where
  targetᴸ = structural-target-lift-left X⊑★ target

  child-rel =
    worker fuel-step catchup⁻-embed inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed acc rank targetᴸ

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


structural-name-smart-Λ-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ Δᵐ}
      {W : CTI2.World Δᴸ Δᴿ Δ}
      {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
      {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
      {U : Term (suc Δᴸ)} {N : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ}
      {p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ `∀ B}
      {q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W (`∀ A) E q)
    → StructuralNameChainPlan {fuel = fuel} W γ (`∀ A) E q plan
    → NonVar A
    → Fin.zero ∈ᵗ A
    → (liftW : CTI2.SmartCommaLiftᴸ W Wᵐ)
    → CTI2.SmartLiftCtxᴸ γ γᵐ
    → Wᵐ CTI2.∣ γᵐ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ (`∀ A)
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ʳ_ (pendingRank vN
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
structural-name-smart-Λ-equal worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed acc rank target
    with StructuralNamePostPlan.smart-Λ-child plan refl liftW
       | StructuralNameChainPlan.smart-Λ-child chain-plan refl liftW
           liftγ chain typed
structural-name-smart-Λ-equal worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan)
    with structural-smart-liftᴸ
      (StructuralTargetInstantiationPackage.structural-ext target)
      liftW
structural-name-smart-Λ-equal worker {γ = γ} {γᵐ = γᵐ}
    {B = B} {X = X}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan Anv z∈A
    liftW liftγ prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan)
    | record { premise-plan = planᵐ ; post-lift = liftW′ } =
  CTI2.Λ⊑²-smart-comma Anv z∈A liftW′ liftγ′ vU target⊢
    child-rel
    (ECR.transport⊑ᵂ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      _)
  where
  targetᵐ = record
    { Δᴿ′ = StructuralTargetInstantiationPackage.Δᴿ′ target
    ; χs = StructuralTargetInstantiationPackage.χs target
    ; Δ′ = _
    ; W′ = _
    ; structural-ext = planᵐ
    ; final = StructuralTargetInstantiationPackage.final target
    ; final-value =
        StructuralTargetInstantiationPackage.final-value target
    ; post-reduction =
        StructuralTargetInstantiationPackage.post-reduction target
    }

  child-rel =
    worker fuel-step catchup⁻-embed inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed acc rank targetᵐ

  liftγ′ =
    mapCtxᴿ-smartLiftCtxᴸ
      (structural-world-extendᴿ
        (StructuralTargetInstantiationPackage.structural-ext target))
      (structural-world-extendᴿ planᵐ)
      liftγ

  postTarget⊢ =
    CTI2T.target-typing² child-rel

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (smartLiftCtxᴸ-target-ctx liftγ′)
      (subst≡ (λ Σ → ⟨ _ , Σ , _ ⟩ ⊢ _ ⦂ _)
        (smartCommaLift-target-store liftW′)
        postTarget⊢)


structural-name-reveal-equal : StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
      {U : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ?}
      {c : Conv↑ Δᴸ A A′}
      {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
      {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A′ E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A′ E q plan
    → CTI2.ImpEnvMono W Wᵖ
    → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
    → Wᵖ CTI2.∣ γᵖ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ A′
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ʳ_ (pendingRank vN
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
structural-name-reveal-equal worker {B = B} {X = X} {c = c}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan mono rb sc
    c⊢ prem vU vN view spine chain typed acc rank target
    with StructuralNamePostPlan.reveal-child plan {c = c} rb
       | StructuralNameChainPlan.reveal-child chain-plan {c = c} rb sc
           chain typed
structural-name-reveal-equal worker {B = B} {X = X} {c = c}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan mono rb sc
    c⊢ prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-reveal-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    mono rb sc c⊢
    (worker fuel-step catchup⁻-embed inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed acc rank
      (structural-target-rebase-left rb target))


structural-name-conceal-equal :
  StructuralNameConcealEqualOKᵀ
  → StructuralNameInstantiationEqualᵀ
  → ∀ {fuel Δᴸ Δᴿ Δ}
      {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
      {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
      {U : Term Δᴸ} {N : Term Δᴿ}
      {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
      {E : Ty Δᴿ} {X : TyVar Δᴿ} {Xᴸ? Xᴿ?}
      {c : Conv↓ Δᴸ A A′}
      {p : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
      {q : A′ CTI2.⊑ᵂ⟨ W ⟩ E}
    → FuelStepSurface fuel
    → Catchup⁻Embedᵀ
    → inst-alloc-decreaseᵀ
    → (plan : StructuralNamePostPlan W A′ E q)
    → StructuralNameChainPlan {fuel = fuel} W γ A′ E q plan
    → CTI2.SourceConcealPartnerOK Wᵖ U c Xᴿ? N
    → CTI2.ImpEnvMono W Wᵖ
    → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
    → CTI2.SameCtx γ γᵖ
    → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
    → Wᵖ CTI2.∣ γᵖ ⊢² U ⊑ N ∶ p
    → Value U
    → (vN : Value N)
    → AllValueView N
    → (spine : InstantiationSpine (B [ ＇ X ]ᵗ) E)
    → (chain : TargetFrameAbsorptionChain W γ A′
        (name-type-app-frame B X refl refl ▻ⁱ spine) q)
    → (typed : SpineTypedʷ {fuel = fuel} W
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<_ (pendingCastMass vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → Acc _<ʳ_ (pendingRank vN
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → (target : StructuralTargetInstantiationPackage W N
        (name-type-app-frame B X refl refl ▻ⁱ spine))
    → StructuralTargetInstantiationPackage.W′ target CTI2.∣
        ECR.mapCtxᴿ
          (structural-world-extendᴿ
            (StructuralTargetInstantiationPackage.structural-ext target))
          γ
        ⊢² U ↓ c ⊑
          StructuralTargetInstantiationPackage.final target ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralTargetInstantiationPackage.structural-ext target))
            q
structural-name-conceal-equal ok-equal worker {B = B} {X = X} {c = c}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan ok mono rb
    sc c⊢ prem vU vN view spine chain typed acc rank target
    with StructuralNamePostPlan.conceal-child plan {c = c} rb
       | StructuralNameChainPlan.conceal-child chain-plan {c = c} rb sc
           chain typed
structural-name-conceal-equal ok-equal worker {B = B} {X = X} {c = c}
    fuel-step catchup⁻-embed inst-decrease plan chain-plan ok mono rb
    sc c⊢ prem vU vN view spine chain typed acc rank target
    | q₀ , child-plan
    | child-chain , (child-typed , child-chain-plan) =
  structural-conceal-replay
    (StructuralTargetInstantiationPackage.structural-ext target)
    mono rb sc c⊢
    (ok-equal rb ok spine target)
    (worker fuel-step catchup⁻-embed inst-decrease
      child-plan child-chain-plan prem vU vN
      (name-type-app-frame B X refl refl ▻ⁱ spine)
      child-chain child-typed acc rank
      (structural-target-tag-rebase-left rb target))


structural-value-instantiation : StructuralValueInstantiationᵀ
structural-value-instantiation {fuel = fuel} {W = W} {γ = γ}
    {A = A} {B = B} {R = R} {q = q}
    surfaces name-worker fuel-step catchup⁻-embed inst-decrease plan
    chain-plan rel vM vV view target =
  erase-structural-name-root surfaces name-worker fuel-step catchup⁻-embed
    inst-decrease plan chain-plan rel vM
    (renameᵗᵐ-preserves-Value wk↪ᵗ vV)
    (SpineValueProof.rename-all-value-view wk↪ᵗ view)
    []ⁱ
    (root-value-instantiation-frame-chain
      {W = W} {γ = γ} {A = A} {B = B} {R = R} {q = q})
    (root-value-instantiation-spine-typed
      {fuel = fuel} {W = W} {A = A} {B = B} {R = R})
    target
