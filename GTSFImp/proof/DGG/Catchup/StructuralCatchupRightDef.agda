module proof.DGG.Catchup.StructuralCatchupRightDef where

-- File Charter:
--   * Defines the LG-3 internal right-catch-up result package that carries
--     `StructuralWorldExtendᴿ`.
--   * Preserves the nine conversion-wrapper cases with their direct
--     generator, representation, and generator-position evidence.
--   * Provides erasure adapters to the public `WorldExtendᴿ` result surfaces
--     used by `ValueCatchupRightAt` and `ExtraCastRightAt`.
--   * Keeps structural traces internal; no public fuel statement is widened.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; ⇑ᵗ; renameNonVar)
open import TyStore using (_∋_⦂_)
open import Consistency using
  (Env∼; _↪ᵗ_; _⊢_∼_; inst_; instᵐ; wk↪ᵗ; toRenameᵗ)
open import Conversion using
  (Conv↑; Conv↓; seal; unseal; id↓; _⊢↑[_⦂_]_; _⊢↓[_⦂_]_)
open import Imprecision using (X⊑★)
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩; _《_》; _↑_;
   _↓_; renameᵗᵐ)
open import Reduction using
  (StoreChanges; []; _∷_; keep; _—→[_]_; _—↠[_]_; _—→[_]⟨_⟩_;
   _—↠[_]⟨_⟩_; _∎[]; bind;
   applyConsistency; applyConsistencies; applyStores; applyTys)
open import proof.Reduction using
  (cast-↠; applyConsistencies-Inert; _++χ_; applyTys-++;
   applyTys-★; cast-applyConsistencies-++; composeReduction; reveal-↠;
   conceal-↠; applyReveals; applyConceals)

import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetExtend as TE
import proof.DGG.ExtraCastRight2 as ECR
open TE using (source-insert; target-center-reflect)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
  using (StructuralWorldExtendSplit; splitStructuralWorldExtendᴿ;
         structural-world-extendᴿ; composeStructuralWorldExtendᴿ;
         mapCtxᴿ-structural-compose; mapCtxᴿ-structural-keep)
open import proof.DGG.Catchup.StructuralWorldRebaseProof using
  (structural-rebase-at-pullback;
   structural-reverse-rebase-at-pullback)
open import proof.DGG.Catchup.StructuralWorldEvidenceProof using
  (mapCtxᴿ-sameCtx; mapCtxᴿ-liftCtxᴸ; mapCtxᴿ-smartLiftCtxᴸ;
   liftCtxᴸ-target-ctx; smartCommaLift-target-store;
   smartLiftCtxᴸ-target-ctx; structural-source-reveal;
   structural-source-conceal; structural-target-reveal;
   structural-target-conceal; structural-target-member;
   structural-source-reveal-position;
   structural-source-conceal-position;
   structural-target-reveal-position;
   structural-target-conceal-position)
open import proof.DGG.Catchup.StructuralFrameOutcomeDef using
  (StructuralFrameOutcome; structural-frame-value; structural-frame-keep)
open import proof.DGG.Catchup.StructuralWorldLiftLeftProof using
  (structural-lift-left)
open import proof.DGG.Catchup.StructuralWorldSmartLiftDef
open import proof.DGG.Catchup.StructuralWorldSmartLiftProof using
  (structural-smart-liftᴸ)
open import proof.DGG.Catchup.StructuralSourceLambdaReplayProof using
  (structural-Λ-replay; structural-smart-Λ-replay)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (TargetCastBound; ValueCatchupRight²; ValueCatchupRightAt;
   ExtraCastRightAt; InstCatchupRightAt; castSize)
import proof.DGG.CastTermImprecision2Typing as CTI2T
open import proof.DGG.ConversionPivotAlignment using
  (generator-absent; revealGeneratorPosition; concealGeneratorPosition)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


record StructuralCatchupRightResult {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (M : Term Δᴸ) (M″ : Term Δᴿ)
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    (q : A ⊑ᵂ⟨ W ⟩ B) : Set₁ where
  field
    Δᴿ′ : TyCtx
    χs : StoreChanges Δᴿ Δᴿ′
    Δ′ : TyCtx
    W′ : World Δᴸ Δᴿ′ Δ′
    structural-ext : StructuralWorldExtendᴿ χs W W′
    N′ : Term Δᴿ′
    final-value : Value N′
    post-reduction : M″ —↠[ χs ] N′
    final-relation :
      W′ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ structural-ext) γ
        ⊢² M ⊑ N′ ∶
          ECR.transport⊑ᵂ (structural-world-extendᴿ structural-ext) q


StructuralCatchupRightPayload : ∀ {Δᴸ Δᴿ Δ}
  → (W : World Δᴸ Δᴿ Δ)
  → CtxImp W
  → Term Δᴸ
  → Term Δᴿ
  → ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
  → A ⊑ᵂ⟨ W ⟩ B
  → Set₁
StructuralCatchupRightPayload = StructuralCatchupRightResult


PairedConcealRevealPeelᵀ : Set
PairedConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


SourceOnlyConcealRevealPeelᵀ : Set
SourceOnlyConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {N′ V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → ((N′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record TargetRevealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-conceal-reveal :
      PairedConcealRevealPeelᵀ
    source-opened-conceal-reveal :
      SourceOnlyConcealRevealPeelᵀ


record TargetConcealKeepOutcomeContinuationsᵀ : Set₁ where
  field
    paired-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢²
          (V₀ ↓ id↓ A)
          ⊑ (V₀′ ↓ id↓ B) ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → (V₀′ ↓ id↓ B) —→[ keep ] V₀′
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q

    source-opened-id-conceal :
      ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
        {A : Ty Δᴸ} {B : Ty Δᴿ}
        {q : A ⊑ᵂ⟨ W ⟩ B}
      → Value V₀
      → Value V₀′
      → W ∣ γ ⊢² (V₀ ↓ id↓ A) ⊑ V₀′ ∶ q
      → (V₀ ↓ id↓ A) —→[ keep ] V₀
      → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record RestatedDispatcherKeepOutcomesᵀ : Set₁ where
  field
    target-reveal-outcomes : TargetRevealKeepOutcomeContinuationsᵀ
    target-conceal-outcomes : TargetConcealKeepOutcomeContinuationsᵀ


data SourceΛReplayStack {Δᴸ₀ Δᴿ Δ₀}
    (W₀ : World Δᴸ₀ Δᴿ Δ₀) (γ₀ : CtxImp W₀)
    (M₀ : Term Δᴸ₀) {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    (q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀)
    : ∀ {Δᴸ Δ}
      → (W : World Δᴸ Δᴿ Δ)
      → CtxImp W
      → Term Δᴸ
      → ∀ {A : Ty Δᴸ} {B : Ty Δᴿ}
      → A ⊑ᵂ⟨ W ⟩ B
      → Set₁ where
  source-Λ-stack-id :
    SourceΛReplayStack W₀ γ₀ M₀ q₀ W₀ γ₀ M₀ q₀

  source-Λ-stack-plain :
    ∀ {Δᴸ Δ}
      {W : World Δᴸ Δᴿ Δ}
      {γ : CtxImp W}
      {γᴸ : CtxImp (CTX.liftWorldLeft W)}
      {U : Term (suc Δᴸ)}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ B}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ (Λ U) q
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTX.LiftCtxᴸ X⊑★ γ γᴸ
    → Value U
    → SourceΛReplayStack W₀ γ₀ M₀ q₀
        (CTX.liftWorldLeft W) γᴸ U p

  source-Λ-stack-smart :
    ∀ {Δᴸ Δ Δᵐ}
      {W : World Δᴸ Δᴿ Δ}
      {Wᵐ : World (suc Δᴸ) Δᴿ Δᵐ}
      {γ : CtxImp W} {γᵐ : CtxImp Wᵐ}
      {U : Term (suc Δᴸ)}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ Wᵐ ⟩ B}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ (Λ U) q
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTX.SmartCommaLiftᴸ W Wᵐ
    → CTX.SmartLiftCtxᴸ γ γᵐ
    → Value U
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ Wᵐ γᵐ U p


source-Λ-stack-replay-here : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q
  → ∀ {N : Term Δᴿ}
  → W ∣ γ ⊢² M ⊑ N ∶ q
  → W₀ ∣ γ₀ ⊢² M₀ ⊑ N ∶ q₀
source-Λ-stack-replay-here source-Λ-stack-id rel = rel
source-Λ-stack-replay-here
    (source-Λ-stack-plain stack Anv z∈A liftγ vU) rel =
  source-Λ-stack-replay-here stack
    (subst≡ (λ γ′ → _ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (ECR.mapCtxᴿ-same _)
      (structural-Λ-replay structural-[] Anv z∈A liftγ vU
        target⊢ rel′))
  where
  rel′ =
    subst≡ (λ γ′ → _ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (ECR.mapCtxᴿ-same _))
      rel

  target⊢γ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (liftCtxᴸ-target-ctx liftγ)
      (CTI2T.target-typing² rel)

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (cong CTX.tgtCtxʷ (ECR.mapCtxᴿ-same _)))
      target⊢γ
source-Λ-stack-replay-here
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) rel =
  source-Λ-stack-replay-here stack
    (subst≡ (λ γ′ → _ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (ECR.mapCtxᴿ-same _)
      (structural-smart-Λ-replay structural-[] Anv z∈A liftW liftγ vU
        target⊢ rel′))
  where
  rel′ =
    subst≡ (λ γ′ → _ ∣ γ′ ⊢² _ ⊑ _ ∶ _)
      (sym (ECR.mapCtxᴿ-same _))
      rel

  target⊢γ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (smartLiftCtxᴸ-target-ctx liftγ)
      (subst≡ (λ Σ → ⟨ _ , Σ , _ ⟩ ⊢ _ ⦂ _)
        (smartCommaLift-target-store liftW)
        (CTI2T.target-typing² rel))

  target⊢ =
    subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (cong CTX.tgtCtxʷ (ECR.mapCtxᴿ-same _)))
      target⊢γ


record SourceΛReplayStackTransport {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {Δᴿ′ Δ₀′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀′ : World Δᴸ₀ Δᴿ′ Δ₀′}
    (plan₀ : StructuralWorldExtendᴿ χs W₀ W₀′) : Set₁ where
  field
    Δ′ : TyCtx
    W′ : World Δᴸ Δᴿ′ Δ′
    current-plan : StructuralWorldExtendᴿ χs W W′
    stack′ :
      SourceΛReplayStack
        W₀′
        (ECR.mapCtxᴿ (structural-world-extendᴿ plan₀) γ₀)
        M₀
        (ECR.transport⊑ᵂ (structural-world-extendᴿ plan₀) q₀)
        W′
        (ECR.mapCtxᴿ (structural-world-extendᴿ current-plan) γ)
        M
        (ECR.transport⊑ᵂ (structural-world-extendᴿ current-plan) q)


source-Λ-stack-transport : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {Δᴿ′ Δ₀′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀′ : World Δᴸ₀ Δᴿ′ Δ₀′}
    (plan₀ : StructuralWorldExtendᴿ χs W₀ W₀′)
  → SourceΛReplayStackTransport stack plan₀
source-Λ-stack-transport source-Λ-stack-id plan₀ = record
  { Δ′ = _
  ; W′ = _
  ; current-plan = plan₀
  ; stack′ = source-Λ-stack-id
  }
source-Λ-stack-transport
    (source-Λ-stack-plain stack Anv z∈A liftγ vU) plan₀
    with source-Λ-stack-transport stack plan₀
source-Λ-stack-transport
    (source-Λ-stack-plain stack Anv z∈A liftγ vU) plan₀
    | record { W′ = W′ ; current-plan = plan ; stack′ = stack′ } =
  record
    { Δ′ = _
    ; W′ = CTX.liftWorldLeft W′
    ; current-plan = structural-lift-left plan X⊑★
    ; stack′ =
        source-Λ-stack-plain stack′ Anv z∈A
          (mapCtxᴿ-liftCtxᴸ
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (structural-lift-left plan X⊑★))
            liftγ)
          vU
    }
source-Λ-stack-transport
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) plan₀
    with source-Λ-stack-transport stack plan₀
source-Λ-stack-transport
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) plan₀
    | record { current-plan = plan ; stack′ = stack′ }
    with structural-smart-liftᴸ plan liftW
source-Λ-stack-transport
    (source-Λ-stack-smart stack Anv z∈A liftW liftγ vU) plan₀
    | record { current-plan = plan ; stack′ = stack′ }
    | record { Wᵐ′ = Wᵐ′ ; premise-plan = planᵐ
             ; post-lift = liftW′ } =
  record
    { Δ′ = _
    ; W′ = Wᵐ′
    ; current-plan = planᵐ
    ; stack′ =
        source-Λ-stack-smart stack′ Anv z∈A liftW′
          (mapCtxᴿ-smartLiftCtxᴸ
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ planᵐ)
            liftγ)
          vU
    }


source-Λ-stack-target-bind-child : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {R : Ty Δᴿ} {Δ₀¹} {π₀ : Δ₀ ↪ᵗ Δ₀¹}
    {W₀¹ : World Δᴸ₀ (suc Δᴿ) Δ₀¹}
  → (ins₀ : TE.TargetInsert wk↪ᵗ π₀ W₀ W₀¹)
  → (follows₀ : CTX.targetStoreʷ W₀¹ ≡
      applyStores (bind R ∷ []) (CTX.targetStoreʷ W₀))
  → SourceΛReplayStackTransport stack
      (structural-bind ins₀ follows₀ structural-[])
source-Λ-stack-target-bind-child stack ins₀ follows₀ =
  source-Λ-stack-transport stack
    (structural-bind ins₀ follows₀ structural-[])


source-Λ-stack-unlift-plan : ∀ {Δᴸ₀ Δᴿ Δ₀}
    {W₀ : World Δᴸ₀ Δᴿ Δ₀} {γ₀ : CtxImp W₀}
    {M₀ : Term Δᴸ₀} {A₀ : Ty Δᴸ₀} {B₀ : Ty Δᴿ}
    {q₀ : A₀ ⊑ᵂ⟨ W₀ ⟩ B₀}
    {Δᴸ Δ} {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
    (stack : SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ M q)
    {Δᴿ′ Δ₀′} {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀′ : World Δᴸ₀ Δᴿ′ Δ₀′}
    (plan₀ : StructuralWorldExtendᴿ χs W₀ W₀′)
    (transported : SourceΛReplayStackTransport stack plan₀)
  → ∀ {N′ : Term Δᴿ′}
  → SourceΛReplayStackTransport.W′ transported ∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (SourceΛReplayStackTransport.current-plan transported))
        γ
      ⊢² M ⊑ N′ ∶
        ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (SourceΛReplayStackTransport.current-plan transported))
          q
  → W₀′ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan₀) γ₀
      ⊢² M₀ ⊑ N′ ∶
        ECR.transport⊑ᵂ (structural-world-extendᴿ plan₀) q₀
source-Λ-stack-unlift-plan stack plan₀ transported rel =
  source-Λ-stack-replay-here
    (SourceΛReplayStackTransport.stack′ transported)
    rel


erase-structural-catchup-result : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → StructuralCatchupRightResult W γ M M″ q
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
    Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
    Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
    Σ[ N′ ∈ Term Δᴿ′ ]
      (Value N′
        × (M″ —↠[ χs ] N′)
        × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
            ECR.transport⊑ᵂ ext q))
erase-structural-catchup-result result =
  StructuralCatchupRightResult.Δᴿ′ result ,
  StructuralCatchupRightResult.χs result ,
  StructuralCatchupRightResult.Δ′ result ,
  StructuralCatchupRightResult.W′ result ,
  structural-world-extendᴿ
    (StructuralCatchupRightResult.structural-ext result) ,
  StructuralCatchupRightResult.N′ result ,
  StructuralCatchupRightResult.final-value result ,
  StructuralCatchupRightResult.post-reduction result ,
  StructuralCatchupRightResult.final-relation result


rel-target-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A ⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ⊑ N ∶ p
  → W ∣ γ ⊢² M ⊑ N ∶
      subst≡ (λ C → A ⊑ᵂ⟨ W ⟩ C) eq p
rel-target-transportᴿ refl p rel = rel


structural-no-target-at-source : ∀ {Δᴸ Δᴿ Δᴿ′ Δ₀ Δ₀′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ′ Δ₀′}
    {X : TyVar Δᴸ}
  → StructuralWorldExtendᴿ χs W₀ W₀′
  → CTX.NoTargetOccupantAtSource W₀ X
  → CTX.NoTargetOccupantAtSource W₀′ X
structural-no-target-at-source structural-[] no-target = no-target
structural-no-target-at-source (structural-keep plan) no-target =
  structural-no-target-at-source plan no-target
structural-no-target-at-source {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) no-target =
  structural-no-target-at-source plan no-target′
  where
  no-target′ : CTX.NoTargetOccupantAtSource W₁ X
  no-target′ (Y′ , eq)
      with TE.target-center-reflect ins
        (trans eq (TE.source-insert ins X))
  no-target′ (Y′ , eq) | Y , _ , target-eq =
    no-target (Y , target-eq)


structural-source-star-mark : ∀ {Δᴸ Δᴿ Δᴿ′ Δ₀ Δ₀′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ′ Δ₀′}
    {X : TyVar Δᴸ}
  → StructuralWorldExtendᴿ χs W₀ W₀′
  → CTX.impEnvʷ W₀ (toRenameᵗ (CTX.ηᴸʷ W₀) X) ≡ X⊑★
  → CTX.impEnvʷ W₀′ (toRenameᵗ (CTX.ηᴸʷ W₀′) X) ≡ X⊑★
structural-source-star-mark structural-[] mark = mark
structural-source-star-mark (structural-keep plan) mark =
  structural-source-star-mark plan mark
structural-source-star-mark {W₀ = W₀} {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) mark =
  structural-source-star-mark plan mark′
  where
  mark′ :
    CTX.impEnvʷ W₁ (toRenameᵗ (CTX.ηᴸʷ W₁) X) ≡ X⊑★
  mark′ =
    trans (cong (CTX.impEnvʷ W₁) (TE.source-insert ins X))
      (trans
        (TE.impEnv-insert ins (toRenameᵗ (CTX.ηᴸʷ W₀) X)) mark)


structural-catchup-refl : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {N′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value N′
  → W ∣ γ ⊢² M ⊑ N′ ∶ q
  → StructuralCatchupRightResult W γ M N′ q
structural-catchup-refl {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {N′ = N′} {q = q} vN′ rel =
  record
    { Δᴿ′ = Δᴿ
    ; χs = []
    ; Δ′ = Δ
    ; W′ = W
    ; structural-ext = structural-[]
    ; N′ = N′
    ; final-value = vN′
    ; post-reduction = N′ ∎[]
    ; final-relation =
        subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ N′ ∶ q)
          (sym (ECR.mapCtxᴿ-same γ)) rel
    }


structural-catchup-keep-step : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ N′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value N′
  → M″ —→[ keep ] N′
  → W ∣ γ ⊢² M ⊑ N′ ∶ q
  → StructuralCatchupRightResult W γ M M″ q
structural-catchup-keep-step {Δᴿ = Δᴿ} {Δ = Δ} {W = W} {γ = γ}
    {M = M} {M″ = M″} {N′ = N′} {q = q}
    vN′ step rel =
  record
    { Δᴿ′ = Δᴿ
    ; χs = keep ∷ []
    ; Δ′ = Δ
    ; W′ = W
    ; structural-ext = structural-keep structural-[]
    ; N′ = N′
    ; final-value = vN′
    ; post-reduction =
        M″ —→[ keep ]⟨ step ⟩
        N′ ∎[]
    ; final-relation =
        subst≡ (λ γ′ → W ∣ γ′ ⊢² M ⊑ N′ ∶ q)
          (sym (ECR.mapCtxᴿ-keep γ)) rel
    }


structural-catchup-prepend-keep-stutter : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ M₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → M″ —→[ keep ] M₁
  → StructuralCatchupRightResult W γ M M₁ q
  → StructuralCatchupRightResult W γ M M″ q
structural-catchup-prepend-keep-stutter
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {γ = γ}
    {M″ = M″} {M₁ = M₁} {q = q}
    step result =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result
    ; χs = keep ∷ StructuralCatchupRightResult.χs result
    ; Δ′ = StructuralCatchupRightResult.Δ′ result
    ; W′ = StructuralCatchupRightResult.W′ result
    ; structural-ext =
        structural-keep
          (StructuralCatchupRightResult.structural-ext result)
    ; N′ = StructuralCatchupRightResult.N′ result
    ; final-value = StructuralCatchupRightResult.final-value result
    ; post-reduction =
        M″ —→[ keep ]⟨ step ⟩
        M₁ —↠[ χs ]⟨ tail ⟩
        N′ ∎[]
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ result ∣ γ′ ⊢² _
            ⊑ _ ∶
            ECR.transport⊑ᵂ
              (structural-world-extendᴿ
                (structural-keep
                  (StructuralCatchupRightResult.structural-ext result)))
              q)
          (sym (mapCtxᴿ-structural-keep
            (StructuralCatchupRightResult.structural-ext result) γ))
          (StructuralCatchupRightResult.final-relation result)
    }
  where
  χs = StructuralCatchupRightResult.χs result
  tail = StructuralCatchupRightResult.post-reduction result
  N′ = StructuralCatchupRightResult.N′ result


structural-catchup-prepend-keep : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ M₁ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → M″ —→[ keep ] M₁
  → W ∣ γ ⊢² M ⊑ M₁ ∶ q
  → StructuralCatchupRightResult W γ M M₁ q
  → StructuralCatchupRightResult W γ M M″ q
structural-catchup-prepend-keep step rel₁ =
  structural-catchup-prepend-keep-stutter step


structural-catchup-source-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c : ν ⊢ A ∼ A′)
  → (result : StructuralCatchupRightResult W γ M M″ p)
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) M″ q
structural-catchup-source-cast {q = q} c result = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result
  ; χs = StructuralCatchupRightResult.χs result
  ; Δ′ = StructuralCatchupRightResult.Δ′ result
  ; W′ = StructuralCatchupRightResult.W′ result
  ; structural-ext = StructuralCatchupRightResult.structural-ext result
  ; N′ = StructuralCatchupRightResult.N′ result
  ; final-value = StructuralCatchupRightResult.final-value result
  ; post-reduction = StructuralCatchupRightResult.post-reduction result
  ; final-relation =
      CTI2.cast⊑² c
        (StructuralCatchupRightResult.final-relation result)
        (ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralCatchupRightResult.structural-ext result))
          q)
  }


structural-catchup-target-inert-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → Inert c′
  → (result : StructuralCatchupRightResult W γ M M″ p)
  → StructuralCatchupRightResult W γ M (M″ ⟨ c′ ⟩) q
structural-catchup-target-inert-cast {q = q}
    c′ inert result = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result
  ; χs = StructuralCatchupRightResult.χs result
  ; Δ′ = StructuralCatchupRightResult.Δ′ result
  ; W′ = StructuralCatchupRightResult.W′ result
  ; structural-ext = StructuralCatchupRightResult.structural-ext result
  ; N′ = StructuralCatchupRightResult.N′ result
      ⟨ applyConsistencies (StructuralCatchupRightResult.χs result) c′ ⟩
  ; final-value =
      StructuralCatchupRightResult.final-value result 《
        applyConsistencies-Inert
          (StructuralCatchupRightResult.χs result) inert 》
  ; post-reduction =
      cast-↠ c′ (StructuralCatchupRightResult.post-reduction result)
  ; final-relation =
      CTI2.⊑cast²
        (applyConsistencies (StructuralCatchupRightResult.χs result) c′)
        (StructuralCatchupRightResult.final-relation result)
        (ECR.transport⊑ᵂ
          (structural-world-extendᴿ
            (StructuralCatchupRightResult.structural-ext result))
          q)
  }


structural-catchup-source-reveal-neutral : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → revealGeneratorPosition c⊢ ≡ generator-absent
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralCatchupRightResult W γ (M ↑ c) M′ q
structural-catchup-source-reveal-neutral {q = q}
    c⊢ empty child = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
  ; χs = StructuralCatchupRightResult.χs child
  ; Δ′ = StructuralCatchupRightResult.Δ′ child
  ; W′ = StructuralCatchupRightResult.W′ child
  ; structural-ext = StructuralCatchupRightResult.structural-ext child
  ; N′ = StructuralCatchupRightResult.N′ child
  ; final-value = StructuralCatchupRightResult.final-value child
  ; post-reduction = StructuralCatchupRightResult.post-reduction child
  ; final-relation =
      CTI2.reveal⊑-identity
        (structural-source-reveal plan c⊢)
        (trans (structural-source-reveal-position plan c⊢) empty)
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
  }
  where
  plan = StructuralCatchupRightResult.structural-ext child


structural-catchup-source-reveal-only : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
  → CTX.NoTargetOccupantAtSource W Xᴸ
  → Rᴸ ⊑ᵂ⟨ W ⟩ ★
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralCatchupRightResult W γ (M ↑ c) M′ q
structural-catchup-source-reveal-only {Rᴸ = Rᴸ} {q = q}
    c⊢ active mark no-target representation child = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
  ; χs = StructuralCatchupRightResult.χs child
  ; Δ′ = StructuralCatchupRightResult.Δ′ child
  ; W′ = StructuralCatchupRightResult.W′ child
  ; structural-ext = plan
  ; N′ = StructuralCatchupRightResult.N′ child
  ; final-value = StructuralCatchupRightResult.final-value child
  ; post-reduction = StructuralCatchupRightResult.post-reduction child
  ; final-relation =
      CTI2.reveal⊑-only²
        (structural-source-reveal plan c⊢)
        (λ empty → active
          (trans (sym (structural-source-reveal-position plan c⊢)) empty))
        (structural-source-star-mark plan mark)
        (λ Y eq → structural-no-target-at-source plan no-target (Y , eq))
        (subst≡ (λ T → Rᴸ ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-★ χs)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan)
            representation))
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
  }
  where
  χs = StructuralCatchupRightResult.χs child
  W′ = StructuralCatchupRightResult.W′ child
  plan = StructuralCatchupRightResult.structural-ext child


structural-catchup-source-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ Rᴸ : Ty Δᴸ} {B Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → CTX.targetStoreʷ W ∋ Xᴿ ⦂ Rᴿ
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → StructuralRebaseAtPullbackReplay
      (StructuralCatchupRightResult.structural-ext child) rb
  → StructuralCatchupRightResult W γ (M ↑ c) M′ q
structural-catchup-source-reveal {γ = γ} {q = q}
    c⊢ active target-member representation mono rb sc child replay
    with structural-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb replay
structural-catchup-source-reveal {γ = γ} {q = q}
    c⊢ active target-member representation mono rb sc child replay
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = W′
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
    ; final-value = StructuralCatchupRightResult.final-value child
    ; post-reduction = StructuralCatchupRightResult.post-reduction child
    ; final-relation =
        CTI2.reveal⊑²
          (structural-source-reveal plan c⊢)
          (λ empty → active
            (trans
              (sym (structural-source-reveal-position plan c⊢)) empty))
          (structural-target-member plan target-member)
          (ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            representation)
          (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }


structural-catchup-source-conceal-neutral : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → concealGeneratorPosition c⊢ ≡ generator-absent
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralCatchupRightResult W γ (M ↓ c) M′ q
structural-catchup-source-conceal-neutral {q = q}
    c⊢ empty child = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
  ; χs = StructuralCatchupRightResult.χs child
  ; Δ′ = StructuralCatchupRightResult.Δ′ child
  ; W′ = StructuralCatchupRightResult.W′ child
  ; structural-ext = plan
  ; N′ = StructuralCatchupRightResult.N′ child
  ; final-value = StructuralCatchupRightResult.final-value child
  ; post-reduction = StructuralCatchupRightResult.post-reduction child
  ; final-relation =
      CTI2.conceal⊑-identity
        (structural-source-conceal plan c⊢)
        (trans (structural-source-conceal-position plan c⊢) empty)
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
  }
  where
  plan = StructuralCatchupRightResult.structural-ext child


structural-catchup-source-conceal : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ Rᴸ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → concealGeneratorPosition c⊢ ≢ generator-absent
  → CTX.impEnvʷ W (toRenameᵗ (CTX.ηᴸʷ W) Xᴸ) ≡ X⊑★
  → CTX.NoTargetOccupantAtSource W Xᴸ
  → Rᴸ ⊑ᵂ⟨ W ⟩ ★
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralCatchupRightResult W γ (M ↓ c) M′ q
structural-catchup-source-conceal {Rᴸ = Rᴸ} {q = q}
    c⊢ active mark no-target representation child = record
  { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
  ; χs = StructuralCatchupRightResult.χs child
  ; Δ′ = StructuralCatchupRightResult.Δ′ child
  ; W′ = StructuralCatchupRightResult.W′ child
  ; structural-ext = plan
  ; N′ = StructuralCatchupRightResult.N′ child
  ; final-value = StructuralCatchupRightResult.final-value child
  ; post-reduction = StructuralCatchupRightResult.post-reduction child
  ; final-relation =
      CTI2.conceal⊑²
        (structural-source-conceal plan c⊢)
        (λ empty → active
          (trans (sym (structural-source-conceal-position plan c⊢)) empty))
        (structural-source-star-mark plan mark)
        (λ Y eq → structural-no-target-at-source plan no-target (Y , eq))
        (subst≡ (λ T → Rᴸ ⊑ᵂ⟨ W′ ⟩ T)
          (applyTys-★ χs)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan)
            representation))
        (StructuralCatchupRightResult.final-relation child)
        (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
  }
  where
  χs = StructuralCatchupRightResult.χs child
  W′ = StructuralCatchupRightResult.W′ child
  plan = StructuralCatchupRightResult.structural-ext child


structural-catchup-target-reveal-neutral : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴿ : TyVar Δᴿ} {c′ : Conv↑ Δᴿ B B′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′⊢ : CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c′⊢ ≡ generator-absent
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralFrameOutcome
      (StructuralCatchupRightResult.N′ child
        ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
  → (∀ {Δᵒ}
      {Wᵒ : World Δᴸ
        (StructuralCatchupRightResult.Δᴿ′ child) Δᵒ}
      {N₁}
      → (plan : StructuralWorldExtendᴿ
          (StructuralCatchupRightResult.χs child) W Wᵒ)
      → Wᵒ ∣
          ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
          ⊢² M ⊑
            (StructuralCatchupRightResult.N′ child
              ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
            ∶ ECR.transport⊑ᵂ
                (structural-world-extendᴿ plan) q
      → (StructuralCatchupRightResult.N′ child
           ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
          —→[ keep ] N₁
      → Value N₁
      → StructuralCatchupRightResult W γ M (M′ ↑ c′) q)
  → StructuralCatchupRightResult W γ M (M′ ↑ c′) q
structural-catchup-target-reveal-neutral {c′ = c′} {q = q}
    c′⊢ empty child (structural-frame-value finalV) keep-cont =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = StructuralCatchupRightResult.W′ child
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
        ↑ applyReveals χs c′
    ; final-value = finalV
    ; post-reduction =
        reveal-↠ c′ (StructuralCatchupRightResult.post-reduction child)
    ; final-relation =
        CTI2.⊑reveal²
          (structural-target-reveal plan c′⊢)
          (trans (structural-target-reveal-position plan c′⊢) empty)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
  plan = StructuralCatchupRightResult.structural-ext child
structural-catchup-target-reveal-neutral {c′ = c′} {q = q}
    c′⊢ empty child (structural-frame-keep step finalV) keep-cont =
  keep-cont plan frame-rel step finalV
  where
  plan = StructuralCatchupRightResult.structural-ext child
  frame-rel =
    CTI2.⊑reveal²
      (structural-target-reveal plan c′⊢)
      (trans (structural-target-reveal-position plan c′⊢) empty)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-target-conceal-neutral : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ Rᴿ : Ty Δᴿ}
    {Xᴿ : TyVar Δᴿ} {c′ : Conv↓ Δᴿ B B′}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′⊢ : CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → concealGeneratorPosition c′⊢ ≡ generator-absent
  → (child : StructuralCatchupRightResult W γ M M′ p)
  → StructuralFrameOutcome
      (StructuralCatchupRightResult.N′ child
        ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
  → (∀ {Δᵒ}
      {Wᵒ : World Δᴸ
        (StructuralCatchupRightResult.Δᴿ′ child) Δᵒ}
      {N₁}
      → (plan : StructuralWorldExtendᴿ
          (StructuralCatchupRightResult.χs child) W Wᵒ)
      → Wᵒ ∣
          ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
          ⊢² M ⊑
            (StructuralCatchupRightResult.N′ child
              ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
            ∶ ECR.transport⊑ᵂ
                (structural-world-extendᴿ plan) q
      → (StructuralCatchupRightResult.N′ child
           ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
          —→[ keep ] N₁
      → Value N₁
      → StructuralCatchupRightResult W γ M (M′ ↓ c′) q)
  → StructuralCatchupRightResult W γ M (M′ ↓ c′) q
structural-catchup-target-conceal-neutral {c′ = c′} {q = q}
    c′⊢ empty child (structural-frame-value finalV) keep-cont =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = StructuralCatchupRightResult.W′ child
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
        ↓ applyConceals χs c′
    ; final-value = finalV
    ; post-reduction =
        conceal-↠ c′ (StructuralCatchupRightResult.post-reduction child)
    ; final-relation =
        CTI2.⊑conceal²
          (structural-target-conceal plan c′⊢)
          (trans (structural-target-conceal-position plan c′⊢) empty)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
  plan = StructuralCatchupRightResult.structural-ext child
structural-catchup-target-conceal-neutral {c′ = c′} {q = q}
    c′⊢ empty child (structural-frame-keep step finalV) keep-cont =
  keep-cont plan frame-rel step finalV
  where
  plan = StructuralCatchupRightResult.structural-ext child
  frame-rel =
    CTI2.⊑conceal²
      (structural-target-conceal plan c′⊢)
      (trans (structural-target-conceal-position plan c′⊢) empty)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-paired-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A B Rᴸ : Ty Δᴸ} {C C′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ C C′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ C} {q : B ⊑ᵂ⟨ W ⟩ C′}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↑[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : CTX.targetStoreʷ W ⊢↑[ Xᴿ ⦂ Rᴿ ] c′)
  → revealGeneratorPosition c⊢ ≡ revealGeneratorPosition c′⊢
  → revealGeneratorPosition c⊢ ≢ generator-absent
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → StructuralRebaseAtPullbackReplay
      (StructuralCatchupRightResult.structural-ext child) rb
  → StructuralFrameOutcome
      (StructuralCatchupRightResult.N′ child
        ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
  → (∀ {N₁}
      → ∀ {Δᵒ}
      → {Wᵒ : World Δᴸ
          (StructuralCatchupRightResult.Δᴿ′ child) Δᵒ}
      → (plan : StructuralWorldExtendᴿ
          (StructuralCatchupRightResult.χs child) W Wᵒ)
      → Wᵒ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
          ⊢² M ↑ c ⊑
            (StructuralCatchupRightResult.N′ child
              ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
            ∶ ECR.transport⊑ᵂ
                (structural-world-extendᴿ plan) q
      → (StructuralCatchupRightResult.N′ child
           ↑ applyReveals (StructuralCatchupRightResult.χs child) c′)
          —→[ keep ] N₁
      → Value N₁
      → StructuralCatchupRightResult W γ (M ↑ c) (M′ ↑ c′) q)
  → StructuralCatchupRightResult W γ (M ↑ c) (M′ ↑ c′) q
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-value finalV) keep-cont
    with structural-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb replay
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-value finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = W′
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
        ↑ applyReveals χs c′
    ; final-value = finalV
    ; post-reduction =
        reveal-↠ c′ (StructuralCatchupRightResult.post-reduction child)
    ; final-relation =
        CTI2.reveal⊑reveal²
          (structural-source-reveal plan c⊢)
          (structural-target-reveal plan c′⊢)
          (trans (structural-source-reveal-position plan c⊢)
            (trans position
              (sym (structural-target-reveal-position plan c′⊢))))
          (λ empty → active
            (trans
              (sym (structural-source-reveal-position plan c⊢)) empty))
          (ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            representation)
          (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-keep step finalV) keep-cont
    with structural-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb replay
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.reveal⊑reveal²
      (structural-source-reveal plan c⊢)
      (structural-target-reveal plan c′⊢)
      (trans (structural-source-reveal-position plan c⊢)
        (trans position
          (sym (structural-target-reveal-position plan c′⊢))))
      (λ empty → active
        (trans (sym (structural-source-reveal-position plan c⊢)) empty))
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        representation)
      (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-paired-conceal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A B Rᴸ : Ty Δᴸ} {C C′ Rᴿ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ C C′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ C} {q : B ⊑ᵂ⟨ W ⟩ C′}
  → (c⊢ : CTX.sourceStoreʷ W ⊢↓[ Xᴸ ⦂ Rᴸ ] c)
  → (c′⊢ : CTX.targetStoreʷ W ⊢↓[ Xᴿ ⦂ Rᴿ ] c′)
  → concealGeneratorPosition c⊢ ≡ concealGeneratorPosition c′⊢
  → concealGeneratorPosition c⊢ ≢ generator-absent
  → Rᴸ ⊑ᵂ⟨ Wᵖ ⟩ Rᴿ
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → StructuralReverseRebaseAtPullbackReplay
      (StructuralCatchupRightResult.structural-ext child) rb
  → StructuralFrameOutcome
      (StructuralCatchupRightResult.N′ child
        ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
  → (∀ {N₁}
      → ∀ {Δᵒ}
      → {Wᵒ : World Δᴸ
          (StructuralCatchupRightResult.Δᴿ′ child) Δᵒ}
      → (plan : StructuralWorldExtendᴿ
          (StructuralCatchupRightResult.χs child) W Wᵒ)
      → Wᵒ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
          ⊢² M ↓ c ⊑
            (StructuralCatchupRightResult.N′ child
              ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
            ∶ ECR.transport⊑ᵂ
                (structural-world-extendᴿ plan) q
      → (StructuralCatchupRightResult.N′ child
           ↓ applyConceals (StructuralCatchupRightResult.χs child) c′)
          —→[ keep ] N₁
      → Value N₁
      → StructuralCatchupRightResult W γ (M ↓ c) (M′ ↓ c′) q)
  → StructuralCatchupRightResult W γ (M ↓ c) (M′ ↓ c′) q
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-value finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb replay
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-value finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ child
    ; χs = StructuralCatchupRightResult.χs child
    ; Δ′ = StructuralCatchupRightResult.Δ′ child
    ; W′ = W′
    ; structural-ext = plan
    ; N′ = StructuralCatchupRightResult.N′ child
        ↓ applyConceals χs c′
    ; final-value = finalV
    ; post-reduction =
        conceal-↠ c′ (StructuralCatchupRightResult.post-reduction child)
    ; final-relation =
        CTI2.conceal⊑conceal²
          (structural-source-conceal plan c⊢)
          (structural-target-conceal plan c′⊢)
          (trans (structural-source-conceal-position plan c⊢)
            (trans position
              (sym (structural-target-conceal-position plan c′⊢))))
          (λ empty → active
            (trans
              (sym (structural-source-conceal-position plan c⊢)) empty))
          (ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            representation)
          (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-keep step finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb replay
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    c⊢ c′⊢ position active representation mono rb sc child replay
    (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.conceal⊑conceal²
      (structural-source-conceal plan c⊢)
      (structural-target-conceal plan c′⊢)
      (trans (structural-source-conceal-position plan c⊢)
        (trans position
          (sym (structural-target-conceal-position plan c′⊢))))
      (λ empty → active
        (trans (sym (structural-source-conceal-position plan c⊢)) empty))
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        representation)
      (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-compose : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {A : Ty Δᴸ} {B₀ B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B₀} {q : A ⊑ᵂ⟨ W ⟩ B}
  → (result₁ : StructuralCatchupRightResult W γ M M₀ p)
  → StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ result₁)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext result₁))
        γ)
      M
      (StructuralCatchupRightResult.N′ result₁)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext result₁))
        q)
  → StructuralCatchupRightResult W γ M M₀ q
structural-catchup-compose {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {γ = γ}
    {M₀ = M₀} {B = B} {q = q} result₁ result₂ =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ result₂
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ result₂
    ; W′ = StructuralCatchupRightResult.W′ result₂
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ result₂
    ; final-value = StructuralCatchupRightResult.final-value result₂
    ; post-reduction =
        composeReduction
          (StructuralCatchupRightResult.post-reduction result₁)
          (StructuralCatchupRightResult.post-reduction result₂)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ result₂ ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TE.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ B)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation result₂)))
    }
  where
  χs₁ = StructuralCatchupRightResult.χs result₁
  χs₂ = StructuralCatchupRightResult.χs result₂
  plan₁ = StructuralCatchupRightResult.structural-ext result₁
  plan₂ = StructuralCatchupRightResult.structural-ext result₂
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


structural-catchup-compose-target-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {A : Ty Δᴸ} {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B₀} {q : A ⊑ᵂ⟨ W ⟩ B}
  → (c′ : ν ⊢ B₀ ∼ B)
  → (child : StructuralCatchupRightResult W γ M M₀ p)
  → (residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        γ)
      M
      (StructuralCatchupRightResult.N′ child
        ⟨ applyConsistencies
          (StructuralCatchupRightResult.χs child) c′ ⟩)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        q))
  → StructuralCatchupRightResult W γ M (M₀ ⟨ c′ ⟩) q
structural-catchup-compose-target-cast {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {γ = γ} {M₀ = M₀} {B = B} {q = q} c′ child residual =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ residual
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ residual
    ; W′ = StructuralCatchupRightResult.W′ residual
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ residual
    ; final-value = StructuralCatchupRightResult.final-value residual
    ; post-reduction =
        composeReduction
          (cast-↠ c′ (StructuralCatchupRightResult.post-reduction child))
          (StructuralCatchupRightResult.post-reduction residual)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ residual ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TE.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ B)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation residual)))
    }
  where
  χs₁ = StructuralCatchupRightResult.χs child
  χs₂ = StructuralCatchupRightResult.χs residual
  plan₁ = StructuralCatchupRightResult.structural-ext child
  plan₂ = StructuralCatchupRightResult.structural-ext residual
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


structural-catchup-compose-paired-target-cast : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M₀ : Term Δᴿ}
    {C A : Ty Δᴸ} {C′ A′ : Ty Δᴿ}
    {ν : Env∼ Δᴸ} {ν′ : Env∼ Δᴿ}
    {p : C ⊑ᵂ⟨ W ⟩ C′} {q : A ⊑ᵂ⟨ W ⟩ A′}
  → (c : ν ⊢ C ∼ A)
  → (c′ : ν′ ⊢ C′ ∼ A′)
  → (child : StructuralCatchupRightResult W γ M M₀ p)
  → (residual : StructuralCatchupRightResult
      (StructuralCatchupRightResult.W′ child)
      (ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        γ)
      (M ⟨ c ⟩)
      (StructuralCatchupRightResult.N′ child
        ⟨ applyConsistencies
          (StructuralCatchupRightResult.χs child) c′ ⟩)
      (ECR.transport⊑ᵂ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        q))
  → StructuralCatchupRightResult W γ (M ⟨ c ⟩) (M₀ ⟨ c′ ⟩) q
structural-catchup-compose-paired-target-cast {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    {γ = γ} {M₀ = M₀} {A′ = A′} {q = q} c c′ child residual =
  record
    { Δᴿ′ = StructuralCatchupRightResult.Δᴿ′ residual
    ; χs = χs₁ ++χ χs₂
    ; Δ′ = StructuralCatchupRightResult.Δ′ residual
    ; W′ = StructuralCatchupRightResult.W′ residual
    ; structural-ext = composeStructuralWorldExtendᴿ plan₁ plan₂
    ; N′ = StructuralCatchupRightResult.N′ residual
    ; final-value = StructuralCatchupRightResult.final-value residual
    ; post-reduction =
        composeReduction
          (cast-↠ c′ (StructuralCatchupRightResult.post-reduction child))
          (StructuralCatchupRightResult.post-reduction residual)
    ; final-relation =
        subst≡
          (λ γ′ → StructuralCatchupRightResult.W′ residual ∣ γ′ ⊢² _
            ⊑ _ ∶ ECR.transport⊑ᵂ ext q)
          (mapCtxᴿ-structural-compose plan₁ plan₂ γ)
          (TE.⊢²-retarget
            (rel-target-transportᴿ
              (applyTys-++ χs₁ χs₂ A′)
              (ECR.transport⊑ᵂ ext₂
                (ECR.transport⊑ᵂ ext₁ q))
              (StructuralCatchupRightResult.final-relation residual)))
    }
  where
  χs₁ = StructuralCatchupRightResult.χs child
  χs₂ = StructuralCatchupRightResult.χs residual
  plan₁ = StructuralCatchupRightResult.structural-ext child
  plan₂ = StructuralCatchupRightResult.structural-ext residual
  ext₁ = structural-world-extendᴿ plan₁
  ext₂ = structural-world-extendᴿ plan₂
  ext = structural-world-extendᴿ (composeStructuralWorldExtendᴿ plan₁ plan₂)


StructuralValueCatchupRight² : Set₁
StructuralValueCatchupRight² = ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → W ∣ γ ⊢² M ⊑ M″ ∶ q
  → StructuralCatchupRightResult W γ M M″ q


erase-structural-value-catchup-right² :
  StructuralValueCatchupRight² → ValueCatchupRight²
erase-structural-value-catchup-right² worker vM rel =
  erase-structural-catchup-result (worker vM rel)


StructuralExtraCastRightAt : ℕ → Set₁
StructuralExtraCastRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B′}
  → (c′ : ν ⊢ B ∼ B′)
  → castSize c′ < fuel
  → W ∣ γ ⊢² M ⊑ (M′ ⟨ c′ ⟩) ∶ q
  → Value M
  → Value M′
  → StructuralCatchupRightResult W γ M (M′ ⟨ c′ ⟩) q


erase-structural-extra-cast-right-at : ∀ {fuel}
  → StructuralExtraCastRightAt fuel
  → ExtraCastRightAt fuel
erase-structural-extra-cast-right-at worker c′ c′<fuel rel vM vM′ =
  erase-structural-catchup-result (worker c′ c′<fuel rel vM vM′)


StructuralValueCatchupRightAt : ℕ → Set₁
StructuralValueCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M″ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {q : A ⊑ᵂ⟨ W ⟩ B}
  → Value M
  → (rel : W ∣ γ ⊢² M ⊑ M″ ∶ q)
  → TargetCastBound fuel rel
  → StructuralCatchupRightResult W γ M M″ q


erase-structural-value-catchup-right-at : ∀ {fuel}
  → StructuralValueCatchupRightAt fuel
  → ValueCatchupRightAt fuel
erase-structural-value-catchup-right-at worker vM rel bound =
  erase-structural-catchup-result (worker vM rel bound)


StructuralInstCatchupRightAt : ℕ → Set₁
StructuralInstCatchupRightAt fuel = ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Value M
  → Value M′
  → AllValueView M′
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → castSize ((inst c′) B′≢★) < fuel
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → StructuralCatchupRightResult W γ M
      (M′ ⟨ (inst c′) B′≢★ ⟩) q


erase-structural-inst-catchup-right-at : ∀ {fuel}
  → StructuralInstCatchupRightAt fuel
  → InstCatchupRightAt fuel
erase-structural-inst-catchup-right-at worker rel vM vM′ spine c′
    B′≢★ c′<fuel q =
  erase-structural-catchup-result
    (worker rel vM vM′ spine c′ B′≢★ c′<fuel q)
