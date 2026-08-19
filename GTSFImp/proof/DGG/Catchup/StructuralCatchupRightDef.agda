module proof.DGG.Catchup.StructuralCatchupRightDef where

-- File Charter:
--   * Defines the LG-3 internal right-catch-up result package that carries
--     `StructuralWorldExtendᴿ`.
--   * Provides erasure adapters to the public `WorldExtendᴿ` result surfaces
--     used by `ValueCatchupRightAt` and `ExtraCastRightAt`.
--   * Keeps structural traces internal; no public fuel statement is widened.

import Data.Fin as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types using
  (Ty; TyCtx; TyVar; NonVar; _∈ᵗ_; ★; ＇_; `∀; ⇑ᵗ; renameNonVar)
open import Consistency using
  (Env∼; _↪ᵗ_; _⊢_∼_; inst_; instᵐ; wk↪ᵗ; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; seal)
open import Imprecision using (X⊑★)
open import CastTerms using
  (Term; Value; Inert; ⟨_,_,_⟩; _⊢_⦂_; Λ_; _⟨_⟩; _《_》; _↑_;
   _↓_; renameᵗᵐ)
open import Reduction using (StoreChanges; []; _∷_; keep; _—→[_]_;
  _—↠[_]_; _—→[_]⟨_⟩_; _—↠[_]⟨_⟩_; _∎[]; bind;
  applyConsistency; applyConsistencies; applyStores; applyTys; ξ-conceal;
  ↠-step)
open import proof.Reduction using
  (cast-↠; applyConsistencies-Inert; _++χ_; applyTys-++;
   applyTys-★; cast-applyConsistencies-++; composeReduction; reveal-↠;
   conceal-↠; applyReveals; applyConceals)

import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.TargetBindLift as TBL
import proof.DGG.TargetExtend as TE
import proof.DGG.ExtraCastRight2 as ECR
open TE using (align-insert; renameRep★PartnerOK; source-insert;
  target-center-reflect)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open import proof.DGG.Catchup.StructuralWorldExtendDef
open import proof.DGG.Catchup.StructuralWorldExtendProof
  using (StructuralWorldExtendSplit; splitStructuralWorldExtendᴿ;
         structural-world-extendᴿ; composeStructuralWorldExtendᴿ;
         mapCtxᴿ-structural-compose; mapCtxᴿ-structural-keep)
open import proof.DGG.Catchup.StructuralWorldRebaseProof using
  (structural-rebase-atᴸ-pullback; structural-rebase-atᴿ-pullback;
   structural-rebase-at-pullback; structural-reverse-rebase-atᴿ-pullback;
   structural-reverse-rebase-at-pullback)
open import proof.DGG.Catchup.StructuralWorldTagRebaseDef
open import proof.DGG.Catchup.StructuralWorldTagRebaseProof using
  (structural-tag-rebase-atᴸ-pullback)
open import proof.DGG.Catchup.StructuralWorldEvidenceProof using
  (mapCtxᴿ-sameCtx; mapCtxᴿ-liftCtxᴸ; mapCtxᴿ-smartLiftCtxᴸ;
   liftCtxᴸ-target-ctx; smartCommaLift-target-store;
   smartLiftCtxᴸ-target-ctx; structural-source-reveal;
   structural-source-conceal; structural-target-reveal;
   structural-target-conceal)
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
open import proof.TypeInTermSubst using (toRename-wk-eq)
import proof.DGG.CastTermImprecision2Typing as CTI2T
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


mapPivotChanges-just : ∀ {Δ Δ′}
  → (χs : StoreChanges Δ Δ′)
  → (X : TyVar Δ)
  → mapPivotChanges χs (just X) ≡ just (mapVarChanges χs X)
mapPivotChanges-just [] X = refl
mapPivotChanges-just (keep ∷ χs) X =
  mapPivotChanges-just χs X
mapPivotChanges-just (bind A ∷ χs) X =
  mapPivotChanges-just χs (toRenameᵗ wk↪ᵗ X)


mapPivotChanges-nothing : ∀ {Δ Δ′}
  → (χs : StoreChanges Δ Δ′)
  → mapPivotChanges χs nothing ≡ nothing
mapPivotChanges-nothing [] = refl
mapPivotChanges-nothing (keep ∷ χs) =
  mapPivotChanges-nothing χs
mapPivotChanges-nothing (bind A ∷ χs) =
  mapPivotChanges-nothing χs


mapVarChanges-cong : ∀ {Δ Δ′}
  → (χs : StoreChanges Δ Δ′)
  → {X Y : TyVar Δ}
  → X ≡ Y
  → mapVarChanges χs X ≡ mapVarChanges χs Y
mapVarChanges-cong χs refl = refl


applyTys-var : ∀ {Δ Δ′}
  → (χs : StoreChanges Δ Δ′)
  → (X : TyVar Δ)
  → applyTys χs (＇ X) ≡ ＇ mapVarChanges χs X
applyTys-var [] X = refl
applyTys-var (keep ∷ χs) X = applyTys-var χs X
applyTys-var (bind A ∷ χs) X =
  trans (applyTys-var χs (Fin.suc X))
    (cong ＇_
      (mapVarChanges-cong χs (sym (toRename-wk-eq X))))


structural-target-reveal-just : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {A B : Ty Δᴿ}
    {c : Conv↑ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTX.targetStoreʷ W Conv.⊢↑[ just X ] c
  → CTX.targetStoreʷ W′ Conv.⊢↑[ just (mapVarChanges χs X) ]
      applyReveals χs c
structural-target-reveal-just {χs = χs} {W′ = W′} {X = X} {c = c}
    plan c⊢ =
  subst≡
    (λ pivot → CTX.targetStoreʷ W′ Conv.⊢↑[ pivot ]
      applyReveals χs c)
    (mapPivotChanges-just χs X)
    (structural-target-reveal plan c⊢)


structural-target-conceal-just : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ} {A B : Ty Δᴿ}
    {c : Conv↓ Δᴿ A B}
  → StructuralWorldExtendᴿ χs W W′
  → CTX.targetStoreʷ W Conv.⊢↓[ just X ] c
  → CTX.targetStoreʷ W′ Conv.⊢↓[ just (mapVarChanges χs X) ]
      applyConceals χs c
structural-target-conceal-just {χs = χs} {W′ = W′} {X = X} {c = c}
    plan c⊢ =
  subst≡
    (λ pivot → CTX.targetStoreʷ W′ Conv.⊢↓[ pivot ]
      applyConceals χs c)
    (mapPivotChanges-just χs X)
    (structural-target-conceal plan c⊢)


structural-target-seal-star : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : World Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ′ Δ′}
    {X : TyVar Δᴿ}
  → StructuralWorldExtendᴿ χs W W′
  → CTX.targetStoreʷ W Conv.⊢↓[ just X ] seal X ★
  → CTX.targetStoreʷ W′ Conv.⊢↓[ just (mapVarChanges χs X) ]
      seal (mapVarChanges χs X) ★
structural-target-seal-star structural-[] c⊢ = c⊢
structural-target-seal-star (structural-keep plan) c⊢ =
  structural-target-seal-star plan c⊢
structural-target-seal-star {X = X}
    (structural-bind {W₁ = W₁} ins follows plan) (Conv.⊢↓-sealˣ X∈) =
  structural-target-seal-star plan
    (Conv.⊢↓-sealˣ (TE.targetStore-rename ins X∈))


conceal-seal-star-↠ : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′}
    {χs : StoreChanges Δ Δ′}
  → (X : TyVar Δ)
  → M —↠[ χs ] N
  → M ↓ seal X ★ —↠[ χs ] N ↓ seal (mapVarChanges χs X) ★
conceal-seal-star-↠ {M = M} X (_ ∎[]) = M ↓ seal X ★ ∎[]
conceal-seal-star-↠ {M = M} {N = P} {χs = keep ∷ χs} X
    (_ —→[ keep ]⟨ M→N ⟩ N↠P) =
  M ↓ seal X ★
    —→[ keep ]⟨ ξ-conceal M→N refl ⟩
  _
    —↠[ χs ]⟨ conceal-seal-star-↠ X N↠P ⟩
  P ↓ seal (mapVarChanges χs X) ★ ∎[]
conceal-seal-star-↠ {M = M} {N = P} {χs = bind A ∷ χs} X
    (↠-step {N = N} M→N N↠P) =
  M ↓ seal X ★
    —→[ bind A ]⟨ ξ-conceal M→N refl ⟩
  N ↓ seal (Fin.suc X) ★
    —↠[ χs ]⟨
      subst≡
        (λ T → N ↓ seal (Fin.suc X) ★ —↠[ χs ] T)
        (cong (λ Y → P ↓ seal Y ★)
          (mapVarChanges-cong χs (sym (toRename-wk-eq X))))
        (conceal-seal-star-↠ (Fin.suc X) N↠P) ⟩
  P ↓ seal (mapVarChanges χs (toRenameᵗ wk↪ᵗ X)) ★ ∎[]


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
      {γᴸ : CtxImp (CTX.liftWorldLeft X⊑★ W)}
      {U : Term (suc Δᴸ)}
      {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
      {p : A ⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ W ⟩ B}
      {q : `∀ A ⊑ᵂ⟨ W ⟩ B}
    → SourceΛReplayStack W₀ γ₀ M₀ q₀ W γ (Λ U) q
    → NonVar A
    → Fin.zero ∈ᵗ A
    → CTX.LiftCtxᴸ X⊑★ γ γᴸ
    → Value U
    → SourceΛReplayStack W₀ γ₀ M₀ q₀
        (CTX.liftWorldLeft X⊑★ W) γᴸ U p

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
    ; W′ = CTX.liftWorldLeft X⊑★ W′
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


structural-matched-partner-refl : ∀ {Δᴸ Δᴿ Δ₀ Δ₀′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ Δ₀′}
    {M : Term Δᴿ}
  → StructuralWorldExtendᴿ [] W₀ W₀′
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
  → CTX.MatchedConcealPartnerOK W₀ P c Xᴿ? M
  → CTX.MatchedConcealPartnerOK W₀′ P c
      (mapPivotChanges [] Xᴿ?) M
structural-matched-partner-refl structural-[] ok = ok


structural-matched-partner-target-cast-refl :
    ∀ {Δᴸ Δᴿ Δ₀ Δ₀′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ Δ₀′}
    {M : Term Δᴿ}
  → StructuralWorldExtendᴿ [] W₀ W₀′
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (c′ : ν ⊢ B₀ ∼ B)
  → CTX.MatchedConcealPartnerOK W₀ P c₀ Xᴿ? (M ⟨ c′ ⟩)
  → CTX.MatchedConcealPartnerOK W₀′ P c₀
      (mapPivotChanges [] Xᴿ?) (M ⟨ applyConsistencies [] c′ ⟩)
structural-matched-partner-target-cast-refl structural-[] c′ ok = ok


structural-matched-partner-keep-step : ∀ {Δᴸ Δᴿ Δ₀ Δ₀′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ Δ₀′}
    {M N : Term Δᴿ}
  → (∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      → CTX.MatchedConcealPartnerOK W₀ P c Xᴿ? M
      → CTX.MatchedConcealPartnerOK W₀ P c Xᴿ? N)
  → (plan : StructuralWorldExtendᴿ (keep ∷ []) W₀ W₀′)
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
  → CTX.MatchedConcealPartnerOK W₀ P c Xᴿ? M
  → CTX.MatchedConcealPartnerOK
      W₀′ P c (mapPivotChanges (keep ∷ []) Xᴿ?) N
structural-matched-partner-keep-step partner-step
    (structural-keep structural-[]) ok =
  partner-step ok


structural-matched-partner-keep-step-target-cast :
    ∀ {Δᴸ Δᴿ Δ₀ Δ₀′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ Δ₀′}
    {M N : Term Δᴿ}
  → (∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
      → (c′ : ν ⊢ B₀ ∼ B)
      → CTX.MatchedConcealPartnerOK W₀ P c₀ Xᴿ? (M ⟨ c′ ⟩)
      → CTX.MatchedConcealPartnerOK W₀ P c₀ Xᴿ? (N ⟨ c′ ⟩))
  → (plan : StructuralWorldExtendᴿ (keep ∷ []) W₀ W₀′)
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      {B₀ B : Ty Δᴿ} {ν : Env∼ Δᴿ}
  → (c′ : ν ⊢ B₀ ∼ B)
  → CTX.MatchedConcealPartnerOK W₀ P c₀ Xᴿ? (M ⟨ c′ ⟩)
  → CTX.MatchedConcealPartnerOK W₀′ P c₀
      (mapPivotChanges (keep ∷ []) Xᴿ?)
      (N ⟨ applyConsistencies (keep ∷ []) c′ ⟩)
structural-matched-partner-keep-step-target-cast
    partner-step-target-cast (structural-keep structural-[]) c′ ok =
  partner-step-target-cast c′ ok


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


rep★-nested-target-cast-direct : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ?}
    {M N : Term Δᴿ} {A₀ A₁ B₀ B : Ty Δᴿ}
    {ν₀ ν : Env∼ Δᴿ}
  → (d′ : ν₀ ⊢ A₀ ∼ A₁)
  → (c′ : ν ⊢ B₀ ∼ B)
  → CTX.Rep★PartnerOK W X P Xᴿ? ((M ⟨ d′ ⟩) ⟨ c′ ⟩)
  → CTX.Rep★PartnerOK W X P Xᴿ? (N ⟨ c′ ⟩)
rep★-nested-target-cast-direct d′ c′ (CTX.rep★-untagged ())
rep★-nested-target-cast-direct d′ c′
    (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag Gnv
rep★-nested-target-cast-direct d′ c′
    (CTX.rep★-var-tag aligned) =
  CTX.rep★-var-tag aligned
rep★-nested-target-cast-direct d′ c′
    (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  CTX.rep★-matched-inner-tags X₂≢X aligned
rep★-nested-target-cast-direct d′ c′ (CTX.rep★-round-trip ok) =
  CTX.rep★-round-trip
    (rep★-nested-target-cast-direct d′ c′ ok)


bind-align-insert : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {π : Δ ↪ᵗ Δ₁}
    {W₀ : World Δᴸ Δᴿ Δ} {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W₀ W₁
  → CTX.CenterAligned W₀ X Y
  → CTX.CenterAligned W₁ X (Fin.suc Y)
bind-align-insert {W₁ = W₁} {X = X} {Y = Y} ins aligned =
  subst≡ (CTX.CenterAligned W₁ X) (toRename-wk-eq Y)
    (TE.align-insert ins aligned)


rep★-bind-nested-target-cast : ∀ {Δᴸ Δᴿ Δ Δ₁}
    {π : Δ ↪ᵗ Δ₁}
    {W₀ : World Δᴸ Δᴿ Δ} {W₁ : World Δᴸ (suc Δᴿ) Δ₁}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {Xᴿ?}
    {M : Term Δᴿ}
    {A₀ A₁ B₀ B R : Ty Δᴿ} {ν₀ ν : Env∼ Δᴿ}
  → TE.TargetInsert wk↪ᵗ π W₀ W₁
  → (d′ : ν₀ ⊢ A₀ ∼ A₁)
  → (c′ : ν ⊢ B₀ ∼ B)
  → CTX.Rep★PartnerOK W₀ X P Xᴿ? ((M ⟨ d′ ⟩) ⟨ c′ ⟩)
  → CTX.Rep★PartnerOK W₁ X P
      (TE.mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?)
      ((renameᵗᵐ wk↪ᵗ M ⟨ applyConsistency (bind R) d′ ⟩)
        ⟨ applyConsistency (bind R) c′ ⟩)
rep★-bind-nested-target-cast ins d′ c′ (CTX.rep★-untagged ())
rep★-bind-nested-target-cast ins d′ c′
    (CTX.rep★-nonvar-tag Gnv) =
  CTX.rep★-nonvar-tag (renameNonVar Fin.suc Gnv)
rep★-bind-nested-target-cast {W₁ = W₁} {X = X} {P = P}
    {M = M} {R = R} ins d′ c′
    (CTX.rep★-var-tag {Y = Y} aligned) =
  subst≡
    (λ pivot → CTX.Rep★PartnerOK W₁ X P pivot
      ((renameᵗᵐ wk↪ᵗ M ⟨ applyConsistency (bind R) d′ ⟩)
        ⟨ applyConsistency (bind R) c′ ⟩))
    (cong just (sym (toRename-wk-eq Y)))
    (CTX.rep★-var-tag (bind-align-insert ins aligned))
rep★-bind-nested-target-cast ins d′ c′
    (CTX.rep★-matched-inner-tags {Y = Y} X₂≢X aligned) =
  CTX.rep★-matched-inner-tags {Y = toRenameᵗ wk↪ᵗ Y} X₂≢X
    (bind-align-insert ins aligned)
rep★-bind-nested-target-cast {W₀ = W₀} {W₁ = W₁}
    {X = X} {Xᴿ? = Xᴿ?} {M = M}
    {A₀ = A₀} {A₁ = A₁} {B₀ = B₀} {B = B}
    {R = R} {ν₀ = ν₀} {ν = ν} ins d′ c′
    (CTX.rep★-round-trip {P = P₀} ok) =
  CTX.rep★-round-trip
    (rep★-bind-nested-target-cast {W₀ = W₀} {W₁ = W₁}
      {X = X} {P = P₀} {Xᴿ? = Xᴿ?} {M = M}
      {A₀ = A₀} {A₁ = A₁} {B₀ = B₀} {B = B}
      {R = R} {ν₀ = ν₀} {ν = ν} ins d′ c′ ok)


structural-rep★-nested-target-cast : ∀ {Δᴸ Δᴿ Δᴿ′ Δ₀ Δ₀′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ′ Δ₀′}
    {X : TyVar Δᴸ} {P : Term Δᴸ} {Xᴿ?}
    {M : Term Δᴿ} {N : Term Δᴿ′}
    {A₀ A₁ B₀ B : Ty Δᴿ} {ν₀ ν : Env∼ Δᴿ}
  → StructuralWorldExtendᴿ χs W₀ W₀′
  → (d′ : ν₀ ⊢ A₀ ∼ A₁)
  → (c′ : ν ⊢ B₀ ∼ B)
  → CTX.Rep★PartnerOK W₀ X P Xᴿ? ((M ⟨ d′ ⟩) ⟨ c′ ⟩)
  → CTX.Rep★PartnerOK W₀′ X P (mapPivotChanges χs Xᴿ?)
      (N ⟨ applyConsistencies χs c′ ⟩)
structural-rep★-nested-target-cast structural-[] d′ c′ ok =
  rep★-nested-target-cast-direct d′ c′ ok
structural-rep★-nested-target-cast (structural-keep plan) d′ c′ ok =
  structural-rep★-nested-target-cast plan d′ c′ ok
structural-rep★-nested-target-cast
    (structural-bind {B = B} ins follows plan)
    d′ c′ ok =
  structural-rep★-nested-target-cast plan
    (applyConsistency (bind B) d′)
    (applyConsistency (bind B) c′)
    (rep★-bind-nested-target-cast {R = B} ins d′ c′ ok)


structural-matched-partner-nested-target-cast : ∀
    {Δᴸ Δᴿ Δᴿ′ Δ₀ Δ₀′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W₀ : World Δᴸ Δᴿ Δ₀} {W₀′ : World Δᴸ Δᴿ′ Δ₀′}
  → StructuralWorldExtendᴿ χs W₀ W₀′
  → ∀ {P : Term Δᴸ} {A₀ A₁ : Ty Δᴸ}
      {c₀ : Conv↓ Δᴸ A₀ A₁} {Xᴿ?}
      {M : Term Δᴿ} {N : Term Δᴿ′}
      {B₀ B C₀ C : Ty Δᴿ} {ν₀ ν : Env∼ Δᴿ}
  → (d′ : ν₀ ⊢ B₀ ∼ B)
  → (c′ : ν ⊢ C₀ ∼ C)
  → CTX.MatchedConcealPartnerOK W₀ P c₀ Xᴿ?
      ((M ⟨ d′ ⟩) ⟨ c′ ⟩)
  → CTX.MatchedConcealPartnerOK W₀′ P c₀
      (mapPivotChanges χs Xᴿ?) (N ⟨ applyConsistencies χs c′ ⟩)
structural-matched-partner-nested-target-cast plan d′ c′
    (CTX.matched-seal-star-partner ok) =
  CTX.matched-seal-star-partner
    (structural-rep★-nested-target-cast plan d′ c′ ok)
structural-matched-partner-nested-target-cast plan d′ c′
    (CTX.matched-seal-nonstar Rns) =
  CTX.matched-seal-nonstar Rns
structural-matched-partner-nested-target-cast plan d′ c′
    CTX.matched-fun-conceal-target =
  CTX.matched-fun-conceal-target
structural-matched-partner-nested-target-cast plan d′ c′
    CTX.matched-all-conceal-target =
  CTX.matched-all-conceal-target
structural-matched-partner-nested-target-cast plan d′ c′
    CTX.matched-id-conceal-target =
  CTX.matched-id-conceal-target


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


structural-catchup-source-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {c : Conv↑ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAtᴸ W Wᵖ Xᴸ?)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↑[ Xᴸ? ] c
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → StructuralCatchupRightResult W γ (M ↑ c) M′ q
structural-catchup-source-reveal {γ = γ} {q = q}
    mono rb sc c⊢ child
    with structural-rebase-atᴸ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-source-reveal {γ = γ} {q = q}
    mono rb sc c⊢ child
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
        CTI2.reveal⊑² (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-reveal plan c⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }


structural-catchup-source-conceal-seal-star-open : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {B : Ty Δᴿ} {X : TyVar Δᴸ}
    {p : ★ ⊑ᵂ⟨ Wᵖ ⟩ B} {q : (＇ X) ⊑ᵂ⟨ W ⟩ B}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W (just X) nothing)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X ★
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → CTX.NoTargetOccupantAtSource
      (StructuralCatchupRightResult.W′ child) X
  → StructuralCatchupRightResult W γ (M ↓ seal X ★) M′ q
structural-catchup-source-conceal-seal-star-open
    {γ = γ} {X = X} {q = q} mono rb sc c⊢ child no-target
    with structural-tag-rebase-atᴸ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-source-conceal-seal-star-open
    {γ = γ} {X = X} {q = q} mono rb sc c⊢ child no-target
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
        CTI2.conceal⊑²-seal-star-open
          no-target
          (mono′ mono)
          (subst≡
            (λ Xᴿ? → CTX.TagRebaseAtᴸ
              (StructuralCatchupRightResult.W′ child) W′ (just X) Xᴿ?)
            (mapPivotChanges-nothing
              (StructuralCatchupRightResult.χs child))
            rb′)
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-conceal plan c⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }


structural-catchup-source-conceal-source-ok : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {c : Conv↓ Δᴸ A A′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → CTX.SourceConcealOK
      (StructuralCatchupRightResult.W′ child) M c
      (mapPivotChanges (StructuralCatchupRightResult.χs child) Xᴿ?)
      (StructuralCatchupRightResult.N′ child)
  → StructuralCatchupRightResult W γ (M ↓ c) M′ q
structural-catchup-source-conceal-source-ok {γ = γ} {q = q}
    mono rb sc c⊢ child endpoint-ok
    with structural-tag-rebase-atᴸ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-source-conceal-source-ok {γ = γ} {q = q}
    mono rb sc c⊢ child endpoint-ok
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
        CTI2.conceal⊑²-source-ok
          endpoint-ok
          (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-conceal plan c⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }


structural-catchup-target-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {c′ : Conv↑ Δᴿ B B′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAtᴿ W Wᵖ Xᴿ?)
  → CTX.SameCtx γ γᵖ
  → CTX.targetStoreʷ W Conv.⊢↑[ Xᴿ? ] c′
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
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
structural-catchup-target-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-value finalV) keep-cont
    with structural-rebase-atᴿ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-target-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-value finalV) keep-cont
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
        CTI2.⊑reveal² (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-target-reveal plan c′⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-target-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-keep step finalV) keep-cont
    with structural-rebase-atᴿ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-target-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.⊑reveal² (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (structural-target-reveal plan c′⊢)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-target-conceal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
    {Xᴿ? : Maybe (TyVar Δᴿ)} {c′ : Conv↓ Δᴿ B B′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAtᴿ Wᵖ W Xᴿ?)
  → CTX.SameCtx γ γᵖ
  → CTX.targetStoreʷ W Conv.⊢↓[ Xᴿ? ] c′
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
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
structural-catchup-target-conceal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-value finalV) keep-cont
    with structural-reverse-rebase-atᴿ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-target-conceal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-value finalV) keep-cont
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
        CTI2.⊑conceal² (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-target-conceal plan c′⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-target-conceal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-keep step finalV) keep-cont
    with structural-reverse-rebase-atᴿ-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-target-conceal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c′⊢ child (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.⊑conceal² (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (structural-target-conceal plan c′⊢)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-paired-reveal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ B B′ : Ty Δᴸ} {C C′ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c : Conv↑ Δᴸ A B} {c′ : Conv↑ Δᴿ C C′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ C} {q : B ⊑ᵂ⟨ W ⟩ C′}
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt W Wᵖ Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↑[ just Xᴸ ] c
  → CTX.targetStoreʷ W Conv.⊢↑[ just Xᴿ ] c′
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
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
    mono rb sc c⊢ c′⊢ child (structural-frame-value finalV) keep-cont
    with structural-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c⊢ c′⊢ child (structural-frame-value finalV) keep-cont
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
        CTI2.reveal⊑reveal² (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-reveal plan c⊢)
          (structural-target-reveal-just plan c′⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c⊢ c′⊢ child (structural-frame-keep step finalV) keep-cont
    with structural-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-paired-reveal {γ = γ} {c′ = c′} {q = q}
    mono rb sc c⊢ c′⊢ child (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.reveal⊑reveal² (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (structural-source-reveal plan c⊢)
      (structural-target-reveal-just plan c′⊢)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-paired-conceal : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ B B′ : Ty Δᴸ} {C C′ : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ C C′}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ C} {q : B ⊑ᵂ⟨ W ⟩ C′}
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p)
  → CTX.MatchedConcealPartnerOK
      (StructuralCatchupRightResult.W′ child) M c
      (just (mapVarChanges (StructuralCatchupRightResult.χs child) Xᴿ))
      (StructuralCatchupRightResult.N′ child)
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just Xᴸ ] c
  → CTX.targetStoreʷ W Conv.⊢↓[ just Xᴿ ] c′
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
    child endpoint-partner mono rb sc c⊢ c′⊢
    (structural-frame-value finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    child endpoint-partner mono rb sc c⊢ c′⊢
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
        CTI2.conceal⊑conceal² endpoint-partner (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-conceal plan c⊢)
          (structural-target-conceal-just plan c′⊢)
          (StructuralCatchupRightResult.final-relation child)
          (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
    }
  where
  χs = StructuralCatchupRightResult.χs child
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    child endpoint-partner mono rb sc c⊢ c′⊢
    (structural-frame-keep step finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-paired-conceal {γ = γ} {c′ = c′} {q = q}
    child endpoint-partner mono rb sc c⊢ c′⊢
    (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  frame-rel =
    CTI2.conceal⊑conceal² endpoint-partner (mono′ mono) rb′
      (mapCtxᴿ-sameCtx
        (structural-world-extendᴿ plan)
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        sc)
      (structural-source-conceal plan c⊢)
      (structural-target-conceal-just plan c′⊢)
      (StructuralCatchupRightResult.final-relation child)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)


structural-catchup-packaged-seal-star : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p★ : ★ ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {qᵖ : (＇ Xᴸ) ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Xᴿ)}
  → (child : StructuralCatchupRightResult Wᵖ γᵖ M M′ p★)
  → CTX.MatchedConcealPartnerOK
      (StructuralCatchupRightResult.W′ child) M (seal Xᴸ ★)
      (mapPivotChanges (StructuralCatchupRightResult.χs child) Xᴿ?)
      (StructuralCatchupRightResult.N′ child)
  → StructuralCatchupRightResult.W′ child ∣
      ECR.mapCtxᴿ
        (structural-world-extendᴿ
          (StructuralCatchupRightResult.structural-ext child))
        γᵖ
      ⊢² M ↓ seal Xᴸ ★
        ⊑ StructuralCatchupRightResult.N′ child ∶
          ECR.transport⊑ᵂ
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            qᵖ
  → CTX.ImpEnvMono W Wᵖ
  → (rb : CTX.RebaseAt Wᵖ W Xᴸ Xᴿ)
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just Xᴸ ] seal Xᴸ ★
  → CTX.targetStoreʷ W Conv.⊢↓[ just Xᴿ ] seal Xᴿ ★
  → StructuralFrameOutcome
      (StructuralCatchupRightResult.N′ child
        ↓ seal
            (mapVarChanges (StructuralCatchupRightResult.χs child) Xᴿ) ★)
  → (∀ {N₁}
      → ∀ {Δᵒ}
      → {Wᵒ : World Δᴸ
          (StructuralCatchupRightResult.Δᴿ′ child) Δᵒ}
      → (plan : StructuralWorldExtendᴿ
          (StructuralCatchupRightResult.χs child) W Wᵒ)
      → Wᵒ ∣ ECR.mapCtxᴿ (structural-world-extendᴿ plan) γ
          ⊢² M ↓ seal Xᴸ ★ ⊑
            (StructuralCatchupRightResult.N′ child
              ↓ seal
                  (mapVarChanges
                    (StructuralCatchupRightResult.χs child) Xᴿ)
                  ★)
            ∶ ECR.transport⊑ᵂ
                (structural-world-extendᴿ plan) q
      → (StructuralCatchupRightResult.N′ child
           ↓ seal
               (mapVarChanges (StructuralCatchupRightResult.χs child) Xᴿ)
               ★)
          —→[ keep ] N₁
      → Value N₁
      → StructuralCatchupRightResult W γ (M ↓ seal Xᴸ ★)
          (M′ ↓ seal Xᴿ ★) q)
  → StructuralCatchupRightResult W γ (M ↓ seal Xᴸ ★)
      (M′ ↓ seal Xᴿ ★) q
structural-catchup-packaged-seal-star
    {γ = γ} {γᵖ = γᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    {p★ = p★} {qᵖ = qᵖ} {q = q} child endpoint-partner
    endpoint-source-rel mono rb sc c⊢ c′⊢
    (structural-frame-value finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-packaged-seal-star
    {γ = γ} {γᵖ = γᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    {p★ = p★} {qᵖ = qᵖ} {q = q} child endpoint-partner
    endpoint-source-rel mono rb sc c⊢ c′⊢
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
        ↓ seal (mapVarChanges χs Xᴿ) ★
    ; final-value = finalV
    ; post-reduction =
        conceal-seal-star-↠ Xᴿ
          (StructuralCatchupRightResult.post-reduction child)
    ; final-relation =
        TBL.⊢²-retarget
          {q = ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q}
          (rel-target-transportᴿ
            (sym (applyTys-var χs Xᴿ))
            q-packaged
            (CTI2.packaged-seal-star²
              {p★ = p★-packaged} {qᵖ = qᵖ-packaged}
              endpoint-partner (mono′ mono) rb′
              (mapCtxᴿ-sameCtx
                (structural-world-extendᴿ plan)
                (structural-world-extendᴿ
                  (StructuralCatchupRightResult.structural-ext child))
                sc)
              (structural-source-conceal plan c⊢)
              (structural-target-seal-star plan c′⊢)
              (TBL.⊢²-retarget {q = p★-packaged}
                (rel-target-transportᴿ
                  (applyTys-★ χs)
                  (ECR.transport⊑ᵂ child-ext p★)
                  (StructuralCatchupRightResult.final-relation child)))
              (TBL.⊢²-retarget {q = qᵖ-packaged}
                (rel-target-transportᴿ
                  (applyTys-★ χs)
                  (ECR.transport⊑ᵂ child-ext qᵖ)
                  endpoint-source-rel))
              q-packaged))
    }
  where
  χs = StructuralCatchupRightResult.χs child
  child-ext =
    structural-world-extendᴿ
      (StructuralCatchupRightResult.structural-ext child)
  p★-packaged : ★ ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ ★
  p★-packaged =
    subst≡
      (λ B → ★ ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ B)
      (applyTys-★ χs)
      (ECR.transport⊑ᵂ child-ext p★)
  qᵖ-packaged :
    (＇ Xᴸ) ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ ★
  qᵖ-packaged =
    subst≡
      (λ B → (＇ Xᴸ) ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ B)
      (applyTys-★ χs)
      (ECR.transport⊑ᵂ child-ext qᵖ)
  q-packaged :
    (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ (＇ mapVarChanges χs Xᴿ)
  q-packaged =
    subst≡
      (λ B → (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ B)
      (applyTys-var χs Xᴿ)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
structural-catchup-packaged-seal-star
    {γ = γ} {γᵖ = γᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    {p★ = p★} {qᵖ = qᵖ} {q = q} child endpoint-partner
    endpoint-source-rel mono rb sc c⊢ c′⊢
    (structural-frame-keep step finalV) keep-cont
    with structural-reverse-rebase-at-pullback
      (StructuralCatchupRightResult.structural-ext child) rb
structural-catchup-packaged-seal-star
    {γ = γ} {γᵖ = γᵖ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    {p★ = p★} {qᵖ = qᵖ} {q = q} child endpoint-partner
    endpoint-source-rel mono rb sc c⊢ c′⊢
    (structural-frame-keep step finalV) keep-cont
    | record { W′ = W′ ; outer-plan = plan
             ; post-rebase = rb′ ; post-mono = mono′ } =
  keep-cont plan frame-rel step finalV
  where
  χs = StructuralCatchupRightResult.χs child
  child-ext =
    structural-world-extendᴿ
      (StructuralCatchupRightResult.structural-ext child)
  p★-packaged : ★ ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ ★
  p★-packaged =
    subst≡
      (λ B → ★ ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ B)
      (applyTys-★ χs)
      (ECR.transport⊑ᵂ child-ext p★)
  qᵖ-packaged :
    (＇ Xᴸ) ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ ★
  qᵖ-packaged =
    subst≡
      (λ B → (＇ Xᴸ) ⊑ᵂ⟨ StructuralCatchupRightResult.W′ child ⟩ B)
      (applyTys-★ χs)
      (ECR.transport⊑ᵂ child-ext qᵖ)
  q-packaged :
    (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ (＇ mapVarChanges χs Xᴿ)
  q-packaged =
    subst≡
      (λ B → (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ B)
      (applyTys-var χs Xᴿ)
      (ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q)
  frame-rel =
    TBL.⊢²-retarget
      {q = ECR.transport⊑ᵂ (structural-world-extendᴿ plan) q}
      (rel-target-transportᴿ
        (sym (applyTys-var χs Xᴿ))
        q-packaged
        (CTI2.packaged-seal-star²
          {p★ = p★-packaged} {qᵖ = qᵖ-packaged}
          endpoint-partner (mono′ mono) rb′
          (mapCtxᴿ-sameCtx
            (structural-world-extendᴿ plan)
            (structural-world-extendᴿ
              (StructuralCatchupRightResult.structural-ext child))
            sc)
          (structural-source-conceal plan c⊢)
          (structural-target-seal-star plan c′⊢)
          (TBL.⊢²-retarget {q = p★-packaged}
            (rel-target-transportᴿ
              (applyTys-★ χs)
              (ECR.transport⊑ᵂ child-ext p★)
              (StructuralCatchupRightResult.final-relation child)))
          (TBL.⊢²-retarget {q = qᵖ-packaged}
            (rel-target-transportᴿ
              (applyTys-★ χs)
              (ECR.transport⊑ᵂ child-ext qᵖ)
              endpoint-source-rel))
          q-packaged))


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
          (TBL.⊢²-retarget
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
          (TBL.⊢²-retarget
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
          (TBL.⊢²-retarget
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
