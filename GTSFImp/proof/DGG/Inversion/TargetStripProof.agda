module proof.DGG.Inversion.TargetStripProof where

-- File Charter:
--   * Provides the sliced target-tag-at-star strip members used by source
--     stripping.
--   * Keeps any remaining proof debt aligned with the validated target-seal
--     and target-tag slice surfaces.
--   * Derives the old compound strip inhabitants from those slices.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-empty; store-lift; store-bind; lookupStore; _∋_⦂_;
   Z∋; S-lift∋; S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using
  (Term; Value; Inert; inj; fun; all; genᵥ;
   Λ_; _⦂∀_[_]; _↓_; _⟨_⟩; _⊢_⦂_; ⟨_,_,_⟩; seal)
open import Imprecision
open import proof.ImprecisionConsistency using
  (fin-suc-injective; imp-env-weaken; rename-⊑; unshift-⊑)
open import proof.TypeInTermSubst using (rename-occurs; toRename-keep-eq)
import Conversion as Conv
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealTransferCore as STC
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   TargetSealTerminusData; target-seal-terminus-data;
   target-seal-terminus-paired;
   TargetSealTerminusᴸData; target-seal-terminusᴸ-data;
   target-seal-terminusᴸ-paired;
   TargetStripAt★Data; target-strip★-data;
   target-strip★-paired;
   TargetStripAt★ᴸData; target-strip★ᴸ-data;
   target-strip★ᴸ-paired;
   TagDispatchAt★Case; TagDispatchAt★ᴸCase;
   dispatch-tag; dispatch-source-fold; dispatch-nonvar-empty;
   dispatch-tagᴸ; dispatch-source-foldᴸ; dispatch-nonvar-emptyᴸ;
   tag-node★; tag-node★ᴸ;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-Λ; sv-cast; sv-seal; sv-reveal-fun;
   sv-conceal-fun; sv-reveal-all; sv-conceal-all;
   var-value-view; varv-seal)
open import proof.DGG.Inversion.TargetDescentLemma using
  (composeSamePivotRebase; inner-source-pivot-eqᴿ)
open import proof.DGG.Inversion.TargetWalkSupport using
  (impEnvMono-∘; liftWorldLeft-⊑ᵂ; lowerWorldLeft-shift-⊑ᵂ;
   renameᵗ-skip-eq;
   rebase-source-membership; rebase-target-membership; sameCtx-∘;
   seal-target-nonstar-⊥; star-source-nonstar-⊥; store-lookup-unique;
   tagged-target-nonvar-nonstar-spine-⊥; target-seal-rebase-source)

open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   impEnvʷ;
   ηᴸʷ;
   ηᴿʷ;
   sourceStoreʷ;
   targetStoreʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)

private
  sameCtx-refl : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    → CTX.SameCtx γ γ
  sameCtx-refl {γ = []} = CTX.same-[]
  sameCtx-refl {γ = CTX.ctx-imp A B p ∷ γ} =
    CTX.same-∷ sameCtx-refl

  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Z : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Z ⦂ S
    → targetStoreʷ W′ ∋ Z ⦂ S
  rebase-target-membership-forward rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb)) Z∈

  rebase-target-membership-back : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Z : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W′ ∋ Z ⦂ S
    → targetStoreʷ W ∋ Z ⦂ S
  rebase-target-membership-back rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (sym (CTX.SameRuntime.targetStore-same
        (CTX.RebaseAt.sameRuntime rb))) Z∈

  origin-var-obligation : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt Wʳ Wᵒ Xᴸ Y
    → (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y
  origin-var-obligation {Wᵒ = Wᵒ} {Xᴸ = Xᴸ} {Y = Y} rb =
    subst≡
      (λ Z → impEnvʷ Wᵒ ⊢
        ＇ (toRenameᵗ (ηᴸʷ Wᵒ) Xᴸ) ⊑ ＇ Z)
      (CTX.RebaseAt.pivotAligned rb)
      X⊑X

  composeOuterRebase : ∀ {Δᴸ Δᴿ Δ}
      {W W′ W₂ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    → RebaseAt W′ W X Y
    → RebaseAt W₂ W′ X Y′
    → RebaseAt W₂ W X Y
  composeOuterRebase {W = W} {W′ = W′} {W₂ = W₂}
      {X = X} {Y = Y} rb₁ rb₂ =
    CTX.rebase-at
      (CTX.same-runtime
        (trans (CTX.SameRuntime.sourceStore-same
          (CTX.RebaseAt.sameRuntime rb₁))
          (CTX.SameRuntime.sourceStore-same
            (CTX.RebaseAt.sameRuntime rb₂)))
        (trans (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb₁))
          (CTX.SameRuntime.targetStore-same
            (CTX.RebaseAt.sameRuntime rb₂))))
      source-off target-frozen (CTX.RebaseAt.pivotAligned rb₁)
      (CTX.RebaseAt.storeRepresentations rb₁)
    where
    source-off : ∀ {Z} → Z ≢ X
      → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
    source-off Z≢X =
      trans (CTX.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
        (CTX.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

    target-frozen : ∀ Z
      → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
    target-frozen Z =
      trans (CTX.RebaseAt.ηᴿ-frozen rb₁ Z)
        (CTX.RebaseAt.ηᴿ-frozen rb₂ Z)

  liftWorldLeft-shift-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → ⇑ᵗ A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ B
  liftWorldLeft-shift-⊑ᵂ {W = W} {A = A} {B = B} p =
    liftWorldLeft-⊑ᵂ {W = W} {A = ⇑ᵗ A} {B = B}
      (subst≡
        (λ L → instᵐ (impEnvʷ W) ⊢ L ⊑ ⇑ᵗ (CTX.embedᴿ W B))
        (sym (renameᵗ-shift (toRenameᵗ (ηᴸʷ W)) A))
        (rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) p))

  liftCtxᴸ-canonical : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
    → (γ : CtxImp W)
    → Σ[ γᴸ ∈ CtxImp (CTX.liftWorldLeft W) ]
        CTX.LiftCtxᴸ X⊑★ γ γᴸ
  liftCtxᴸ-canonical {W = W} [] = [] , CTX.liftᴸ-[]
  liftCtxᴸ-canonical {W = W} (CTX.ctx-imp A B p ∷ γ)
      with liftCtxᴸ-canonical γ
  liftCtxᴸ-canonical {W = W} (CTX.ctx-imp A B p ∷ γ)
      | γᴸ , liftγ =
    CTX.ctx-imp (⇑ᵗ A) B
      (liftWorldLeft-shift-⊑ᵂ {W = W} {A = A} {B = B} p) ∷ γᴸ ,
    CTX.liftᴸ-∷ liftγ

  sameCtx-liftᴸ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W₂ : World Δᴸ Δᴿ Δ}
      {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂}
      {γ₁ᴸ : CtxImp (CTX.liftWorldLeft W₁)}
      {γ₂ᴸ : CtxImp (CTX.liftWorldLeft W₂)}
    → CTX.SameCtx γ₁ γ₂
    → CTX.LiftCtxᴸ X⊑★ γ₁ γ₁ᴸ
    → CTX.LiftCtxᴸ X⊑★ γ₂ γ₂ᴸ
    → CTX.SameCtx γ₁ᴸ γ₂ᴸ
  sameCtx-liftᴸ CTX.same-[] CTX.liftᴸ-[] CTX.liftᴸ-[] =
    CTX.same-[]
  sameCtx-liftᴸ (CTX.same-∷ sc) (CTX.liftᴸ-∷ lift₁)
      (CTX.liftᴸ-∷ lift₂) =
    CTX.same-∷ (sameCtx-liftᴸ sc lift₁ lift₂)

  nonvar-var-⊥ : ∀ {Δ} {X : TyVar Δ}
    → NonVar (＇ X)
    → ⊥
  nonvar-var-⊥ ()

  liftImpEnvMonoLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
    → CTX.ImpEnvMono W W′
    → CTX.ImpEnvMono
        (CTX.liftWorldLeft W)
        (CTX.liftWorldLeft W′)
  liftImpEnvMonoLeft {W = W} {W′ = W′} mono =
    CTX.imp-env-mono dynamic precise
    where
    dynamic : ∀ Z
      → impEnvʷ (CTX.liftWorldLeft W) Z ≡ X⊑★
      → impEnvʷ (CTX.liftWorldLeft W′) Z ≡ X⊑★
    dynamic Fin.zero mark = mark
    dynamic (Fin.suc Z) mark =
      CTX.dynamic-preserved mono Z mark

    precise : ∀ Z
      → impEnvʷ (CTX.liftWorldLeft W) Z ≡ X⊑X
      → impEnvʷ (CTX.liftWorldLeft W′) Z ≡ X⊑X
    precise Fin.zero ()
    precise (Fin.suc Z) mark =
      CTX.precise-preserved mono Z mark

  liftRebaseAtLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt W W′ Xᴸ Y
    → RebaseAt
        (CTX.liftWorldLeft W)
        (CTX.liftWorldLeft W′)
        (Fin.suc Xᴸ) Y
  liftRebaseAtLeft {W = W} {W′ = W′} {Xᴸ = Xᴸ} {Y = Y} rb =
    CTX.rebase-at
      (CTX.same-runtime
        (cong store-lift
          (CTX.SameRuntime.sourceStore-same
            (CTX.RebaseAt.sameRuntime rb)))
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime rb)))
      source-off target-frozen
      (cong Fin.suc (CTX.RebaseAt.pivotAligned rb))
      (CTX.store-rep-imp
        (liftWorldLeft-shift-⊑ᵂ {W = W′}
          {A = CTX.resolveVar (sourceStoreʷ W′) Xᴸ}
          {B = CTX.resolveVar (targetStoreʷ W′) Y}
          (CTX.StoreRepImp.represented
            (CTX.RebaseAt.storeRepresentations rb))))
    where
    source-off : ∀ {Z}
      → Z ≢ Fin.suc Xᴸ
      → toRenameᵗ (ηᴸʷ (CTX.liftWorldLeft W′)) Z
          ≡ toRenameᵗ (ηᴸʷ (CTX.liftWorldLeft W)) Z
    source-off {Fin.zero} Z≢ = refl
    source-off {Fin.suc Z} Z≢ =
      cong Fin.suc
        (CTX.RebaseAt.ηᴸ-off-pivot rb
          (λ eq → Z≢ (cong Fin.suc eq)))

    target-frozen : ∀ Z
      → toRenameᵗ (ηᴿʷ (CTX.liftWorldLeft W′)) Z
          ≡ toRenameᵗ (ηᴿʷ (CTX.liftWorldLeft W)) Z
    target-frozen Z =
      cong Fin.suc (CTX.RebaseAt.ηᴿ-frozen rb Z)

  fin-suc-not-zero : ∀ {n} {X : TyVar n}
    → Fin.suc X ≢ Fin.zero
  fin-suc-not-zero ()

  dropKeep : ∀ {Δ Δ′}
    → (η : suc Δ ↪ᵗ suc Δ′)
    → toRenameᵗ η Fin.zero ≡ Fin.zero
    → Δ ↪ᵗ Δ′
  dropKeep (keep η) refl = η
  dropKeep (skip η) ()

  dropKeep-eq : ∀ {Δ Δ′}
      (η : suc Δ ↪ᵗ suc Δ′)
      (zero-fixed : toRenameᵗ η Fin.zero ≡ Fin.zero)
    → keep (dropKeep η zero-fixed) ≡ η
  dropKeep-eq (keep η) refl = refl
  dropKeep-eq (skip η) ()

  dropSkip : ∀ {Δᴿ Δ}
    → (η : Δᴿ ↪ᵗ suc Δ)
    → TyVar Δᴿ
    → (∀ Y → toRenameᵗ η Y ≢ Fin.zero)
    → Δᴿ ↪ᵗ Δ
  dropSkip empty ()
  dropSkip (keep η) Y nonzero =
    ⊥-elim (nonzero Fin.zero refl)
  dropSkip (skip η) Y nonzero = η

  dropSkip-eq : ∀ {Δᴿ Δ}
      (η : Δᴿ ↪ᵗ suc Δ)
      (Y : TyVar Δᴿ)
      (nonzero : ∀ Z → toRenameᵗ η Z ≢ Fin.zero)
    → skip (dropSkip η Y nonzero) ≡ η
  dropSkip-eq empty ()
  dropSkip-eq (keep η) Y nonzero =
    ⊥-elim (nonzero Fin.zero refl)
  dropSkip-eq (skip η) Y nonzero = refl

  lift-source-zero-fixed : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt Wᴸ (CTX.liftWorldLeft W₁) (Fin.suc X) Y
    → toRenameᵗ (ηᴸʷ Wᴸ) Fin.zero ≡ Fin.zero
  lift-source-zero-fixed link =
    sym (CTX.RebaseAt.ηᴸ-off-pivot link (λ ()))

  lift-target-nonzero : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt Wᴸ (CTX.liftWorldLeft W₁) (Fin.suc X) Y
    → ∀ Z → toRenameᵗ (ηᴿʷ Wᴸ) Z ≢ Fin.zero
  lift-target-nonzero {W₁ = W₁} link Z eq =
    fin-suc-not-zero
      (trans (CTX.RebaseAt.ηᴿ-frozen link Z) eq)

  lowerLiftWorldLeft-invariants : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → (link : RebaseAt Wᴸ (CTX.liftWorldLeft W₁) (Fin.suc X) Y)
    → CTX.WorldInvariants
        (dropKeep (ηᴸʷ Wᴸ) (lift-source-zero-fixed link))
        (dropSkip (ηᴿʷ Wᴸ) Y (lift-target-nonzero link))
        (λ Z → impEnvʷ Wᴸ (Fin.suc Z))
        (sourceStoreʷ W₁) (targetStoreʷ Wᴸ)
  lowerLiftWorldLeft-invariants {W₁ = W₁} {Wᴸ = Wᴸ} {Y = Y} link =
    CTX.world-invariants precise represented unmatched unoccupied
    where
    ηᴸ↓ = dropKeep (ηᴸʷ Wᴸ) (lift-source-zero-fixed link)
    ηᴿ↓ = dropSkip (ηᴿʷ Wᴸ) Y (lift-target-nonzero link)

    keep-eq : keep ηᴸ↓ ≡ ηᴸʷ Wᴸ
    keep-eq = dropKeep-eq (ηᴸʷ Wᴸ) (lift-source-zero-fixed link)

    skip-eq : skip ηᴿ↓ ≡ ηᴿʷ Wᴸ
    skip-eq = dropSkip-eq (ηᴿʷ Wᴸ) Y (lift-target-nonzero link)

    source-stores : store-lift (sourceStoreʷ W₁) ≡ sourceStoreʷ Wᴸ
    source-stores = CTX.SameRuntime.sourceStore-same
      (CTX.RebaseAt.sameRuntime link)

    source-image : ∀ Xᴸ
      → Fin.suc (toRenameᵗ ηᴸ↓ Xᴸ)
        ≡ toRenameᵗ (ηᴸʷ Wᴸ) (Fin.suc Xᴸ)
    source-image Xᴸ =
      cong (λ η → toRenameᵗ η (Fin.suc Xᴸ)) keep-eq

    target-image : ∀ Xᴿ
      → Fin.suc (toRenameᵗ ηᴿ↓ Xᴿ) ≡ toRenameᵗ (ηᴿʷ Wᴸ) Xᴿ
    target-image Xᴿ = cong (λ η → toRenameᵗ η Xᴿ) skip-eq

    precise : ∀ Xᴸ
      → impEnvʷ Wᴸ (Fin.suc (toRenameᵗ ηᴸ↓ Xᴸ)) ≡ X⊑X
      → Σ[ Xᴿ ∈ TyVar _ ] toRenameᵗ ηᴿ↓ Xᴿ ≡ toRenameᵗ ηᴸ↓ Xᴸ
    precise Xᴸ mark
        with CTX.preciseMarksAligned (CTX.invariantsʷ Wᴸ) (Fin.suc Xᴸ)
          (subst≡ (λ Z → impEnvʷ Wᴸ Z ≡ X⊑X)
            (source-image Xᴸ) mark)
    precise Xᴸ mark | Xᴿ , aligned =
      Xᴿ , fin-suc-injective
        (trans (target-image Xᴿ)
          (trans aligned (sym (source-image Xᴸ))))

    lower-env : ∀ Z
      → impEnvʷ Wᴸ Z ≡ X⊑★
      → instᵐ (λ Q → impEnvʷ Wᴸ (Fin.suc Q)) Z ≡ X⊑★
    lower-env Fin.zero mark = refl
    lower-env (Fin.suc Z) mark = mark

    source-representation-shift : ∀ Xᴸ
      → renameᵗ (toRenameᵗ (ηᴸʷ Wᴸ))
          (lookupStore (sourceStoreʷ Wᴸ) (Fin.suc Xᴸ))
        ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ηᴸ↓)
          (lookupStore (sourceStoreʷ W₁) Xᴸ))
    source-representation-shift Xᴸ =
      trans
        (cong (renameᵗ (toRenameᵗ (ηᴸʷ Wᴸ)))
          (sym (cong (λ Σ → lookupStore Σ (Fin.suc Xᴸ)) source-stores)))
        (trans
          (cong (λ η → renameᵗ (toRenameᵗ η)
              (⇑ᵗ (lookupStore (sourceStoreʷ W₁) Xᴸ)))
            (sym keep-eq))
          (trans
            (renameᵗ-cong
              (⇑ᵗ (lookupStore (sourceStoreʷ W₁) Xᴸ))
              (toRename-keep-eq ηᴸ↓))
            (renameᵗ-shift (toRenameᵗ ηᴸ↓)
              (lookupStore (sourceStoreʷ W₁) Xᴸ))))

    target-representation-shift : ∀ Xᴿ
      → renameᵗ (toRenameᵗ (ηᴿʷ Wᴸ))
          (lookupStore (targetStoreʷ Wᴸ) Xᴿ)
        ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ηᴿ↓)
          (lookupStore (targetStoreʷ Wᴸ) Xᴿ))
    target-representation-shift Xᴿ =
      trans
        (cong (λ η → renameᵗ (toRenameᵗ η)
            (lookupStore (targetStoreʷ Wᴸ) Xᴿ))
          (sym skip-eq))
        (renameᵗ-skip-eq ηᴿ↓ (lookupStore (targetStoreʷ Wᴸ) Xᴿ))

    represented : ∀ {Xᴸ : TyVar _} {Xᴿ : TyVar _}
      → toRenameᵗ ηᴸ↓ Xᴸ ≡ toRenameᵗ ηᴿ↓ Xᴿ
      → (λ Z → impEnvʷ Wᴸ (Fin.suc Z)) ⊢
          renameᵗ (toRenameᵗ ηᴸ↓) (lookupStore (sourceStoreʷ W₁) Xᴸ)
          ⊑ renameᵗ (toRenameᵗ ηᴿ↓) (lookupStore (targetStoreʷ Wᴸ) Xᴿ)
    represented {Xᴸ} {Xᴿ} aligned =
      unshift-⊑
        (subst≡
          (λ L → instᵐ (λ Z → impEnvʷ Wᴸ (Fin.suc Z)) ⊢ L ⊑
            ⇑ᵗ (renameᵗ (toRenameᵗ ηᴿ↓)
              (lookupStore (targetStoreʷ Wᴸ) Xᴿ)))
          (source-representation-shift Xᴸ)
          (subst≡
            (λ R → instᵐ (λ Z → impEnvʷ Wᴸ (Fin.suc Z)) ⊢
              renameᵗ (toRenameᵗ (ηᴸʷ Wᴸ))
                (lookupStore (sourceStoreʷ Wᴸ) (Fin.suc Xᴸ)) ⊑ R)
            (target-representation-shift Xᴿ)
            (imp-env-weaken lower-env
              (CTX.representationsImprecise (CTX.invariantsʷ Wᴸ)
                (trans (sym (source-image Xᴸ))
                  (trans (cong Fin.suc aligned) (target-image Xᴿ)))))))

    unmatched : ∀ Xᴿ
      → (∀ Xᴸ → toRenameᵗ ηᴸ↓ Xᴸ ≢ toRenameᵗ ηᴿ↓ Xᴿ)
      → lookupStore (targetStoreʷ Wᴸ) Xᴿ ≡ ★
        ⊎ Σ[ Yᴿ ∈ TyVar _ ]
            (lookupStore (targetStoreʷ Wᴸ) Xᴿ ≡ ＇ Yᴿ)
          × (∀ Xᴸ → toRenameᵗ ηᴸ↓ Xᴸ ≢ toRenameᵗ ηᴿ↓ Yᴿ)
    unmatched Xᴿ no-source
        with CTX.unmatchedTargetsDynamic (CTX.invariantsʷ Wᴸ) Xᴿ
          no-lifted-source
      where
      no-lifted-source : ∀ Xᴸ
        → toRenameᵗ (ηᴸʷ Wᴸ) Xᴸ ≢ toRenameᵗ (ηᴿʷ Wᴸ) Xᴿ
      no-lifted-source Fin.zero aligned =
        fin-suc-not-zero
          (sym (trans (cong (λ η → toRenameᵗ η Fin.zero) keep-eq)
            (trans aligned (sym (target-image Xᴿ)))))
      no-lifted-source (Fin.suc Xᴸ) aligned =
        no-source Xᴸ
          (fin-suc-injective
            (trans (source-image Xᴸ)
              (trans aligned (sym (target-image Xᴿ)))))
    unmatched Xᴿ no-source | inj₁ dynamic = inj₁ dynamic
    unmatched Xᴿ no-source | inj₂ (Yᴿ , entry , no-lifted-source) =
      inj₂ (Yᴿ , entry , no-lowered-source)
      where
      no-lowered-source : ∀ Xᴸ
        → toRenameᵗ ηᴸ↓ Xᴸ ≢ toRenameᵗ ηᴿ↓ Yᴿ
      no-lowered-source Xᴸ aligned =
        no-lifted-source (Fin.suc Xᴸ)
          (trans (sym (source-image Xᴸ))
            (trans (cong Fin.suc aligned) (target-image Yᴿ)))

    source-entry-shift : ∀ Xᴸ
      → lookupStore (sourceStoreʷ Wᴸ) (Fin.suc Xᴸ)
        ≡ ⇑ᵗ (lookupStore (sourceStoreʷ W₁) Xᴸ)
    source-entry-shift Xᴸ =
      sym (cong (λ Σ → lookupStore Σ (Fin.suc Xᴸ)) source-stores)

    unoccupied : ∀ Xᴸ
      → impEnvʷ Wᴸ (Fin.suc (toRenameᵗ ηᴸ↓ Xᴸ)) ≡ X⊑★
      → lookupStore (sourceStoreʷ W₁) Xᴸ ≡ ★
      → ∀ Xᴿ → toRenameᵗ ηᴿ↓ Xᴿ ≢ toRenameᵗ ηᴸ↓ Xᴸ
    unoccupied Xᴸ mark entry Xᴿ aligned =
      CTX.dynamicStarSourcesUnoccupied (CTX.invariantsʷ Wᴸ)
        (Fin.suc Xᴸ)
        (subst≡ (λ Z → impEnvʷ Wᴸ Z ≡ X⊑★)
          (source-image Xᴸ) mark)
        (trans (source-entry-shift Xᴸ) (cong ⇑ᵗ entry)) Xᴿ
        (trans (sym (target-image Xᴿ))
          (trans (cong Fin.suc aligned) (source-image Xᴸ)))

  lowerLiftWorldLeft : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt Wᴸ (CTX.liftWorldLeft W₁) (Fin.suc X) Y
    → World Δᴸ Δᴿ Δ
  lowerLiftWorldLeft {W₁ = W₁} {Wᴸ = Wᴸ} {Y = Y} link =
    CTX.lower-leftʷ W₁ Wᴸ
      (dropKeep (ηᴸʷ Wᴸ) (lift-source-zero-fixed link))
      (dropSkip (ηᴿʷ Wᴸ) Y (lift-target-nonzero link))
      (dropKeep-eq (ηᴸʷ Wᴸ) (lift-source-zero-fixed link))
      (dropSkip-eq (ηᴿʷ Wᴸ) Y (lift-target-nonzero link))
      (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime link))
      (lowerLiftWorldLeft-invariants link)

  lowerLiftWorldLeft-decay : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → (link : RebaseAt Wᴸ (CTX.liftWorldLeft W₁)
        (Fin.suc X) Y)
    → WD.EnvDecay Wᴸ
        (CTX.liftWorldLeft (lowerLiftWorldLeft link))
  lowerLiftWorldLeft-decay {W₁ = W₁} {Wᴸ = Wᴸ} {Y = Y} link =
    WD.env-decay
      (dropKeep-eq (ηᴸʷ Wᴸ) (lift-source-zero-fixed link))
      (dropSkip-eq (ηᴿʷ Wᴸ) Y (lift-target-nonzero link))
      (CTX.SameRuntime.sourceStore-same
        (CTX.RebaseAt.sameRuntime link))
      refl
      env-mono
    where
    env-mono : CTX.ImpEnvMono Wᴸ
      (CTX.liftWorldLeft (lowerLiftWorldLeft link))
    env-mono = CTX.imp-env-mono dynamic precise
      where
      dynamic : ∀ Z
        → impEnvʷ Wᴸ Z ≡ X⊑★
        → impEnvʷ (CTX.liftWorldLeft (lowerLiftWorldLeft link)) Z
            ≡ X⊑★
      dynamic Fin.zero mark = refl
      dynamic (Fin.suc Z) mark = mark

      head-not-precise : impEnvʷ Wᴸ Fin.zero ≢ X⊑X
      head-not-precise mark
          with CTX.preciseMarksAligned (CTX.invariantsʷ Wᴸ) Fin.zero
            (subst≡ (λ Z → impEnvʷ Wᴸ Z ≡ X⊑X)
              (sym (lift-source-zero-fixed link)) mark)
      head-not-precise mark | Z , aligned =
        lift-target-nonzero link Z
          (trans aligned (lift-source-zero-fixed link))

      precise : ∀ Z
        → impEnvʷ Wᴸ Z ≡ X⊑X
        → impEnvʷ (CTX.liftWorldLeft (lowerLiftWorldLeft link)) Z
            ≡ X⊑X
      precise Fin.zero mark = ⊥-elim (head-not-precise mark)
      precise (Fin.suc Z) mark = mark

  lowerLiftWorldLeft-mono : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {link : RebaseAt Wᴸ (CTX.liftWorldLeft W₁)
        (Fin.suc X) Y}
    → CTX.ImpEnvMono (CTX.liftWorldLeft W₁) Wᴸ
    → CTX.ImpEnvMono W₁ (lowerLiftWorldLeft link)
  lowerLiftWorldLeft-mono {W₁ = W₁} {link = link} mono =
    CTX.imp-env-mono dynamic precise
    where
    dynamic : ∀ Z
      → impEnvʷ W₁ Z ≡ X⊑★
      → impEnvʷ (lowerLiftWorldLeft link) Z ≡ X⊑★
    dynamic Z mark = CTX.dynamic-preserved mono (Fin.suc Z) mark

    precise : ∀ Z
      → impEnvʷ W₁ Z ≡ X⊑X
      → impEnvʷ (lowerLiftWorldLeft link) Z ≡ X⊑X
    precise Z mark = CTX.precise-preserved mono (Fin.suc Z) mark

  lowerLiftWorldLeft-rebase : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → (link : RebaseAt Wᴸ (CTX.liftWorldLeft W₁)
        (Fin.suc X) Y)
    → RebaseAt (lowerLiftWorldLeft link) W₁ X Y
  lowerLiftWorldLeft-rebase {W₁ = W₁} {Wᴸ = Wᴸ} {X = X} {Y = Y}
      link =
    CTX.rebase-at
      (CTX.same-runtime refl
        (CTX.SameRuntime.targetStore-same
          (CTX.RebaseAt.sameRuntime link)))
      source-off target-frozen pivot-aligned store-representations
    where
    zero-fixed = lift-source-zero-fixed link
    nonzero = lift-target-nonzero link

    source-off : ∀ {Z} → Z ≢ X
      → toRenameᵗ (ηᴸʷ W₁) Z
          ≡ toRenameᵗ
              (ηᴸʷ (lowerLiftWorldLeft link)) Z
    source-off {Z} Z≢X =
      fin-suc-injective
        (trans (CTX.RebaseAt.ηᴸ-off-pivot link
                 (λ eq → Z≢X (fin-suc-injective eq)))
          (cong (λ η → toRenameᵗ η (Fin.suc Z))
            (sym (dropKeep-eq (ηᴸʷ Wᴸ) zero-fixed))))

    target-frozen : ∀ Z
      → toRenameᵗ (ηᴿʷ W₁) Z
          ≡ toRenameᵗ
              (ηᴿʷ (lowerLiftWorldLeft link)) Z
    target-frozen Z =
      fin-suc-injective
        (trans (CTX.RebaseAt.ηᴿ-frozen link Z)
          (cong (λ η → toRenameᵗ η Z)
            (sym (dropSkip-eq (ηᴿʷ Wᴸ) Y nonzero))))

    pivot-aligned :
      toRenameᵗ (ηᴸʷ W₁) X ≡ toRenameᵗ (ηᴿʷ W₁) Y
    pivot-aligned = fin-suc-injective (CTX.RebaseAt.pivotAligned link)

    store-representations :
      CTX.StoreRepImp W₁ X Y
    store-representations =
      CTX.store-rep-imp
        (lowerWorldLeft-shift-⊑ᵂ {W = W₁}
          (CTX.StoreRepImp.represented
            (CTX.RebaseAt.storeRepresentations link)))

  record LoweredLiftCtx {Δᴸ Δᴿ Δ}
      {W₁ W★ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      (γ₁ : CtxImp W₁)
      (γᴸ : CtxImp Wᴸ)
      (dec : WD.EnvDecay Wᴸ (CTX.liftWorldLeft W★)) :
      Set where
    constructor lowered-lift-ctx
    field
      γ★ : CtxImp W★
      γ★ᴸ : CtxImp (CTX.liftWorldLeft W★)
      lift★ : CTX.LiftCtxᴸ X⊑★ γ★ γ★ᴸ
      same★ : CTX.SameCtx γ₁ γ★
      tgtCtx★ : CTX.tgtCtxʷ γ★ᴸ ≡ CTX.tgtCtxʷ γ★
      γ★ᴸ-decay : γ★ᴸ ≡ WD.decayCtx dec γᴸ

  lowerLiftCtx : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W★ : World Δᴸ Δᴿ Δ}
      {Wᴸ : World (suc Δᴸ) Δᴿ (suc Δ)}
      {γ₁ : CtxImp W₁}
      {γ₁ᴸ : CtxImp (CTX.liftWorldLeft W₁)}
      {γᴸ : CtxImp Wᴸ}
      (dec : WD.EnvDecay Wᴸ (CTX.liftWorldLeft W★))
    → CTX.LiftCtxᴸ X⊑★ γ₁ γ₁ᴸ
    → CTX.SameCtx γ₁ᴸ γᴸ
    → LoweredLiftCtx γ₁ γᴸ dec
  lowerLiftCtx {W★ = W★} {γ₁ = []} {γ₁ᴸ = []} dec
      CTX.liftᴸ-[] CTX.same-[] =
    lowered-lift-ctx [] [] CTX.liftᴸ-[] CTX.same-[] refl refl
  lowerLiftCtx {W★ = W★}
      {γ₁ = CTX.ctx-imp A B p ∷ γ₁} dec
      (CTX.liftᴸ-∷ {A = A} {B = B} liftγ)
      (CTX.same-∷ {p′ = pᴸ} same)
      with lowerLiftCtx dec liftγ same
  lowerLiftCtx {W★ = W★}
      {γ₁ = CTX.ctx-imp A B p ∷ γ₁} dec
      (CTX.liftᴸ-∷ {A = A} {B = B} liftγ)
      (CTX.same-∷ {p′ = pᴸ} same)
      | lowered-lift-ctx γ★ γ★ᴸ lift★ same★ tgtCtx★
          γ★ᴸ-decay =
    lowered-lift-ctx
      (CTX.ctx-imp A B
        (lowerWorldLeft-shift-⊑ᵂ {W = W★} (WD.decay⊑ᵂ dec pᴸ))
        ∷ γ★)
      (CTX.ctx-imp (⇑ᵗ A) B (WD.decay⊑ᵂ dec pᴸ) ∷ γ★ᴸ)
      (CTX.liftᴸ-∷ lift★)
      (CTX.same-∷ same★)
      (cong (B ∷_) tgtCtx★)
      (cong (λ γ → CTX.ctx-imp (⇑ᵗ A) B
        (WD.decay⊑ᵂ dec pᴸ) ∷ γ) γ★ᴸ-decay)

  source-binder-strengthen-terminus : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ}
      {γᵒᴸ : CtxImp (CTX.liftWorldLeft Wᵒ)}
      {V : Term (suc Δᴸ)} {A : Ty (suc Δᴸ)}
      {U : Term Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {S : Ty Δᴿ}
    → CTX.LiftCtxᴸ X⊑★ γᵒ γᵒᴸ
    → TargetSealTerminusData (CTX.liftWorldLeft Wᵒ)
        γᵒᴸ V A U (Fin.suc Xᴸ) Y S
    → TargetSealTerminusᴸData Wᵒ γᵒ V A U Xᴸ Y S
  source-binder-strengthen-terminus {Δᴿ = Δᴿ} {γᵒ = γᵒ}
      {γᵒᴸ = γᵒᴸ} {V = V} liftᵒ
      (target-seal-terminus-data U★ Y★ W★ᴸ γ★ᴸ₀
        mono★ᴸ same★ᴸ boundary★ᴸ target∈★ q★ᴸ premise★ᴸ)
      with lowerLiftCtx (lowerLiftWorldLeft-decay boundary★ᴸ)
        liftᵒ same★ᴸ
  source-binder-strengthen-terminus {Δᴿ = Δᴿ} {γᵒ = γᵒ}
      {γᵒᴸ = γᵒᴸ} {V = V} liftᵒ
      (target-seal-terminus-data U★ Y★ W★ᴸ γ★ᴸ₀
        mono★ᴸ same★ᴸ boundary★ᴸ target∈★ q★ᴸ premise★ᴸ)
      | lowered-lift-ctx γ★ γ★ᴸ lift★ same★ tgtCtx★
          γ★ᴸ-decay =
    target-seal-terminusᴸ-data U★ Y★ W★ γ★ γᵒᴸ γ★ᴸ
      liftᵒ lift★ mono★ same★ boundary★ target∈★ body★ U⊢★
      premise★
    where
    W★ = lowerLiftWorldLeft boundary★ᴸ
    dec = lowerLiftWorldLeft-decay boundary★ᴸ
    mono★ = lowerLiftWorldLeft-mono {link = boundary★ᴸ} mono★ᴸ
    boundary★ = lowerLiftWorldLeft-rebase boundary★ᴸ
    body★ = WD.decay⊑ᵂ dec q★ᴸ
    premise★ = subst≡
      (λ γ′ → CTX.liftWorldLeft W★ ∣ γ′ ⊢² V ⊑ U★
        ∶ body★)
      (sym γ★ᴸ-decay)
      (TD.⊢²-decay-at dec premise★ᴸ body★)

    tgtCtx-eq :
      CTX.tgtCtxʷ (WD.decayCtx dec γ★ᴸ₀) ≡ CTX.tgtCtxʷ γ★
    tgtCtx-eq = trans (cong CTX.tgtCtxʷ (sym γ★ᴸ-decay)) tgtCtx★

    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , CTX.tgtCtxʷ γ★ ⟩
      ⊢ U★ ⦂ ★
    U⊢★ =
      subst≡ (λ Γ → ⟨ Δᴿ , targetStoreʷ W★ , Γ ⟩
        ⊢ U★ ⦂ ★)
        tgtCtx-eq
        (CTI2T.target-typing² (TD.⊢²-decay-at dec premise★ᴸ body★))

  source-binder-strengthen-terminus {γᵒᴸ = γᵒᴸ} {U = U}
      {Xᴸ = Xᴸ} {Y = Y} {S = S} liftᵒ
      (target-seal-terminus-paired {P = P} source∈ᵒ target∈ᵒ
        boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ) =
    target-seal-terminusᴸ-paired {P = P} {U = U} {Xᴸ = Xᴸ}
      {Y = Y} {S = S} refl refl γᵒᴸ liftᵒ source∈ᵒ target∈ᵒ
      boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ

  source-binder-strengthen-strip : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ}
      {γᵒᴸ : CtxImp (CTX.liftWorldLeft Wᵒ)}
      {γᵖ : CtxImp Wᵖ}
      {γᵇ : CtxImp (CTX.liftWorldLeft Wᵖ)}
      {V : Term (suc Δᴸ)} {A : Ty (suc Δᴸ)}
      {U : Term Δᴿ} {S : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {p : A ⊑ᵂ⟨ CTX.liftWorldLeft Wᵖ ⟩ ★}
    → CTX.LiftCtxᴸ X⊑★ γᵒ γᵒᴸ
    → TargetStripAt★Data
        (CTX.liftWorldLeft Wᵒ) γᵒᴸ
        V A U (Fin.suc Xᴸ) Y S cY
        (CTX.liftWorldLeft Wᵖ) γᵇ p
    → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY
        Wᵖ γᵖ γᵇ p
  source-binder-strengthen-strip {Δᴿ = Δᴿ} {Wᵖ = Wᵖ}
      {γᵒ = γᵒ} {γᵒᴸ = γᵒᴸ} {γᵇ = γᵇ}
      {V = V} {U = U} {S = S} {Y = Y} {cY = cY}
      {p = p} liftᵒ
      (target-strip★-data U★ Y★ W★ᴸ γ★ᴸ₀ mono★ᴸ same★ᴸ
        boundary★ᴸ target∈★ q★ᴸ premise★ᴸ reemitᴸ)
      with lowerLiftCtx (lowerLiftWorldLeft-decay boundary★ᴸ)
        liftᵒ same★ᴸ
  source-binder-strengthen-strip {Δᴿ = Δᴿ} {Wᵖ = Wᵖ}
      {γᵒ = γᵒ} {γᵒᴸ = γᵒᴸ} {γᵇ = γᵇ}
      {V = V} {U = U} {S = S} {Y = Y} {cY = cY}
      {p = p} liftᵒ
      (target-strip★-data U★ Y★ W★ᴸ γ★ᴸ₀ mono★ᴸ same★ᴸ
        boundary★ᴸ target∈★ q★ᴸ premise★ᴸ reemitᴸ)
      | lowered-lift-ctx γ★ γ★ᴸ lift★ same★ tgtCtx★
          γ★ᴸ-decay =
    target-strip★ᴸ-data U★ Y★ W★ γ★ γ★ᴸ lift★ mono★
      same★ boundary★ target∈★ body★ U⊢★ premise★ reemit★
    where
    W★ = lowerLiftWorldLeft boundary★ᴸ
    dec = lowerLiftWorldLeft-decay boundary★ᴸ
    mono★ = lowerLiftWorldLeft-mono {link = boundary★ᴸ} mono★ᴸ
    boundary★ = lowerLiftWorldLeft-rebase boundary★ᴸ
    body★ = WD.decay⊑ᵂ dec q★ᴸ
    premise★ = subst≡
      (λ γ′ → CTX.liftWorldLeft W★ ∣ γ′ ⊢² V ⊑ U★
        ∶ body★)
      (sym γ★ᴸ-decay)
      (TD.⊢²-decay-at dec premise★ᴸ body★)

    tgtCtx-eq :
      CTX.tgtCtxʷ (WD.decayCtx dec γ★ᴸ₀) ≡ CTX.tgtCtxʷ γ★
    tgtCtx-eq = trans (cong CTX.tgtCtxʷ (sym γ★ᴸ-decay)) tgtCtx★

    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , CTX.tgtCtxʷ γ★ ⟩
      ⊢ U★ ⦂ ★
    U⊢★ =
      subst≡ (λ Γ → ⟨ Δᴿ , targetStoreʷ W★ , Γ ⟩
        ⊢ U★ ⦂ ★)
        tgtCtx-eq
        (CTI2T.target-typing² (TD.⊢²-decay-at dec premise★ᴸ body★))

    reemit★ :
      CTX.liftWorldLeft W★ ∣ γ★ᴸ ⊢² V ⊑ U★ ∶ body★
      → CTI2._∣_⊢²_⊑_∶_
          (CTX.liftWorldLeft Wᵖ) γᵇ
          V ((U ↓ seal Y S) ⟨ cY ⟩) p
    reemit★ _ = reemitᴸ premise★ᴸ

  source-binder-strengthen-strip {γᵒᴸ = γᵒᴸ} {U = U} {S = S}
      {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p} liftᵒ
      (target-strip★-paired {P = P} source∈ᵒ target∈ᵒ boundaryᵒ
        residualᵒ monoᵐ sameᵐ premiseᵐ reemit) =
    target-strip★ᴸ-paired {P = P} {U = U} {Xᴸ = Xᴸ} {Y = Y}
      {S = S} {cY = cY} {p = p} refl refl γᵒᴸ liftᵒ source∈ᵒ target∈ᵒ
      boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ reemit

  all-to-star-obligation : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty (suc Δᴸ)}
    → NonVar A
    → Fin.zero ∈ᵗ A
    → A ⊑ᵂ⟨ CTX.liftWorldLeft W ⟩ ★
    → `∀ A ⊑ᵂ⟨ W ⟩ ★
  all-to-star-obligation {W = W} {A = A} Anv z∈A body★ =
    ∀⊑
      (renameNonVar (extᵗ (toRenameᵗ (ηᴸʷ W))) Anv)
      (rename-occurs (extᵗ (toRenameᵗ (ηᴸʷ W))) z∈A)
      (subst≡
        (λ T → instᵐ (impEnvʷ W) ⊢ T ⊑ ★)
        (renameᵗ-cong A (toRename-keep-eq (ηᴸʷ W)))
        body★)

  shift-not-zero : ∀ {Δ} {A : Ty Δ}
    → (＇ Fin.zero) ≢ ⇑ᵗ A
  shift-not-zero {A = ＇ X} ()
  shift-not-zero {A = ‵ ι} ()
  shift-not-zero {A = ★} ()
  shift-not-zero {A = A ⇒ B} ()
  shift-not-zero {A = `∀ A} ()

  resolveVar-var : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    → Σ ∋ X ⦂ (＇ Y)
    → CTX.resolveVar Σ X ≡ CTX.resolveVar Σ Y
  resolveVar-var {Y = Fin.zero} (Z∋ eq) =
    ⊥-elim (shift-not-zero eq)
  resolveVar-var {Y = Fin.suc Y} (Z∋ {A = ＇ .Y} refl) = refl
  resolveVar-var {Y = Fin.zero} (S-lift∋ X∈ eq) =
    ⊥-elim (shift-not-zero eq)
  resolveVar-var {Y = Fin.suc Y} (S-lift∋ {A = ＇ .Y} X∈ refl) =
    cong ⇑ᵗ (resolveVar-var X∈)
  resolveVar-var {Y = Fin.zero} (S-bind∋ X∈ eq) =
    ⊥-elim (shift-not-zero eq)
  resolveVar-var {Y = Fin.suc Y} (S-bind∋ {A = ＇ .Y} X∈ refl) =
    cong ⇑ᵗ (resolveVar-var X∈)

  resolveVar-var-nonvar : ∀ {Δ} {Σ : TyStore Δ}
      {X Y : TyVar Δ} {S : Ty Δ}
    → Σ ∋ X ⦂ (＇ Y)
    → Σ ∋ Y ⦂ S
    → NonVar S
    → CTX.resolveVar Σ X ≡ S
  resolveVar-var-nonvar X∈ Y∈ Snv =
    trans (resolveVar-var X∈) (SPT.resolveVar-nonvar Y∈ Snv)

  seal-target-var-nonstar-⊥ : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ} {S : Ty Δᴿ}
    → sourceStoreʷ W ∋ X ⦂ ★
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Y ⦂ (＇ Y′)
    → targetStoreʷ W′ ∋ Y′ ⦂ S
    → NonVar S
    → NonStar S
    → ⊥
  seal-target-var-nonstar-⊥ {W = W} {X = X} {Y = Y}
      source∈ rb target∈ target′∈ Snv Sns =
    star-source-nonstar-⊥ {W = W}
      (subst≡ (λ T → ★ ⊑ᵂ⟨ W ⟩ T)
        (resolveVar-var-nonvar target∈
          (rebase-target-membership-back rb target′∈) Snv)
        (subst≡
          (λ T → T ⊑ᵂ⟨ W ⟩ CTX.resolveVar (targetStoreʷ W) Y)
          (SPT.resolveVar-nonvar source∈ nonvar-star)
          (CTX.StoreRepImp.represented
            (CTX.RebaseAt.storeRepresentations rb))))
      Sns

  tagged-seal-source-fold-⊥ : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
      {V : Term Δᴸ} {N : Term Δᴿ} {A : Ty Δᴸ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
    → SpineValue V
    → NonVar A
    → NonStar A
    → Wᵖ ∣ γᵖ ⊢² V ⊑ N ⟨ cY ⟩ ∶ p
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y cY p
  tagged-seal-source-fold-⊥ {Wᵖ = Wᵖ} {γᵖ = γᵖ}
      {V = V} {Y = Y} {cY = cY} {p = p} sv Anv Ans D =
    dispatch-source-fold λ {U} {S} eq vU target∈ →
      ⊥-elim
        (tagged-target-nonvar-nonstar-spine-⊥ sv Anv Ans
          (subst≡
            (λ N′ → Wᵖ ∣ γᵖ ⊢² V ⊑ N′ ⟨ cY ⟩ ∶ p)
            eq D))

  shift-nonstar : ∀ {Δ} {A : Ty Δ}
    → NonStar A
    → NonStar (⇑ᵗ A)
  shift-nonstar nonstar-X = nonstar-X
  shift-nonstar nonstar-ι = nonstar-ι
  shift-nonstar nonstar-⇒ = nonstar-⇒
  shift-nonstar nonstar-∀ = nonstar-∀

  data StarEntryView {Δ} (Σ : TyStore Δ) : Ty Δ → Set where
    star-entry : ∀ {A Y★}
      → Σ ∋ Y★ ⦂ ★
      → A ≡ ★
      → StarEntryView Σ A

    star-nonstar : ∀ {A}
      → NonStar A
      → StarEntryView Σ A

  resolveVar-star-view : ∀ {Δ}
    → (Σ : TyStore Δ)
    → (Y : TyVar Δ)
    → StarEntryView Σ (CTX.resolveVar Σ Y)
  resolveVar-star-view store-empty ()
  resolveVar-star-view (store-lift Σ) Fin.zero =
    star-nonstar nonstar-X
  resolveVar-star-view (store-lift Σ) (Fin.suc Y)
      with resolveVar-star-view Σ Y
  resolveVar-star-view (store-lift Σ) (Fin.suc Y)
      | star-entry Y★∈ eq =
    star-entry (S-lift∋ Y★∈ refl) (cong ⇑ᵗ eq)
  resolveVar-star-view (store-lift Σ) (Fin.suc Y)
      | star-nonstar Ans =
    star-nonstar (shift-nonstar Ans)
  resolveVar-star-view (store-bind Σ (＇ X)) Fin.zero
      with resolveVar-star-view Σ X
  resolveVar-star-view (store-bind Σ (＇ X)) Fin.zero
      | star-entry Y★∈ eq =
    star-entry (S-bind∋ Y★∈ refl) (cong ⇑ᵗ eq)
  resolveVar-star-view (store-bind Σ (＇ X)) Fin.zero
      | star-nonstar Ans =
    star-nonstar (shift-nonstar Ans)
  resolveVar-star-view (store-bind Σ (‵ ι)) Fin.zero =
    star-nonstar nonstar-ι
  resolveVar-star-view (store-bind Σ ★) Fin.zero =
    star-entry (Z∋ refl) refl
  resolveVar-star-view (store-bind Σ (A ⇒ B)) Fin.zero =
    star-nonstar nonstar-⇒
  resolveVar-star-view (store-bind Σ (`∀ A)) Fin.zero =
    star-nonstar nonstar-∀
  resolveVar-star-view (store-bind Σ A) (Fin.suc Y)
      with resolveVar-star-view Σ Y
  resolveVar-star-view (store-bind Σ A) (Fin.suc Y)
      | star-entry Y★∈ eq =
    star-entry (S-bind∋ Y★∈ refl) (cong ⇑ᵗ eq)
  resolveVar-star-view (store-bind Σ A) (Fin.suc Y)
      | star-nonstar Ans =
    star-nonstar (shift-nonstar Ans)

  star-entry-view-terminal : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴿ}
    → StarEntryView (targetStoreʷ W) A
    → ★ ⊑ᵂ⟨ W ⟩ A
    → Σ[ Y★ ∈ TyVar Δᴿ ] targetStoreʷ W ∋ Y★ ⦂ ★
  star-entry-view-terminal (star-entry {Y★ = Y★} Y★∈ eq) p =
    Y★ , Y★∈
  star-entry-view-terminal {W = W} {A = A} (star-nonstar Ans) p =
    ⊥-elim (star-source-nonstar-⊥ {W = W} {S = A} p Ans)

  target-star-terminal-entry : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
    → RebaseAt Wᵖ Wᵒ Xᴸ Y
    → Σ[ Y★ ∈ TyVar Δᴿ ] targetStoreʷ Wᵖ ∋ Y★ ⦂ ★
  target-star-terminal-entry {Wᵒ = Wᵒ} {Y = Y} source∈ rb
      with star-entry-view-terminal {W = Wᵒ}
        {A = CTX.resolveVar (targetStoreʷ Wᵒ) Y}
        (resolveVar-star-view (targetStoreʷ Wᵒ) Y) target★
    where
    target★ : ★ ⊑ᵂ⟨ Wᵒ ⟩ CTX.resolveVar (targetStoreʷ Wᵒ) Y
    target★ =
      subst≡
        (λ T → T ⊑ᵂ⟨ Wᵒ ⟩ CTX.resolveVar (targetStoreʷ Wᵒ) Y)
        (SPT.resolveVar-nonvar source∈ nonvar-star)
        (CTX.StoreRepImp.represented
          (CTX.RebaseAt.storeRepresentations rb))
  target-star-terminal-entry {Wᵒ = Wᵒ} source∈ rb | Y★ , Y★∈ =
    Y★ , rebase-target-membership-forward rb Y★∈

seal-descent-current-star : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {r : (＇ X) ⊑ᵂ⟨ W ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ r
  → TargetSealTerminusData W γ V (＇ X) U X Y ★
seal-descent-current-star {U = U} {X = X} {Y = Y} {r = r}
    sv vU source∈ target∈ D
    with STC.seal-transfer sv vU source∈ D
seal-descent-current-star {U = U} {X = X} {Y = Y} {r = r}
    sv vU source∈ target∈ D
    | STC.seal-transfer-stripped {W₂ = W★} {γ₂ = γ★} {q₂ = q★}
        link mono★ same★ premise★ =
  target-seal-terminus-data U Y W★ γ★ mono★ same★ link
    (rebase-target-membership-forward link target∈) q★ premise★
seal-descent-current-star {U = U} {X = X} {Y = Y} {r = r}
    sv vU source∈ target∈ D
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢ prem =
  target-seal-terminus-paired source∈ target∈ rbᵖ
    (CTI2.conceal⊑conceal²
      (Conv.⊢↓-seal source∈) (Conv.⊢↓-seal target∈)
      refl (λ ()) ★⊑★ monoᵖ rbᵖ scᵖ prem r)
    monoᵖ scᵖ prem

seal-descent-current-var : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    {r : (＇ X) ⊑ᵂ⟨ W ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → sourceStoreʷ W ∋ X ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ (＇ Y′)
  → W ∣ γ ⊢² V ⊑ U ↓ seal Y (＇ Y′) ∶ r
  → TargetSealTerminusData W γ V (＇ X) U X Y (＇ Y′)
seal-descent-current-var {Y = Y} (sv-cast sv₀ ()) vU
    source∈ target∈ (CTI2.cast⊑² c prem r)
seal-descent-current-var {W = W} {Y = Y} (sv-seal sv₀) vU
    source∈ target∈
    (CTI2.conceal⊑² {p = p} (Conv.⊢↓-seal source∈′)
      pos≢absent mark disaligned represented prem r) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = W} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ W ⟩ ＇ Y)
        (store-lookup-unique source∈′ source∈) p)
      nonstar-X)
seal-descent-current-var (sv-seal sv₀) vU source∈ target∈
    (CTI2.conceal⊑-neutral² (Conv.⊢↓-seal source∈′) () prem r)
seal-descent-current-var {Y′ = Y′} (sv-seal sv₀) vU
    source∈ target∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      (Conv.⊢↓-seal source∈′) target⊢ aligned pos≢absent
      represented mono rb sc prem r) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y′}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y′)
        (store-lookup-unique source∈′ source∈) p)
      nonstar-X)
seal-descent-current-var sv vU source∈ target∈
    (CTI2.⊑conceal² (Conv.⊢↓-seal target∈′) () prem r)

seal-descent-at-var-＇ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γʳ : CtxImp Wʳ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {Xᴸ : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    {r : A ⊑ᵂ⟨ Wʳ ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → CTX.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTX.SameCtx γᵒ γʳ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ ＇ Y′
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y (＇ Y′) ∶ r
  → TargetSealTerminusData Wᵒ γᵒ V A U Xᴸ Y (＇ Y′)
seal-descent-at-var-＇ {Wʳ = Wʳ} {A = A} {Y = Y} {r = r}
    sv vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem .r)
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} {r = r}
    sv vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem .r)
    | X₂ , refl , aligned
    with sv
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} {r = r}
    sv vU mono rb sc source∈ target∈ (CTI2.cast⊑² c prem .r)
    | X₂ , refl , aligned | sv-cast sv₀ ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {A = A} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} (sv-seal sv₀) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {p = p} (Conv.⊢↓-seal source∈′)
      pos≢absent mark disaligned represented prem .r)
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} (sv-seal sv₀) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {p = p} (Conv.⊢↓-seal source∈′)
      pos≢absent mark disaligned represented prem .r)
    | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ rb r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} (sv-seal sv₀) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑² {p = p} (Conv.⊢↓-seal source∈′)
      pos≢absent mark disaligned represented prem .r)
    | .Xᴸ , refl , aligned | refl =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wʳ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wʳ ⟩ ＇ Y)
        (store-lookup-unique source∈′
          (rebase-source-membership rb source∈))
        p)
      nonstar-X)
seal-descent-at-var-＇ (sv-seal sv₀) vU mono rb sc source∈ target∈
    (CTI2.conceal⊑-neutral² (Conv.⊢↓-seal source∈′) () prem r)
seal-descent-at-var-＇ {Wʳ = Wʳ} {A = A} {Xᴸ = Xᴸ} {Y = Y}
    {Y′ = Y′} {r = r} (sv-seal sv₀) vU mono rb sc source∈
    target∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      (Conv.⊢↓-seal source∈′) target⊢ alignedᵖ pos≢absent
      representedᵖ mono₁ rb₁ sc₁ prem .r)
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Xᴸ = Xᴸ} {Y = Y}
    {Y′ = Y′} {r = r} (sv-seal sv₀) vU mono rb sc source∈
    target∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      (Conv.⊢↓-seal source∈′) target⊢ alignedᵖ pos≢absent
      representedᵖ mono₁ rb₁ sc₁ prem .r)
    | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ rb r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Xᴸ = Xᴸ} {Y = Y}
    {Y′ = Y′} {r = r} (sv-seal sv₀) vU mono rb sc source∈
    target∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      (Conv.⊢↓-seal source∈′) target⊢ alignedᵖ pos≢absent
      representedᵖ mono₁ rb₁ sc₁ prem .r)
    | .Xᴸ , refl , aligned | refl =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y′}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y′)
        (store-lookup-unique source∈′
          (rebase-source-membership rb source∈))
        p)
      nonstar-X)
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-Λ sv₀) vU mono rb
    sc source∈ target∈
    (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-Λ sv₀) vU mono rb
    sc source∈ target∈
    (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-Λ sv₀) vU mono rb
    sc source∈ target∈
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-Λ sv₀) vU mono rb
    sc source∈ target∈
    (CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-neutral² c⊢ pos≡absent prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-neutral² c⊢ pos≡absent prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-fun sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-neutral² c⊢ pos≡absent prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-neutral² c⊢ pos≡absent prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-reveal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑-neutral² c⊢ pos≡absent prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑-neutral² c⊢ pos≡absent prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented prem r)
    | ()
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑conceal² c⊢ c′⊢ aligned pos≢absent represented
      mono₁ rb₁ sc₁ prem r)
    with SPT.right-var-obligation-view {W = Wʳ} {Y = Y} r
seal-descent-at-var-＇ {Wʳ = Wʳ} {Y = Y} (sv-conceal-all sv₀) vU
    mono rb sc source∈ target∈
    (CTI2.conceal⊑conceal² c⊢ c′⊢ aligned pos≢absent represented
      mono₁ rb₁ sc₁ prem r)
    | ()
seal-descent-at-var-＇ sv vU mono rb sc source∈ target∈
    (CTI2.⊑conceal² (Conv.⊢↓-seal target∈′) () prem r)

seal-descent-at-var-nonvar : ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γʳ : CtxImp Wʳ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {r : A ⊑ᵂ⟨ Wʳ ⟩ ＇ Y}
  → NonVar S
  → NonStar S
  → SpineValue V
  → Value U
  → CTX.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTX.SameCtx γᵒ γʳ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
  → TargetSealTerminusData Wᵒ γᵒ V A U Xᴸ Y S
seal-descent-at-var-nonvar Snv Sns sv vU mono rb sc source∈
    target∈ D =
  ⊥-elim (seal-target-nonstar-⊥ source∈ rb target∈ Snv Sns)

seal-descent-at-var : SealDescentAtVar
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {A = A} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc source∈
    target∈ D
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc source∈
    target∈ D
    | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ rb r
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc source∈
    target∈ D
    | .Xᴸ , refl , aligned | refl
    with STC.seal-transfer sv vU
      (rebase-source-membership rb source∈) D
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc source∈ target∈ D
    | .Xᴸ , refl , aligned | refl
    | STC.seal-transfer-stripped {W₂ = W★} {γ₂ = γ★}
        {q₂ = q★} link mono★ʳ same★ʳ premise★ =
  target-seal-terminus-data U Y W★ γ★
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = W★}
      mono mono★ʳ)
    (sameCtx-∘ sc same★ʳ)
    (composeSamePivotRebase rb link)
    (rebase-target-membership-forward (composeSamePivotRebase rb link)
      target∈)
    q★ premise★
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc source∈ target∈ D
    | .Xᴸ , refl , aligned | refl
    | STC.seal-transfer-paired {Wᵖ = Wᵖ} {γᵖ = γᵖ}
        {P = P} monoᵖ rbᵖ scᵖ source⊢ target⊢ prem =
  target-seal-terminus-paired source∈ target∈
    (composeSamePivotRebase rb rbᵖ)
    (CTI2.conceal⊑conceal²
      (Conv.⊢↓-seal source∈)
      (Conv.⊢↓-seal target∈)
      refl
      (λ ())
      ★⊑★
      (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = Wᵖ} mono monoᵖ)
      (composeSamePivotRebase rb rbᵖ)
      (sameCtx-∘ sc scᵖ)
      prem
      (origin-var-obligation rb))
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = Wᵖ} mono monoᵖ)
    (sameCtx-∘ sc scᵖ) prem
seal-descent-at-var {S = ＇ Y′} sv vU mono rb sc source∈
    target∈ D =
  seal-descent-at-var-＇ sv vU mono rb sc source∈ target∈ D
seal-descent-at-var {S = ‵ ι} sv vU mono rb sc source∈ target∈ D =
  seal-descent-at-var-nonvar nonvar-base nonstar-ι
    sv vU mono rb sc source∈ target∈ D
seal-descent-at-var {S = S ⇒ T} sv vU mono rb sc source∈
    target∈ D =
  seal-descent-at-var-nonvar nonvar-fun nonstar-⇒
    sv vU mono rb sc source∈ target∈ D
seal-descent-at-var {S = `∀ S} sv vU mono rb sc source∈ target∈ D =
  seal-descent-at-var-nonvar nonvar-all nonstar-∀
    sv vU mono rb sc source∈ target∈ D

seal-descent-at-varᴸ : SealDescentAtVarᴸ
seal-descent-at-varᴸ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {γᵇ = γᵇ} {V = V} {U = U} {A = A}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc
    source∈ target∈ liftγ D
    with liftCtxᴸ-canonical γᵒ
seal-descent-at-varᴸ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {γᵇ = γᵇ} {V = V} {U = U} {A = A}
    {S = S} {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc
    source∈ target∈ liftγ D
    | γᵒᴸ , liftᵒ =
  source-binder-strengthen-terminus liftᵒ
    (seal-descent-at-var
      {Wᵒ = CTX.liftWorldLeft Wᵒ}
      {Wʳ = CTX.liftWorldLeft Wʳ}
      {γᵒ = γᵒᴸ}
      {γʳ = γᵇ}
      {V = V}
      {U = U}
      {A = A}
      {S = S}
      {Xᴸ = Fin.suc Xᴸ}
      {Y = Y}
      {r = r}
      sv vU
      (liftImpEnvMonoLeft {W = Wᵒ} {W′ = Wʳ} mono)
      (liftRebaseAtLeft {W = Wʳ} {W′ = Wᵒ} rb)
      (sameCtx-liftᴸ sc liftᵒ liftγ)
      (S-lift∋ source∈ refl)
      target∈
      D)

target-strip★-from-dispatch-case : ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
    {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → SpineValue V
  → Value U
  → CTX.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTX.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A
      (U ↓ seal Y S) Xᴸ Y cY p
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ p
target-strip★-from-dispatch-case sv vU mono rb sc source∈ target∈ D
    (dispatch-tag (tag-node★ r prem))
    with seal-descent-at-var sv vU mono rb sc source∈ target∈ prem
target-strip★-from-dispatch-case sv vU mono rb sc source∈ target∈ D
    (dispatch-tag (tag-node★ r prem))
    | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premise★ =
  target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
    target∈★ q★ premise★ (λ _ → D)
target-strip★-from-dispatch-case sv vU mono rb sc source∈ target∈ D
    (dispatch-tag (tag-node★ r prem))
    | target-seal-terminus-paired source∈ᵒ target∈ᵒ boundaryᵒ
        residualᵒ monoᵐ sameᵐ premiseᵐ =
  target-strip★-paired source∈ᵒ target∈ᵒ boundaryᵒ residualᵒ
    monoᵐ sameᵐ premiseᵐ (λ _ → D)
target-strip★-from-dispatch-case sv vU mono rb sc source∈ target∈ D
    (dispatch-source-fold resume) =
  resume refl vU target∈
target-strip★-from-dispatch-case sv vU mono rb sc source∈ target∈ D
    (dispatch-nonvar-empty bad) =
  ⊥-elim bad

tag-dispatch-at★ : TagDispatchAt★
tag-dispatch-at★ sv vN mono rb sc source∈
    (CTI2.⊑cast² {p = r} cY prem q) =
  dispatch-tag (tag-node★ r prem)
tag-dispatch-at★ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {V = Λ V} {N = N} {A = `∀ A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = q}
    (sv-Λ sv) vN mono rb sc source∈
    (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem .q) =
  dispatch-source-fold resume
  where
  resume : ∀ {U S}
    → N ≡ U ↓ seal Y S
    → Value U
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → TargetStripAt★Data Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S cY
        Wᵖ γᵖ q
  resume {U = U} {S = S} refl vU target∈
      with liftCtxᴸ-canonical γᵒ
  resume {U = U} {S = S} refl vU target∈ | γᵒᴸ , liftᵒ
      with tag-dispatch-at★
        {Wᵒ = CTX.liftWorldLeft Wᵒ}
        {Wᵖ = CTX.liftWorldLeft Wᵖ}
        {γᵒ = γᵒᴸ}
        {γᵖ = _}
        {V = V}
        {N = U ↓ seal Y S}
        {A = A}
        {Xᴸ = Fin.suc Xᴸ}
        {Y = Y}
        {cY = cY}
        {p = _}
        sv (vU ↓ seal)
        (liftImpEnvMonoLeft {W = Wᵒ} {W′ = Wᵖ} mono)
        (liftRebaseAtLeft {W = Wᵖ} {W′ = Wᵒ} rb)
        (sameCtx-liftᴸ sc liftᵒ liftγ)
        (S-lift∋ source∈ refl)
        prem
  resume {U = U} {S = S} refl vU target∈ | γᵒᴸ , liftᵒ
      | branch =
    build
      (source-binder-strengthen-strip {γᵖ = γᵖ} liftᵒ
        (target-strip★-from-dispatch-case
          {Wᵒ = CTX.liftWorldLeft Wᵒ}
          {Wᵖ = CTX.liftWorldLeft Wᵖ}
          {γᵒ = γᵒᴸ}
          {γᵖ = _}
          {V = V}
          {U = U}
          {A = A}
          {S = S}
          {Xᴸ = Fin.suc Xᴸ}
          {Y = Y}
          {cY = cY}
          {p = _}
          sv vU
          (liftImpEnvMonoLeft {W = Wᵒ} {W′ = Wᵖ} mono)
          (liftRebaseAtLeft {W = Wᵖ} {W′ = Wᵒ} rb)
          (sameCtx-liftᴸ sc liftᵒ liftγ)
          (S-lift∋ source∈ refl)
          target∈ prem branch))
    where
    build :
      TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ _ _
      → TargetStripAt★Data Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S cY
          Wᵖ γᵖ q
    build
      (target-strip★ᴸ-data U★ Y★ W★ γ★ γ★ᴸ lift★ mono★
        same★ boundary★ target∈★ body★ U⊢★ premise★ reemit) =
      target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premiseΛ (λ _ →
          CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem q)
      where
      q★ = all-to-star-obligation {W = W★} Anv z∈A body★
      premiseΛ =
        CTI2.Λ⊑² Anv z∈A lift★ vV U⊢★ premise★ q★
    build
      (target-strip★ᴸ-paired refl V≡ γᵒᴸ liftᵒ source∈ᵒ
        target∈ᵒ boundaryᵒ residualᵒ monoᵐ sameᵐ
        premiseᵐ reemit) =
      ⊥-elim (nonvar-var-⊥ Anv)
tag-dispatch-at★ (sv-Λ sv) vN mono rb sc source∈
    D@(CTI2.Λ⊑²-smart-comma Anv z∈A liftW liftγ vV target⊢ prem q) =
  tagged-seal-source-fold-⊥ (sv-Λ sv) nonvar-all nonstar-∀ D
tag-dispatch-at★ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {V = V ⟨ c ⟩} {N = N} {A = ★}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = q}
    (sv-cast sv inj) vN mono rb sc source∈
    (CTI2.cast⊑² .c prem .q) =
  dispatch-source-fold resume
  where
  resume : ∀ {U S}
    → N ≡ U ↓ seal Y S
    → Value U
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → TargetStripAt★Data Wᵒ γᵒ (V ⟨ c ⟩) ★ U Xᴸ Y S cY
        Wᵖ γᵖ q
  resume refl vU target∈
      with tag-dispatch-at★ sv (vU ↓ seal) mono rb sc source∈ prem
  resume refl vU target∈
      | branch
      with target-strip★-from-dispatch-case sv vU mono rb sc source∈
        target∈ prem branch
  resume refl vU target∈
      | branch
      | target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
          target∈★ q★ premise★ reemit =
    target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
      target∈★ ★⊑★ (CTI2.cast⊑² c premise★ ★⊑★)
      (λ _ → CTI2.cast⊑² c (reemit premise★) q)
  resume {U = U} {S = S} refl vU target∈
      | branch
      | target-strip★-paired source∈ᵒ target∈ᵒ boundaryᵒ
          residualᵒ monoᵐ sameᵐ premiseᵐ reemit
      with target-star-terminal-entry source∈ rb
  resume {U = U} {S = S} refl vU target∈
      | branch
      | target-strip★-paired source∈ᵒ target∈ᵒ boundaryᵒ
          residualᵒ monoᵐ sameᵐ premiseᵐ reemit
      | Y★ , target∈★ =
    target-strip★-data ((U ↓ seal Y S) ⟨ cY ⟩) Y★ Wᵖ γᵖ
      mono sc rb target∈★ ★⊑★
      (CTI2.cast⊑² c (reemit residualᵒ) ★⊑★)
      (λ _ → CTI2.cast⊑² c (reemit residualᵒ) q)
tag-dispatch-at★ (sv-cast sv fun) vN mono rb sc source∈
    D@(CTI2.cast⊑² c prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv fun) nonvar-fun nonstar-⇒ D
tag-dispatch-at★ (sv-cast sv all) vN mono rb sc source∈
    D@(CTI2.cast⊑² c prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv all) nonvar-all nonstar-∀ D
tag-dispatch-at★ (sv-cast sv (genᵥ A≢★ safe)) vN mono rb sc source∈
    D@(CTI2.cast⊑² c prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv (genᵥ A≢★ safe))
    nonvar-all nonstar-∀ D
tag-dispatch-at★ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {V = V ⟨ c ⟩} {N = N} {A = ★}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = q}
    (sv-cast sv inj) vN mono rb sc source∈
    (CTI2.cast⊑cast² {p = r} .c cY′ prem .q) =
  dispatch-source-fold resume
  where
  resume : ∀ {U S}
    → N ≡ U ↓ seal Y S
    → Value U
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → TargetStripAt★Data Wᵒ γᵒ (V ⟨ c ⟩) ★ U Xᴸ Y S cY
        Wᵖ γᵖ q
  resume refl vU target∈
      with seal-descent-at-var sv vU mono rb sc source∈ target∈ prem
  resume refl vU target∈
      | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★
          boundary★ target∈★ q★ premise★ =
    target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★
      target∈★ ★⊑★ (CTI2.cast⊑² c premise★ ★⊑★)
      (λ _ → CTI2.cast⊑cast² c cY′ prem q)
  resume {U = U} {S = S} refl vU target∈
      | target-seal-terminus-paired source∈ᵒ target∈ᵒ
          boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ
      with target-star-terminal-entry source∈ᵒ
        (CTX.sameWorldRebaseAt
          (CTX.RebaseAt.pivotAligned boundaryᵒ)
          (CTX.RebaseAt.storeRepresentations boundaryᵒ))
  resume {U = U} {S = S} refl vU target∈
      | target-seal-terminus-paired source∈ᵒ target∈ᵒ
          boundaryᵒ residualᵒ monoᵐ sameᵐ premiseᵐ
      | Y★ , target∈★ =
    target-strip★-data ((U ↓ seal Y S) ⟨ cY′ ⟩) Y★ Wᵒ γᵒ
      CTX.impEnvMono-refl sameCtx-refl
      (CTX.sameWorldRebaseAt
        (CTX.RebaseAt.pivotAligned boundaryᵒ)
        (CTX.RebaseAt.storeRepresentations boundaryᵒ))
      target∈★ ★⊑★ (CTI2.cast⊑cast² c cY′ residualᵒ ★⊑★)
      (λ _ → CTI2.cast⊑cast² c cY′ prem q)
tag-dispatch-at★ (sv-cast sv fun) vN mono rb sc source∈
    D@(CTI2.cast⊑cast² c c′ prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv fun) nonvar-fun nonstar-⇒ D
tag-dispatch-at★ (sv-cast sv all) vN mono rb sc source∈
    D@(CTI2.cast⊑cast² c c′ prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv all) nonvar-all nonstar-∀ D
tag-dispatch-at★ (sv-cast sv (genᵥ A≢★ safe)) vN mono rb sc source∈
    D@(CTI2.cast⊑cast² c c′ prem q) =
  tagged-seal-source-fold-⊥ (sv-cast sv (genᵥ A≢★ safe))
    nonvar-all nonstar-∀ D
tag-dispatch-at★ (sv-seal sv) vN mono rb sc source∈
    (CTI2.conceal⊑-neutral² (Conv.⊢↓-seal source∈′) () prem q)
tag-dispatch-at★ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {V = V ↓ seal X ★} {N = N}
    {A = ＇ X} {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = q}
    (sv-seal sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented
      prem .q) =
  dispatch-source-fold resume
  where
  resume : ∀ {U S}
    → N ≡ U ↓ seal Y S
    → Value U
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → TargetStripAt★Data Wᵒ γᵒ (V ↓ seal X ★) (＇ X)
        U Xᴸ Y S cY Wᵖ γᵖ q
  resume {S = S} refl vU target∈
      with target-star-terminal-entry source∈ rb
  resume {U = U} {S = S} refl vU target∈ | Y★ , target∈★ =
    target-strip★-data ((U ↓ seal Y S) ⟨ cY ⟩) Y★ Wᵖ γᵖ
      mono sc rb target∈★ q D (λ _ → D)
tag-dispatch-at★ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {V = V ↓ seal X R} {N = N}
    {A = ＇ X} {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = q}
    (sv-seal sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented
      prem .q) =
  dispatch-source-fold resume
  where
  resume : ∀ {U S}
    → N ≡ U ↓ seal Y S
    → Value U
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → TargetStripAt★Data Wᵒ γᵒ (V ↓ seal X R) (＇ X)
        U Xᴸ Y S cY Wᵖ γᵖ q
  resume {S = S} refl vU target∈
      with target-star-terminal-entry source∈ rb
  resume {U = U} {S = S} refl vU target∈ | Y★ , target∈★ =
    target-strip★-data ((U ↓ seal Y S) ⟨ cY ⟩) Y★ Wᵖ γᵖ
      mono sc rb target∈★ q D (λ _ → D)
tag-dispatch-at★ (sv-reveal-fun sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑-neutral² c⊢ pos≡absent prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-fun sv) nonvar-fun
    nonstar-⇒ D
tag-dispatch-at★ (sv-reveal-fun sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-fun sv) nonvar-fun
    nonstar-⇒ D
tag-dispatch-at★ (sv-reveal-fun sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-fun sv) nonvar-fun
    nonstar-⇒ D
tag-dispatch-at★ (sv-conceal-fun sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑-neutral² c⊢ pos≡absent prem q) =
  tagged-seal-source-fold-⊥ (sv-conceal-fun sv) nonvar-fun
    nonstar-⇒ D
tag-dispatch-at★ (sv-conceal-fun sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented prem q) =
  tagged-seal-source-fold-⊥ (sv-conceal-fun sv) nonvar-fun
    nonstar-⇒ D
tag-dispatch-at★ (sv-reveal-all sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑-neutral² c⊢ pos≡absent prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-all sv) nonvar-all
    nonstar-∀ D
tag-dispatch-at★ (sv-reveal-all sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑-only² c⊢ pos≢absent mark disaligned represented
      prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-all sv) nonvar-all
    nonstar-∀ D
tag-dispatch-at★ (sv-reveal-all sv) vN mono rb sc source∈
    D@(CTI2.reveal⊑² c⊢ pos≢absent Y∈ represented mono₁ rb₁ sc₁
      prem q) =
  tagged-seal-source-fold-⊥ (sv-reveal-all sv) nonvar-all
    nonstar-∀ D
tag-dispatch-at★ (sv-conceal-all sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑-neutral² c⊢ pos≡absent prem q) =
  tagged-seal-source-fold-⊥ (sv-conceal-all sv) nonvar-all
    nonstar-∀ D
tag-dispatch-at★ (sv-conceal-all sv) vN mono rb sc source∈
    D@(CTI2.conceal⊑² c⊢ pos≢absent mark disaligned represented prem q) =
  tagged-seal-source-fold-⊥ (sv-conceal-all sv) nonvar-all
    nonstar-∀ D

tag-dispatch-at★ᴸ : TagDispatchAt★ᴸ
tag-dispatch-at★ᴸ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {γᵇ = γᵇ} {V = V} {N = N} {A = A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p}
    sv vN mono rb sc source∈ liftγ D
    with liftCtxᴸ-canonical γᵒ
tag-dispatch-at★ᴸ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {γᵇ = γᵇ} {V = V} {N = N} {A = A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p}
    sv vN mono rb sc source∈ liftγ D
    | γᵒᴸ , liftᵒ
    with tag-dispatch-at★
      {Wᵒ = CTX.liftWorldLeft Wᵒ}
      {Wᵖ = CTX.liftWorldLeft Wᵖ}
      {γᵒ = γᵒᴸ}
      {γᵖ = γᵇ}
      {V = V}
      {N = N}
      {A = A}
      {Xᴸ = Fin.suc Xᴸ}
      {Y = Y}
      {cY = cY}
      {p = p}
      sv vN
      (liftImpEnvMonoLeft {W = Wᵒ} {W′ = Wᵖ} mono)
      (liftRebaseAtLeft {W = Wᵖ} {W′ = Wᵒ} rb)
      (sameCtx-liftᴸ sc liftᵒ liftγ)
      (S-lift∋ source∈ refl)
      D
tag-dispatch-at★ᴸ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {γᵇ = γᵇ} {V = V} {N = N} {A = A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p}
    sv vN mono rb sc source∈ liftγ D
    | γᵒᴸ , liftᵒ | dispatch-tag (tag-node★ r prem) =
  dispatch-tagᴸ (tag-node★ᴸ r prem)
tag-dispatch-at★ᴸ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {γᵇ = γᵇ} {V = V} {N = N} {A = A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p}
    sv vN mono rb sc source∈ liftγ D
    | γᵒᴸ , liftᵒ | dispatch-source-fold resume =
  dispatch-source-foldᴸ λ eq vU target∈ →
    source-binder-strengthen-strip {γᵖ = γᵖ} liftᵒ
      (resume eq vU target∈)
tag-dispatch-at★ᴸ {Wᵒ = Wᵒ} {Wᵖ = Wᵖ} {γᵒ = γᵒ}
    {γᵖ = γᵖ} {γᵇ = γᵇ} {V = V} {N = N} {A = A}
    {Xᴸ = Xᴸ} {Y = Y} {cY = cY} {p = p}
    sv vN mono rb sc source∈ liftγ D
    | γᵒᴸ , liftᵒ | dispatch-nonvar-empty bad =
  dispatch-nonvar-emptyᴸ bad

target-strip-at★ : TargetStripAt★
target-strip-at★ =
  target-strip★-from-slices seal-descent-at-var tag-dispatch-at★

target-strip-at★ᴸ : TargetStripAt★ᴸ
target-strip-at★ᴸ =
  target-strip★ᴸ-from-slices seal-descent-at-varᴸ tag-dispatch-at★ᴸ
