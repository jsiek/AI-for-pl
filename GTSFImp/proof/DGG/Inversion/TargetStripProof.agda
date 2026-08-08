module proof.DGG.Inversion.TargetStripProof where

-- File Charter:
--   * Provides the sliced target-tag-at-star strip members used by source
--     stripping.
--   * Keeps any remaining proof debt aligned with the validated target-seal
--     and target-tag slice surfaces.
--   * Derives the old compound strip inhabitants from those slices.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using
  (TyStore; store-lift; _∋_⦂_; Z∋; S-lift∋; S-bind∋)
open import Consistency using (toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _⦂∀_[_]; _↓_)
open import Imprecision
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealTransferCore as STC
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   TargetSealTerminusData; target-seal-terminus-data;
   TargetSealTerminusᴸData; TargetStripAt★Data; target-strip★-data;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-cast; sv-seal; var-value-view; varv-seal)
open import proof.DGG.Inversion.TargetDescentLemma using
  (composeSamePivotRebase; inner-source-pivot-eqᴿ)
open import proof.DGG.Inversion.TargetWalkSupport using
  (impEnvMono-∘; liftWorldLeft-⊑ᵂ; rebase-source-membership;
   rebase-target-membership; sameCtx-∘;
   seal-target-nonstar-⊥; star-source-nonstar-⊥; store-lookup-unique;
   target-seal-rebase-source)

open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   impEnvʷ; ηᴸʷ; ηᴿʷ; sourceStoreʷ; targetStoreʷ)

private
  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Z : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Z ⦂ S
    → targetStoreʷ W′ ∋ Z ⦂ S
  rebase-target-membership-forward rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Z∈

  rebase-target-membership-back : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Z : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W′ ∋ Z ⦂ S
    → targetStoreʷ W ∋ Z ⦂ S
  rebase-target-membership-back rb Z∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (sym (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb))) Z∈

  origin-var-obligation : ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt Wʳ Wᵒ Xᴸ Y
    → (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ＇ Y
  origin-var-obligation {Wᵒ = Wᵒ} {Xᴸ = Xᴸ} {Y = Y} rb =
    subst≡
      (λ Z → impEnvʷ Wᵒ ⊢
        ＇ (toRenameᵗ (ηᴸʷ Wᵒ) Xᴸ) ⊑ ＇ Z)
      (CTI2.RebaseAt.pivotAligned rb)
      X⊑X

  composeOuterRebase : ∀ {Δᴸ Δᴿ Δ}
      {W W′ W₂ : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    → RebaseAt W′ W X Y
    → RebaseAt W₂ W′ X Y′
    → RebaseAt W₂ W X Y
  composeOuterRebase {W = W} {W′ = W′} {W₂ = W₂}
      {X = X} {Y = Y} rb₁ rb₂ =
    CTI2.rebase-at
      (CTI2.same-runtime
        (trans (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime rb₁))
          (CTI2.SameRuntime.sourceStore-same
            (CTI2.RebaseAt.sameRuntime rb₂)))
        (trans (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime rb₁))
          (CTI2.SameRuntime.targetStore-same
            (CTI2.RebaseAt.sameRuntime rb₂))))
      source-off target-frozen (CTI2.RebaseAt.pivotAligned rb₁)
      (CTI2.RebaseAt.storeRepresentations rb₁)
    where
    source-off : ∀ {Z} → Z ≢ X
      → toRenameᵗ (ηᴸʷ W) Z ≡ toRenameᵗ (ηᴸʷ W₂) Z
    source-off Z≢X =
      trans (CTI2.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
        (CTI2.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

    target-frozen : ∀ Z
      → toRenameᵗ (ηᴿʷ W) Z ≡ toRenameᵗ (ηᴿʷ W₂) Z
    target-frozen Z =
      trans (CTI2.RebaseAt.ηᴿ-frozen rb₁ Z)
        (CTI2.RebaseAt.ηᴿ-frozen rb₂ Z)

  liftWorldLeft-shift-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B
    → ⇑ᵗ A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ B
  liftWorldLeft-shift-⊑ᵂ {W = W} {A = A} {B = B} p =
    liftWorldLeft-⊑ᵂ {W = W} {A = ⇑ᵗ A} {B = B}
      (subst≡
        (λ L → instᵐ (impEnvʷ W) ⊢ L ⊑ ⇑ᵗ (CTI2.embedᴿ W B))
        (sym (renameᵗ-shift (toRenameᵗ (ηᴸʷ W)) A))
        (rename-⊑ Fin.suc fin-suc-injective (λ _ eq → eq) p))

  liftCtxᴸ-canonical : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
    → (γ : CtxImp W)
    → Σ[ γᴸ ∈ CtxImp (CTI2.liftWorldLeft X⊑★ W) ]
        CTI2.LiftCtxᴸ X⊑★ γ γᴸ
  liftCtxᴸ-canonical {W = W} [] = [] , CTI2.liftᴸ-[]
  liftCtxᴸ-canonical {W = W} (CTI2.ctx-imp A B p ∷ γ)
      with liftCtxᴸ-canonical γ
  liftCtxᴸ-canonical {W = W} (CTI2.ctx-imp A B p ∷ γ)
      | γᴸ , liftγ =
    CTI2.ctx-imp (⇑ᵗ A) B
      (liftWorldLeft-shift-⊑ᵂ {W = W} {A = A} {B = B} p) ∷ γᴸ ,
    CTI2.liftᴸ-∷ liftγ

  sameCtx-liftᴸ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W₂ : World Δᴸ Δᴿ Δ}
      {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂}
      {γ₁ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₁)}
      {γ₂ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₂)}
    → CTI2.SameCtx γ₁ γ₂
    → CTI2.LiftCtxᴸ X⊑★ γ₁ γ₁ᴸ
    → CTI2.LiftCtxᴸ X⊑★ γ₂ γ₂ᴸ
    → CTI2.SameCtx γ₁ᴸ γ₂ᴸ
  sameCtx-liftᴸ CTI2.same-[] CTI2.liftᴸ-[] CTI2.liftᴸ-[] =
    CTI2.same-[]
  sameCtx-liftᴸ (CTI2.same-∷ sc) (CTI2.liftᴸ-∷ lift₁)
      (CTI2.liftᴸ-∷ lift₂) =
    CTI2.same-∷ (sameCtx-liftᴸ sc lift₁ lift₂)

  liftImpEnvMonoLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono W W′
    → CTI2.ImpEnvMono
        (CTI2.liftWorldLeft X⊑★ W)
        (CTI2.liftWorldLeft X⊑★ W′)
  liftImpEnvMonoLeft mono Fin.zero eq = eq
  liftImpEnvMonoLeft mono (Fin.suc Z) eq = mono Z eq

  liftRebaseAtLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt W W′ Xᴸ Y
    → RebaseAt
        (CTI2.liftWorldLeft X⊑★ W)
        (CTI2.liftWorldLeft X⊑★ W′)
        (Fin.suc Xᴸ) Y
  liftRebaseAtLeft {W = W} {W′ = W′} {Xᴸ = Xᴸ} {Y = Y} rb =
    CTI2.rebase-at
      (CTI2.same-runtime
        (cong store-lift
          (CTI2.SameRuntime.sourceStore-same
            (CTI2.RebaseAt.sameRuntime rb)))
        (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime rb)))
      source-off target-frozen
      (cong Fin.suc (CTI2.RebaseAt.pivotAligned rb))
      (CTI2.store-rep-imp
        (liftWorldLeft-shift-⊑ᵂ {W = W′}
          {A = CTI2.resolveVar (sourceStoreʷ W′) Xᴸ}
          {B = CTI2.resolveVar (targetStoreʷ W′) Y}
          (CTI2.StoreRepImp.represented
            (CTI2.RebaseAt.storeRepresentations rb))))
    where
    source-off : ∀ {Z}
      → Z ≢ Fin.suc Xᴸ
      → toRenameᵗ (ηᴸʷ (CTI2.liftWorldLeft X⊑★ W′)) Z
          ≡ toRenameᵗ (ηᴸʷ (CTI2.liftWorldLeft X⊑★ W)) Z
    source-off {Fin.zero} Z≢ = refl
    source-off {Fin.suc Z} Z≢ =
      cong Fin.suc
        (CTI2.RebaseAt.ηᴸ-off-pivot rb
          (λ eq → Z≢ (cong Fin.suc eq)))

    target-frozen : ∀ Z
      → toRenameᵗ (ηᴿʷ (CTI2.liftWorldLeft X⊑★ W′)) Z
          ≡ toRenameᵗ (ηᴿʷ (CTI2.liftWorldLeft X⊑★ W)) Z
    target-frozen Z =
      cong Fin.suc (CTI2.RebaseAt.ηᴿ-frozen rb Z)

  shift-not-zero : ∀ {Δ} {A : Ty Δ}
    → (＇ Fin.zero) ≢ ⇑ᵗ A
  shift-not-zero {A = ＇ X} ()
  shift-not-zero {A = ‵ ι} ()
  shift-not-zero {A = ★} ()
  shift-not-zero {A = A ⇒ B} ()
  shift-not-zero {A = `∀ A} ()

  resolveVar-var : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    → Σ ∋ X ⦂ (＇ Y)
    → CTI2.resolveVar Σ X ≡ CTI2.resolveVar Σ Y
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
    → CTI2.resolveVar Σ X ≡ S
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
          (λ T → T ⊑ᵂ⟨ W ⟩ CTI2.resolveVar (targetStoreʷ W) Y)
          (SPT.resolveVar-nonvar source∈ nonvar-star)
          (CTI2.StoreRepImp.represented
            (CTI2.RebaseAt.storeRepresentations rb))))
      Sns

postulate
  seal-descent-at-varᴸ : SealDescentAtVarᴸ
  tag-dispatch-at★ : TagDispatchAt★
  tag-dispatch-at★ᴸ : TagDispatchAt★ᴸ

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
seal-descent-current-star {U = U} {Y = Y} sv vU source∈ target∈ D
    with STC.seal-transfer sv vU D
seal-descent-current-star {U = U} {Y = Y} sv vU source∈ target∈ D
    | W★ , γ★ , link , mono★ , same★ , q★ , premise★ =
  target-seal-terminus-data U Y W★ γ★ mono★ same★ link
    (rebase-target-membership-forward link target∈) q★ premise★

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
seal-descent-current-var {Y = Y} (sv-seal sv₀) vU
    source∈ target∈
    (CTI2.conceal⊑² {W′ = Wᵖ} {p = p} mono rb sc
      (CTI2.⊢↓-sealˣ source∈′) prem r) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y)
        (store-lookup-unique source∈′ source∈) p)
      nonstar-X)
seal-descent-current-var {Y′ = Y′} (sv-seal sv₀) vU
    source∈ target∈
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p} mono rb sc
      (CTI2.⊢↓-sealˣ source∈′) target⊢ prem r) =
  ⊥-elim
    (star-source-nonstar-⊥ {W = Wᵖ} {S = ＇ Y′}
      (subst≡ (λ T → T ⊑ᵂ⟨ Wᵖ ⟩ ＇ Y′)
        (store-lookup-unique source∈′ source∈) p)
      nonstar-X)
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    with target-seal-rebase-source rbᴿ r
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    | link
    with var-value-view vU (CTI2T.target-typing² prem)
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    | link | varv-seal {W = U₀} {R = ★} vU₀ target′∈ refl
    with seal-descent-current-star sv vU₀
      (rebase-source-membership link source∈) target′∈ prem
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    | link | varv-seal {W = U₀} {R = ★} vU₀ target′∈ refl
    | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★
        boundary★ target∈★ q★ premise★ =
  target-seal-terminus-data U★ Y★ W★ γ★
    (impEnvMono-∘ {W₁ = W} {W₂ = Wᵈ} {W₃ = W★} mono mono★)
    (sameCtx-∘ sc same★)
    (composeOuterRebase link boundary★)
    target∈★ q★ premise★
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    | link | varv-seal {W = U₀} {R = ＇ Y₂} vU₀ target′∈ refl
    with seal-descent-current-var sv vU₀
      (rebase-source-membership link source∈) target′∈ prem
seal-descent-current-var {W = W} {X = X} {Y = Y} {r = r} sv vU
    source∈ target∈
    (CTI2.⊑conceal² {W′ = Wᵈ} {γ′ = γᵈ} {p = pᵈ}
      mono rbᴿ sc (CTI2.⊢↓-sealˣ target∈′) prem .r)
    | link | varv-seal {W = U₀} {R = ＇ Y₂} vU₀ target′∈ refl
    | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★
        boundary★ target∈★ q★ premise★ =
  target-seal-terminus-data U★ Y★ W★ γ★
    (impEnvMono-∘ {W₁ = W} {W₂ = Wᵈ} {W₃ = W★} mono mono★)
    (sameCtx-∘ sc same★)
    (composeOuterRebase link boundary★)
    target∈★ q★ premise★
seal-descent-current-var {Y = Y} sv vU source∈ target∈
    (CTI2.⊑conceal² {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ target∈′) prem r)
    | link | varv-seal {R = ‵ ι} vU₀ target′∈ refl =
  ⊥-elim
    (seal-target-var-nonstar-⊥ source∈ link target∈ target′∈
      nonvar-base nonstar-ι)
seal-descent-current-var {Y = Y} sv vU source∈ target∈
    (CTI2.⊑conceal² {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ target∈′) prem r)
    | link | varv-seal {R = A ⇒ B} vU₀ target′∈ refl =
  ⊥-elim
    (seal-target-var-nonstar-⊥ source∈ link target∈ target′∈
      nonvar-fun nonstar-⇒)
seal-descent-current-var {Y = Y} sv vU source∈ target∈
    (CTI2.⊑conceal² {p = pᵈ} mono rbᴿ sc
      (CTI2.⊢↓-sealˣ target∈′) prem r)
    | link | varv-seal {R = `∀ A} vU₀ target′∈ refl =
  ⊥-elim
    (seal-target-var-nonstar-⊥ source∈ link target∈ target′∈
      nonvar-all nonstar-∀)

seal-descent-at-var-＇ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γʳ : CtxImp Wʳ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {Xᴸ : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
    {r : A ⊑ᵂ⟨ Wʳ ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γʳ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ ＇ Y′
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y (＇ Y′) ∶ r
  → TargetSealTerminusData Wᵒ γᵒ V A U Xᴸ Y (＇ Y′)
seal-descent-at-var-＇ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {A = A} {Xᴸ = Xᴸ}
    {Y = Y} {r = r} sv vU mono rb sc source∈ target∈ D
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var-＇ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} {r = r} sv vU mono rb sc source∈ target∈ D
    | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ rb r
seal-descent-at-var-＇ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} sv vU mono rb sc source∈ target∈ D
    | .Xᴸ , refl , aligned | refl
    with seal-descent-current-var sv vU
      (rebase-source-membership rb source∈)
      (rebase-target-membership-forward rb target∈) D
seal-descent-at-var-＇ {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {Xᴸ = Xᴸ}
    {Y = Y} sv vU mono rb sc source∈ target∈ D
    | .Xᴸ , refl , aligned | refl
    | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★
        boundary★ target∈★ q★ premise★ =
  target-seal-terminus-data U★ Y★ W★ γ★
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = W★} mono mono★)
    (sameCtx-∘ sc same★)
    (composeOuterRebase rb boundary★)
    target∈★ q★ premise★

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
  → CTI2.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γʳ
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
    with STC.seal-transfer sv vU D
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} sv vU mono rb sc source∈ target∈ D
    | .Xᴸ , refl , aligned | refl
    | W★ , γ★ , link , mono★ʳ , same★ʳ , q★ , premise★ =
  target-seal-terminus-data U Y W★ γ★
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = W★}
      mono mono★ʳ)
    (sameCtx-∘ sc same★ʳ)
    (composeSamePivotRebase rb link)
    (rebase-target-membership-forward (composeSamePivotRebase rb link)
      target∈)
    q★ premise★
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

target-strip-at★ : TargetStripAt★
target-strip-at★ =
  target-strip★-from-slices seal-descent-at-var tag-dispatch-at★

target-strip-at★ᴸ : TargetStripAt★ᴸ
target-strip-at★ᴸ =
  target-strip★ᴸ-from-slices seal-descent-at-varᴸ tag-dispatch-at★ᴸ
