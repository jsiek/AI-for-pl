module proof.DGG.Inversion.TargetStripProof where

-- File Charter:
--   * Provides the sliced target-tag-at-star strip members used by source
--     stripping.
--   * Keeps any remaining proof debt aligned with the validated target-seal
--     and target-tag slice surfaces.
--   * Derives the old compound strip inhabitants from those slices.

open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _↓_)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealTransferCore as STC
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVar; SealDescentAtVarᴸ; TagDispatchAt★;
   TagDispatchAt★ᴸ; TargetStripAt★; TargetStripAt★ᴸ;
   TargetStripAt★Data; target-strip★-data;
   target-strip★-from-slices; target-strip★ᴸ-from-slices)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.DGG.Inversion.TargetDescentLemma using
  (composeSamePivotRebase; inner-source-pivot-eqᴿ)
open import proof.DGG.Inversion.TargetWalkSupport using
  (impEnvMono-∘; sameCtx-∘)

open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   targetStoreʷ)

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

postulate
  seal-descent-at-varᴸ : SealDescentAtVarᴸ
  tag-dispatch-at★ : TagDispatchAt★
  tag-dispatch-at★ᴸ : TagDispatchAt★ᴸ

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
    → targetStoreʷ Wᵒ ∋ Y ⦂ ＇ Y′
    → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y (＇ Y′) ∶ r
    → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ

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
    → targetStoreʷ Wᵒ ∋ Y ⦂ S
    → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
    → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ

seal-descent-at-var : SealDescentAtVar
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {A = A} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc target∈ D
    with SPT.right-var-obligation-view {W = Wʳ} {R = A} {Y = Y} r
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc target∈ D
    | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ rb r
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} {r = r} sv vU mono rb sc target∈ D
    | .Xᴸ , refl , aligned | refl
    with STC.seal-transfer sv vU D
seal-descent-at-var {Wᵒ = Wᵒ} {Wʳ = Wʳ} {γᵒ = γᵒ}
    {γʳ = γʳ} {V = V} {U = U} {S = ★}
    {Xᴸ = Xᴸ} {Y = Y} sv vU mono rb sc target∈ D
    | .Xᴸ , refl , aligned | refl
    | W★ , γ★ , link , mono★ʳ , same★ʳ , q★ , premise★ =
  target-strip★-data Y W★ γ★
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = W★}
      mono mono★ʳ)
    (sameCtx-∘ sc same★ʳ)
    (composeSamePivotRebase rb link)
    (rebase-target-membership-forward (composeSamePivotRebase rb link)
      target∈)
    q★ premise★
seal-descent-at-var {S = ＇ Y′} sv vU mono rb sc target∈ D =
  seal-descent-at-var-＇ sv vU mono rb sc target∈ D
seal-descent-at-var {S = ‵ ι} sv vU mono rb sc target∈ D =
  seal-descent-at-var-nonvar nonvar-base nonstar-ι
    sv vU mono rb sc target∈ D
seal-descent-at-var {S = S ⇒ T} sv vU mono rb sc target∈ D =
  seal-descent-at-var-nonvar nonvar-fun nonstar-⇒
    sv vU mono rb sc target∈ D
seal-descent-at-var {S = `∀ S} sv vU mono rb sc target∈ D =
  seal-descent-at-var-nonvar nonvar-all nonstar-∀
    sv vU mono rb sc target∈ D

target-strip-at★ : TargetStripAt★
target-strip-at★ =
  target-strip★-from-slices seal-descent-at-var tag-dispatch-at★

target-strip-at★ᴸ : TargetStripAt★ᴸ
target-strip-at★ᴸ =
  target-strip★ᴸ-from-slices seal-descent-at-varᴸ tag-dispatch-at★ᴸ
