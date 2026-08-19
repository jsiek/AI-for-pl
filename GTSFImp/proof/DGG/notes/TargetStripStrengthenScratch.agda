module TargetStripStrengthenScratch where

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_; S-lift∋)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using
  (Term; Value; _↓_; _⊢_⦂_; ⟨_,_,_⟩; seal)
open import Imprecision
import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision2 as CTIR
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.SealTransferCore as STC
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open import proof.DGG.Inversion.TargetDescentLemma using
  (composeSamePivotRebase; inner-source-pivot-eqᴿ)
open import proof.DGG.Inversion.TargetStripDef using
  (SealDescentAtVarᴸ; TargetSealTerminusᴸData;
   target-seal-terminusᴸ-data)
open import proof.DGG.Inversion.TargetWalkSupport using
  (impEnvMono-∘; rebase-target-membership; sameCtx-∘)

open CTI2 using
  (World;
   CtxImp;
   RebaseAt;
   LiftCtxᴸ;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ;
   targetStoreʷ;
   tgtCtxʷ)
open CTIR using (_∣_⊢²_⊑_∶_)

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

record LoweredLiftSealTerminal {Δᴸ Δᴿ Δ}
    (W₁ : World Δᴸ Δᴿ Δ) (γ₁ : CtxImp W₁)
    (γ₁ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₁))
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (U : Term Δᴿ) (X : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where
  constructor lowered-lift-seal-terminal
  field
    U★ : Term Δᴿ
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    γ★ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W★)
    lift★ : LiftCtxᴸ X⊑★ γ★ γ★ᴸ
    mono★ : CTI2.ImpEnvMono W₁ W★
    same★ : CTI2.SameCtx γ₁ γ★
    boundary★ : RebaseAt W★ W₁ X Y
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W★ ⟩ ★
    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , tgtCtxʷ γ★ ⟩ ⊢ U★ ⦂ ★
    premise★ :
      CTI2.liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U★ ∶ q★

postulate
  liftCtxᴸ-canonical : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
    → (γ : CtxImp W)
    → Σ[ γᴸ ∈ CtxImp (CTI2.liftWorldLeft X⊑★ W) ]
        LiftCtxᴸ X⊑★ γ γᴸ

  sameCtx-liftᴸ : ∀ {Δᴸ Δᴿ Δ}
      {W₁ W₂ : World Δᴸ Δᴿ Δ}
      {γ₁ : CtxImp W₁} {γ₂ : CtxImp W₂}
      {γ₁ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₁)}
      {γ₂ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₂)}
    → CTI2.SameCtx γ₁ γ₂
    → LiftCtxᴸ X⊑★ γ₁ γ₁ᴸ
    → LiftCtxᴸ X⊑★ γ₂ γ₂ᴸ
    → CTI2.SameCtx γ₁ᴸ γ₂ᴸ

  liftImpEnvMonoLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
    → CTI2.ImpEnvMono W W′
    → CTI2.ImpEnvMono
        (CTI2.liftWorldLeft X⊑★ W)
        (CTI2.liftWorldLeft X⊑★ W′)

  liftRebaseAtLeft : ∀ {Δᴸ Δᴿ Δ}
      {W W′ : World Δᴸ Δᴿ Δ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    → RebaseAt W W′ Xᴸ Y
    → RebaseAt
        (CTI2.liftWorldLeft X⊑★ W)
        (CTI2.liftWorldLeft X⊑★ W′)
        (Fin.suc Xᴸ) Y

  source-binder-strengthen-seal-transfer : ∀ {Δᴸ Δᴿ Δ}
      {W₁ : World Δᴸ Δᴿ Δ}
      {γ₁ : CtxImp W₁}
      {γ₁ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W₁)}
      {V : Term (suc Δᴸ)} {U : Term Δᴿ}
      {A : Ty (suc Δᴸ)}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {r : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W₁ ⟩ ＇ Y}
    → LiftCtxᴸ X⊑★ γ₁ γ₁ᴸ
    → SpineValue V
    → Value U
    → CTI2.liftWorldLeft X⊑★ W₁ ∣ γ₁ᴸ ⊢²
        V ⊑ U ↓ seal Y ★ ∶ r
    → LoweredLiftSealTerminal W₁ γ₁ γ₁ᴸ V A U X Y

  seal-descent-at-varᴸ-nonstar-scratch : SealDescentAtVarᴸ

seal-descent-at-varᴸ-scratch : SealDescentAtVarᴸ
seal-descent-at-varᴸ-scratch {Wᵒ = Wᵒ} {Wʳ = Wʳ}
    {γᵒ = γᵒ} {γʳ = γʳ} {γᵇ = γᵇ} {V = V}
    {U = U} {A = A} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} sv vU mono rb sc source∈ target∈ liftγ D
    with liftCtxᴸ-canonical γᵒ
seal-descent-at-varᴸ-scratch {Wᵒ = Wᵒ} {Wʳ = Wʳ}
    {γᵒ = γᵒ} {γʳ = γʳ} {γᵇ = γᵇ} {V = V}
    {U = U} {A = A} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} sv vU mono rb sc source∈ target∈ liftγ D
    | γᵒᴸ , liftᵒ
    with SPT.right-var-obligation-view
      {W = CTI2.liftWorldLeft X⊑★ Wʳ} {R = A} {Y = Y} r
seal-descent-at-varᴸ-scratch {Wᵒ = Wᵒ} {Wʳ = Wʳ}
    {γᵒ = γᵒ} {γʳ = γʳ} {γᵇ = γᵇ} {V = V}
    {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
    {r = r} sv vU mono rb sc source∈ target∈ liftγ D
    | γᵒᴸ , liftᵒ | X₂ , refl , aligned
    with inner-source-pivot-eqᴿ (liftRebaseAtLeft rb) r
seal-descent-at-varᴸ-scratch {Wᵒ = Wᵒ} {Wʳ = Wʳ}
    {γᵒ = γᵒ} {γʳ = γʳ} {γᵇ = γᵇ} {V = V}
    {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
    sv vU mono rb sc source∈ target∈ liftγ D
    | γᵒᴸ , liftᵒ | .(Fin.suc Xᴸ) , refl , aligned | refl
    with source-binder-strengthen-seal-transfer liftγ sv vU D
seal-descent-at-varᴸ-scratch {Wᵒ = Wᵒ} {Wʳ = Wʳ}
    {γᵒ = γᵒ} {γʳ = γʳ} {γᵇ = γᵇ} {V = V}
    {U = U} {S = ★} {Xᴸ = Xᴸ} {Y = Y}
    sv vU mono rb sc source∈ target∈ liftγ D
    | γᵒᴸ , liftᵒ | .(Fin.suc Xᴸ) , refl , aligned | refl
    | lowered-lift-seal-terminal U★ Y★ W★ γ★ γ★ᴸ lift★
        mono★ʳ same★ʳ boundary★ target∈★ q★ U⊢★ premise★ =
  target-seal-terminusᴸ-data U★ Y★ W★ γ★ γᵒᴸ γ★ᴸ liftᵒ lift★
    (impEnvMono-∘ {W₁ = Wᵒ} {W₂ = Wʳ} {W₃ = W★}
      mono mono★ʳ)
    (sameCtx-∘ sc same★ʳ)
    (composeSamePivotRebase rb boundary★)
    target∈★
    q★ U⊢★ premise★
seal-descent-at-varᴸ-scratch {S = ＇ Y′} sv vU mono rb sc source∈
    target∈ liftγ D =
  seal-descent-at-varᴸ-nonstar-scratch sv vU mono rb sc source∈
    target∈ liftγ D
seal-descent-at-varᴸ-scratch {S = ‵ ι} sv vU mono rb sc source∈
    target∈ liftγ D =
  seal-descent-at-varᴸ-nonstar-scratch sv vU mono rb sc source∈
    target∈ liftγ D
seal-descent-at-varᴸ-scratch {S = A ⇒ B} sv vU mono rb sc source∈
    target∈ liftγ D =
  seal-descent-at-varᴸ-nonstar-scratch sv vU mono rb sc source∈
    target∈ liftγ D
seal-descent-at-varᴸ-scratch {S = `∀ S} sv vU mono rb sc source∈
    target∈ liftγ D =
  seal-descent-at-varᴸ-nonstar-scratch sv vU mono rb sc source∈
    target∈ liftγ D
