module proof.DGG.Catchup.InstInversionProof where

-- File Charter:
--   * Proves support lemmas for the M5 target-instantiation inversion
--     packages.
--   * Starts with residual `CatchupCast⁻` provenance for the Λ package.
--   * Imports only the live Def surface plus core/proof-only consistency
--     support; it does not consume other catch-up Proof modules.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
import Data.List as List
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (n<1+n)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; id; _↦_; ∀ᶜ_; _!; ？_; inst_; gen_;
   bot-elim; bot-intro; instᵐ; ↑ᶜ_; close-instᶜ; renameNonStar;
   _↪ᵗ_; keep; skip; toRenameᵗ; wk↪ᵗ)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)
open import Reduction using
  (StoreChanges; _—↠[_]_; bind; _∷_; []; ↠-refl; ↠-step;
   applyStores; applyTys)
import CastTerms as CT
open import CastTerms using (_⟨_⟩)
open import proof.Consistency using (gen-safe)
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; nonstar-from-≢★; rename-⊑)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; _++χ_; FuelStepSurface; Catchup⁻Embedᵀ;
   catchup⁻-inert; catchup⁻-id; catchup⁻-inst;
   catchup⁻-bot-elim; catchup⁻-bot-intro)
open import proof.DGG.Catchup.InstInversionDef using
  (Catchup⁻NonStarᵀ; InstPostCatalogPackage;
   InstPostCatalogPackageAt; InstResidualProvenanceᵀ;
   InstSpineDescentPackage; Λ⊑²AtRewrapᵀ;
   Λ⊑²CPSRewrapᵀ; MapCtxᴿLiftᴸᵀ; RightBindUnderLeftLiftᵀ)


inst-post-at→package : ∀ {fuel Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ Δᴿ₂ Δ₂}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {M′ : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {χs₂ : StoreChanges Δᴿ Δᴿ₂}
  → (rel : W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p)
  → (vM : CT.Value M)
  → (vM′ : CT.Value M′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂)
  → (Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ CTI2.World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ CT.Term Δᴿ′ ]
        (CT.Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ CTI2.∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              ECR.transport⊑ᵂ ext q)))
  → InstPostCatalogPackageAt fuel rel vM vM′ c′ B′≢★
      c<fuel q χs₂ W₂ ext₂
  → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q
inst-post-at→package rel vM vM′ c′ B′≢★ c<fuel q ext₂
    finish pkg =
  record
    { Δᴿ₂ = _
    ; χs₂ = _
    ; Δ₂ = _
    ; W₂ = _
    ; ext₂ = ext₂
    ; B₂ = InstPostCatalogPackageAt.at-B₂ pkg
    ; post = InstPostCatalogPackageAt.at-post pkg
    ; p₂ = InstPostCatalogPackageAt.at-p₂ pkg
    ; post-relation =
        InstPostCatalogPackageAt.at-post-relation pkg
    ; ν₂ = InstPostCatalogPackageAt.at-ν₂ pkg
    ; residual-cast =
        InstPostCatalogPackageAt.at-residual-cast pkg
    ; residual-provenance =
        InstPostCatalogPackageAt.at-residual-provenance pkg
    ; spine-descent =
        InstPostCatalogPackageAt.at-spine-descent pkg
    ; finish = finish
    }


applyStores-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ Σ
  → applyStores ψs (applyStores χs Σ) ≡ applyStores (χs ++χ ψs) Σ
applyStores-++ [] ψs Σ = refl
applyStores-++ (χ ∷ χs) ψs Σ =
  applyStores-++ χs ψs _


applyTys-++ : ∀ {Δ₀ Δ₁ Δ₂}
  → (χs : StoreChanges Δ₀ Δ₁)
  → (ψs : StoreChanges Δ₁ Δ₂)
  → ∀ A
  → applyTys ψs (applyTys χs A) ≡ applyTys (χs ++χ ψs) A
applyTys-++ [] ψs A = refl
applyTys-++ (χ ∷ χs) ψs A = applyTys-++ χs ψs _


composeWorldExtendᴿ : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
  → ECR.WorldExtendᴿ χs W₀ W₁
  → ECR.WorldExtendᴿ ψs W₁ W₂
  → ECR.WorldExtendᴿ (χs ++χ ψs) W₀ W₂
composeWorldExtendᴿ {χs = χs} {ψs = ψs} {W₀ = W₀} {W₂ = W₂}
    ext₁ ext₂ =
  record
    { sourceStore-kept =
        trans (ECR.sourceStore-kept ext₂) (ECR.sourceStore-kept ext₁)
    ; targetStore-follows =
        trans (ECR.targetStore-follows ext₂)
          (trans
            (cong (applyStores ψs) (ECR.targetStore-follows ext₁))
            (applyStores-++ χs ψs (CTI2.targetStoreʷ W₀)))
    ; transport⊑ᵂ = λ {A = A} {C = C} p →
        subst≡ (λ C′ → A CTI2.⊑ᵂ⟨ W₂ ⟩ C′)
          (applyTys-++ χs ψs C)
          (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p))
    }


ctx-imp-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A CTI2.⊑ᵂ⟨ W ⟩ B)
  → CTI2.ctx-imp {W = W} A B p ≡
    CTI2.ctx-imp {W = W} A B′
      (subst≡ (λ C → A CTI2.⊑ᵂ⟨ W ⟩ C) eq p)
ctx-imp-transportᴿ refl p = refl


mapCtxᴿ-compose : ∀ {Δᴸ Δ₀ Δ₁ Δ₂ Δ Δ₁ᵂ Δ₂ᵂ}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {W₀ : CTI2.World Δᴸ Δ₀ Δ}
    {W₁ : CTI2.World Δᴸ Δ₁ Δ₁ᵂ}
    {W₂ : CTI2.World Δᴸ Δ₂ Δ₂ᵂ}
    (ext₁ : ECR.WorldExtendᴿ χs W₀ W₁)
    (ext₂ : ECR.WorldExtendᴿ ψs W₁ W₂)
    (γ : CTI2.CtxImp W₀)
  → ECR.mapCtxᴿ ext₂ (ECR.mapCtxᴿ ext₁ γ) ≡
    ECR.mapCtxᴿ (composeWorldExtendᴿ ext₁ ext₂) γ
mapCtxᴿ-compose ext₁ ext₂ List.[] = refl
mapCtxᴿ-compose {χs = χs} {ψs = ψs} {W₂ = W₂} ext₁ ext₂
    (CTI2.ctx-imp A B p List.∷ γ) =
  cong₂ List._∷_
    (ctx-imp-transportᴿ {W = W₂} (applyTys-++ χs ψs B)
      (ECR.transport⊑ᵂ ext₂ (ECR.transport⊑ᵂ ext₁ p)))
    (mapCtxᴿ-compose ext₁ ext₂ γ)


composeReduction : ∀ {Δ₀ Δ₁ Δ₂}
    {χs : StoreChanges Δ₀ Δ₁} {ψs : StoreChanges Δ₁ Δ₂}
    {M : CT.Term Δ₀} {N : CT.Term Δ₁} {P : CT.Term Δ₂}
  → M —↠[ χs ] N
  → N —↠[ ψs ] P
  → M —↠[ χs ++χ ψs ] P
composeReduction ↠-refl N↠P = N↠P
composeReduction (↠-step M→N N↠P) P↠Q =
  ↠-step M→N (composeReduction N↠P P↠Q)


rel-target-transportᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {N : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ}
  → (eq : B ≡ B′)
  → (p : A CTI2.⊑ᵂ⟨ W ⟩ B)
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → W CTI2.∣ γ ⊢² M ⊑ N ∶
      subst≡ (λ C → A CTI2.⊑ᵂ⟨ W ⟩ C) eq p
rel-target-transportᴿ refl p rel = rel


inst-post-at-finish : ∀ {fuel Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ Δᴿ₂ Δ₂}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {M′ : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {χs₂ : StoreChanges Δᴿ Δᴿ₂}
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → (rel : W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p)
  → (vM : CT.Value M)
  → (vM′ : CT.Value M′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂)
  → (pkg : InstPostCatalogPackageAt fuel rel vM vM′ c′ B′≢★
      c<fuel q χs₂ W₂ ext₂)
  → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ CTI2.World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ CT.Term Δᴿ′ ]
        (CT.Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ CTI2.∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              ECR.transport⊑ᵂ ext q))
inst-post-at-finish {γ = γ} {B′ = B′} {χs₂ = χs₂}
    fuel-step catchup⁻-embed rel vM vM′ c′
    B′≢★ c<fuel q ext₂ pkg
    with FuelStepSurface.smaller-extra fuel-step
      (InstPostCatalogPackageAt.at-residual-fuel pkg)
      (InstPostCatalogPackageAt.at-post-relation pkg)
      vM
      (InstPostCatalogPackageAt.at-post-value pkg)
      (InstPostCatalogPackageAt.at-residual-cast pkg)
      (n<1+n (castSize
        (InstPostCatalogPackageAt.at-residual-cast pkg)))
      (ECR.transport⊑ᵂ ext₂ q)
      (catchup⁻-embed
        (InstPostCatalogPackageAt.at-post pkg)
        (InstPostCatalogPackageAt.at-residual-provenance pkg))
inst-post-at-finish {γ = γ} {B′ = B′} {χs₂ = χs₂}
    fuel-step catchup⁻-embed rel vM vM′ c′
    B′≢★ c<fuel q ext₂ pkg
  | Δᴿ′ , ψs , Δ′ , W′ , ext′ , N′ ,
    (vN′ , post↠N′ , rel′) =
  Δᴿ′ , _ , Δ′ , W′ , composeWorldExtendᴿ ext₂ ext′ , N′ ,
  vN′ ,
  composeReduction
    (InstPostCatalogPackageAt.at-prefix-reduction pkg) post↠N′ ,
  subst≡
    (λ γ′ → W′ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶
      ECR.transport⊑ᵂ (composeWorldExtendᴿ ext₂ ext′) q)
    (mapCtxᴿ-compose ext₂ ext′ γ)
    (rel-target-transportᴿ (applyTys-++ χs₂ ψs B′)
      (ECR.transport⊑ᵂ ext′ (ECR.transport⊑ᵂ ext₂ q))
      rel′)


spine-descent-zero : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {post : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → CT.Value post
  → W CTI2.∣ γ ⊢² M ⊑ post ∶ p
  → InstSpineDescentPackage W γ M post p
spine-descent-zero {W = W} {γ = γ} vPost rel = record
  { Δᴿ′ = _
  ; χs = []
  ; Δ′ = _
  ; W′ = W
  ; ext = ECR.sameWorldExtendᴿ
  ; final = _
  ; final-value = vPost
  ; post-reduction = ↠-refl
  ; final-relation =
      subst≡
        (λ γ′ → W CTI2.∣ γ′ ⊢² _ ⊑ _ ∶ _)
        (sym (ECR.mapCtxᴿ-same γ))
        rel
  }


inst-post-at→root-package : ∀ {fuel Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ Δᴿ₂ Δ₂}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {M′ : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {χs₂ : StoreChanges Δᴿ Δᴿ₂}
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → (rel : W CTI2.∣ γ ⊢² M ⊑ M′ ∶ p)
  → (vM : CT.Value M)
  → (vM′ : CT.Value M′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂)
  → InstPostCatalogPackageAt fuel rel vM vM′ c′ B′≢★
      c<fuel q χs₂ W₂ ext₂
  → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q
inst-post-at→root-package fuel-step catchup⁻-embed rel vM vM′
    c′ B′≢★ c<fuel q ext₂ pkg =
  inst-post-at→package rel vM vM′ c′ B′≢★ c<fuel q ext₂
    (inst-post-at-finish fuel-step catchup⁻-embed rel vM vM′
      c′ B′≢★ c<fuel q ext₂ pkg)
    pkg


ext-suc-keep-skip : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
  → ∀ X
  → extᵗ Fin.suc (toRenameᵗ (keep η) X)
      ≡ toRenameᵗ (keep (skip η)) X
ext-suc-keep-skip η Fin.zero = refl
ext-suc-keep-skip η (Fin.suc X) = refl


ext-suc-skip-keep : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
  → ∀ X
  → extᵗ Fin.suc (toRenameᵗ (skip η) X)
      ≡ toRenameᵗ (skip (keep η)) (Fin.suc X)
ext-suc-skip-keep η X = refl


source-under-left-right : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (A : Ty (suc Δ₀))
  → renameᵗ (extᵗ Fin.suc) (renameᵗ (toRenameᵗ (keep η)) A)
      ≡ renameᵗ (toRenameᵗ (keep (skip η))) A
source-under-left-right η A =
  trans (renameᵗ-comp (toRenameᵗ (keep η)) (extᵗ Fin.suc) A)
    (renameᵗ-cong A (ext-suc-keep-skip η))


target-under-left-right : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (B : Ty Δ₀)
  → renameᵗ (extᵗ Fin.suc) (renameᵗ (toRenameᵗ (skip η)) B)
      ≡ renameᵗ (toRenameᵗ (skip (keep η))) (⇑ᵗ B)
target-under-left-right η B =
  trans (renameᵗ-comp (toRenameᵗ (skip η)) (extᵗ Fin.suc) B)
    (trans (renameᵗ-cong B (ext-suc-skip-keep η))
      (sym (renameᵗ-comp Fin.suc (toRenameᵗ (skip (keep η))) B)))


left-right-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.extendᵐ I.X⊑★ μ X ≡ I.X⊑★
  → I.extendᵐ I.X⊑★ (I.instᵐ μ) (extᵗ Fin.suc X) ≡ I.X⊑★
left-right-star-map Fin.zero eq = refl
left-right-star-map (Fin.suc X) eq = eq


right-bind-under-left-lift-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ B
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld W B′) ⟩ ⇑ᵗ B
right-bind-under-left-lift-⊑ᵂ {W = W} {B′ = B′} {A = A} {B = B} p =
  subst≡
    (λ L → CTI2.impEnvʷ
      (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′))
      ⊢ L ⊑ CTI2.embedᴿ
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′))
        (⇑ᵗ B))
    (source-under-left-right (CTI2.ηᴸʷ W) A)
    (subst≡
      (λ R → CTI2.impEnvʷ
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′))
        ⊢ renameᵗ (extᵗ Fin.suc)
            (CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W) A)
          ⊑ R)
      (target-under-left-right (CTI2.ηᴿʷ W) B)
      (rename-⊑ (extᵗ Fin.suc)
        (ext-injective fin-suc-injective)
        left-right-star-map p))


right-bind-under-left-lift : RightBindUnderLeftLiftᵀ
right-bind-under-left-lift {W = W} {B = B′} = record
  { sourceStore-kept = refl
  ; targetStore-follows = refl
  ; transport⊑ᵂ = λ {A = A} {C = C} p →
      right-bind-under-left-lift-⊑ᵂ
        {W = W} {B′ = B′} {A = A} {B = C} p
  }


mapCtxᴿ-liftᴸ : MapCtxᴿLiftᴸᵀ right-bind-under-left-lift
mapCtxᴿ-liftᴸ ext CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftᴸ ext (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftᴸ ext liftγ)


Λ⊑²-cps-rewrap :
  Λ⊑²CPSRewrapᵀ right-bind-under-left-lift mapCtxᴿ-liftᴸ
Λ⊑²-cps-rewrap {p₂ = p₂} ext Anv zero∈A liftγ vV
    target⊢ bodyRel =
  CTI2.Λ⊑² Anv zero∈A (mapCtxᴿ-liftᴸ ext liftγ) vV
    target⊢ bodyRel p₂


Λ⊑²-at-rewrap : Λ⊑²AtRewrapᵀ
Λ⊑²-at-rewrap {p₂ = p₂} Anv zero∈A liftγ vV
    target⊢ bodyRel =
  CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ bodyRel p₂


catchup⁻-nonstar : Catchup⁻NonStarᵀ
catchup⁻-nonstar Bns B′ns (id ★) = catchup⁻-id ★
catchup⁻-nonstar Bns B′ns (id (‵ ι)) = catchup⁻-id (‵ ι)
catchup⁻-nonstar Bns B′ns (id (＇ X)) = catchup⁻-id (＇ X)
catchup⁻-nonstar Bns B′ns (c ↦ d) =
  catchup⁻-inert CT.fun
catchup⁻-nonstar Bns B′ns (∀ᶜ c) =
  catchup⁻-inert CT.all
catchup⁻-nonstar Bns () (_! c)
catchup⁻-nonstar () B′ns (？ c)
catchup⁻-nonstar Bns B′ns (inst_ c B≢★) =
  catchup⁻-inst
catchup⁻-nonstar Bns B′ns
    (gen_ ⦃ Bnv ⦄ ⦃ z∈B ⦄ c A≢★) =
  catchup⁻-inert (CT.genᵥ A≢★ (gen-safe c A≢★ Bnv z∈B))
catchup⁻-nonstar Bns B′ns bot-elim = catchup⁻-bot-elim
catchup⁻-nonstar Bns B′ns bot-intro = catchup⁻-bot-intro


inst-residual-source-nonstar : ∀ {Δ} {B : Ty (suc Δ)}
  → NonVar B
  → Fin.zero ∈ᵗ B
  → NonStar (B [ ★ ]ᵗ)
inst-residual-source-nonstar nonvar-base ()
inst-residual-source-nonstar nonvar-star ()
inst-residual-source-nonstar nonvar-fun zero∈B = nonstar-⇒
inst-residual-source-nonstar nonvar-all zero∈B = nonstar-∀


inst-residual-provenance : InstResidualProvenanceᵀ
inst-residual-provenance {B = B} {B′ = B′} c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ =
  catchup⁻-nonstar
    (renameNonStar (toRenameᵗ wk↪ᵗ)
      (inst-residual-source-nonstar Bnv zero∈B))
    (renameNonStar (toRenameᵗ wk↪ᵗ) (nonstar-from-≢★ B′≢★))
    (↑ᶜ (close-instᶜ c′))
