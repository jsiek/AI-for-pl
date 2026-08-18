module proof.DGG.Catchup.InstInversionProof where

-- File Charter:
--   * Provides the shared M5 target-instantiation inversion package base.
--   * Exports residual provenance, generic world/context transport,
--     reduction composition, and generated reveal/conceal utilities used by
--     the producer-specific inversion workers.
--   * Does not import the Λ-specific inversion worker.

open import Data.Empty using (⊥; ⊥-elim)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
import Data.List as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; s≤s)
open import Data.Nat.Properties using (n<1+n; ≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore using
  (TyStore; store-lift; store-bind; _∋_⦂_; Z∋; S-lift∋;
   S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; id; _↦_; ∀ᶜ_; _!; ？_; inst_; gen_;
   bot-elim; bot-intro; instᵐ; ↑ᶜ_; close-instᶜ; renameNonStar;
   subst-left-∼; subst-right-∼; _↪ᵗ_; empty; keep; skip; toRenameᵗ;
   id↪ᵗ; wk↪ᵗ)
open import Conversion using
  (Conv↑; Conv↓; replaceTy; makeConceal; 〖_,_↑_〗; rename↑;
   seal; _↦↓_; `∀↓_; id↓)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)
open import Primitives using
  (constTy-renameᵗ; primArgTy; primResultTy)
open import Reduction using
  (StoreChanges; _—↠[_]_; _—→[_]⟨_⟩_; _∎[]; bind; _∷_; [];
   ↠-refl; ↠-step; β-inst; β-Λ; ξ-⟨⟩; ξ-reveal; ξ-•;
   applyStores; applyTys; applyBody; applyVar; applyConsistency;
   applyConsistencies)
import TermCtx as T
import CastTerms as CT
open import CastTerms using
  (⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _⦂∀_[_]; _↑_; Λ_; ⇑ᵗᵐ;
   Value; RevealValue; _《_》; _↓_)
open import proof.Consistency using
  (gen-safe; castSize-subst-left-∼; castSize-subst-right-∼)
open import proof.Reduction using (cast-↠)
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; nonstar-from-≢★; rename-⊑;
   source-nonvar-from-target; source-nonvar-target; source-occurs-target;
   subst-⊑; subst₂-⊑; subst-zero-occurs-exts; target-occurs-source;
   toRenameᵗ-injective)
import proof.ImprecisionConsistency as PIC
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value; rename-occurs; StoreTransport;
   StoreTransport-lift-bind; StoreRename-suc-bind; toRename-id-eq;
   toRename-keep-eq; renameᵗ-wk-eq;
   toRename-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.CenterRename as CR
import proof.DGG.TargetBindLift as TBL
import proof.DGG.TargetExtend as TE
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; _++χ_; FuelStepSurface; CatchupCast⁻; Catchup⁻Embedᵀ;
   inst-alloc-decreaseᵀ;
   catchup⁻-inert; catchup⁻-id; catchup⁻-inst;
   catchup⁻-ground-other; catchup⁻-bot-elim; catchup⁻-bot-intro)
open import proof.DGG.Catchup.InstInversionDef using
  (Catchup⁻NonStarᵀ; InstPostCatalogPackage;
   InstPostCatalogPackageAt; InstResidualProvenanceᵀ;
   InstSpineDescentPackage; Λ⊑Λ²PostBodyTransportᵀ;
   Λ⊑Λ²PostBodyTransportAtᵀ; Λ⊑²AtRewrapᵀ;
   Λ⊑Λ²BodyAfter★; Λ⊑Λ²PostTerm; Λ⊑Λ²TargetSplit₂;
   Λ⊑²CPSRewrapᵀ; MapCtxᴿLiftᴸᵀ; RightBindUnderLeftLiftᵀ)
open import proof.DGG.Catchup.InstCatchupRightDef using
  (InstCastAllocPrefixᵀ; AllValueViewStepCatalogᵀ)
open import proof.DGG.Catchup.InstCatchupRightProof using
  (right-bind-right-bind-world-extendᴿ)
open import proof.DGG.Catchup.ColumnSupportProof using
  (castSize-applyConsistency; castSize-applyConsistencies;
   transportCatchup⁻)
open import proof.DGG.Catchup.StructuralWorldEvidenceProof using
  (mapCtxᴿ-sameCtx)


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
    ; ν₂ = InstPostCatalogPackageAt.at-ν₂ pkg
    ; residual-target =
        InstPostCatalogPackageAt.at-residual-target pkg
    ; residual-q =
        InstPostCatalogPackageAt.at-residual-q pkg
    ; residual-target-eq =
        InstPostCatalogPackageAt.at-residual-target-eq pkg
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
generated-reveal-value : ∀ {Δ} {X : TyVar Δ} {R B : Ty Δ}
  → NonVar B
  → X ∈ᵗ B
  → RevealValue (〖 X , R ↑ B 〗)
generated-reveal-value nonvar-base ()
generated-reveal-value nonvar-star ()
generated-reveal-value nonvar-fun X∈B = CT.fun
generated-reveal-value nonvar-all X∈B = CT.all


reveal-value-rename : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′)
    {A B : Ty Δ} {c : Conv↑ Δ A B}
  → RevealValue c
  → RevealValue (rename↑ ρ c)
reveal-value-rename ρ CT.fun = CT.fun
reveal-value-rename ρ CT.all = CT.all


unrenameNonVar : ∀ {Δ Δ′} {A : Ty Δ} (ρ : Δ ⇒ʳ Δ′)
  → NonVar (renameᵗ ρ A)
  → NonVar A
unrenameNonVar {A = ＇ X} ρ ()
unrenameNonVar {A = ‵ ι} ρ nonvar-base = nonvar-base
unrenameNonVar {A = ★} ρ nonvar-star = nonvar-star
unrenameNonVar {A = A ⇒ B} ρ nonvar-fun = nonvar-fun
unrenameNonVar {A = `∀ A} ρ nonvar-all = nonvar-all


mutual
  generated-reveal-⊢↑-present :
      ∀ {Δ : TyCtx} {Σ : TyStore.TyStore Δ}
        {X : TyVar Δ} {R B : Ty Δ}
    → X ∈ᵗ B
    → Σ ∋ X ⦂ R
    → Σ CTI2.⊢↑[ just X ] 〖 X , R ↑ B 〗
  generated-reveal-⊢↑-present {X = X} var-∈ X∈ with X ≟ X
  generated-reveal-⊢↑-present {X = X} var-∈ X∈ | yes refl =
    CTI2.⊢↑-unsealˣ X∈
  generated-reveal-⊢↑-present {X = X} var-∈ X∈ | no X≢X =
    ⊥-elim (X≢X refl)
  generated-reveal-⊢↑-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ with occurs? X B
  generated-reveal-⊢↑-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ | present X∈B =
    CTI2.⊢↑-⇒ˣ CTI2.join-both
      (generated-conceal-⊢↓-present X∈A X∈)
      (generated-reveal-⊢↑-present X∈B X∈)
  generated-reveal-⊢↑-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ | absent X∉B =
    CTI2.⊢↑-⇒ˣ CTI2.join-left
      (generated-conceal-⊢↓-present X∈A X∈)
      (generated-reveal-⊢↑-absent X∉B X∈)
  generated-reveal-⊢↑-present
      (∈-fun-right X∉A X∈B) X∈ =
    CTI2.⊢↑-⇒ˣ CTI2.join-right
      (generated-conceal-⊢↓-absent X∉A X∈)
      (generated-reveal-⊢↑-present X∈B X∈)
  generated-reveal-⊢↑-present (∈-all X∈B) X∈ =
    CTI2.⊢↑-∀ˣ
      (generated-reveal-⊢↑-present X∈B (S-lift∋ X∈ refl))

  generated-reveal-⊢↑-absent :
      ∀ {Δ : TyCtx} {Σ : TyStore.TyStore Δ}
        {X : TyVar Δ} {R B : Ty Δ}
    → X ∉ᵗ B
    → Σ ∋ X ⦂ R
    → Σ CTI2.⊢↑[ nothing ] 〖 X , R ↑ B 〗
  generated-reveal-⊢↑-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      with X ≟ Y
  generated-reveal-⊢↑-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      | yes refl =
    ⊥-elim (≢ᶠ→≢ X≢Y refl)
  generated-reveal-⊢↑-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      | no X≢Y′ =
    CTI2.⊢↑-idˣ
  generated-reveal-⊢↑-absent ∉-base X∈ = CTI2.⊢↑-idˣ
  generated-reveal-⊢↑-absent ∉-star X∈ = CTI2.⊢↑-idˣ
  generated-reveal-⊢↑-absent (∉-fun X∉A X∉B) X∈ =
    CTI2.⊢↑-⇒ˣ CTI2.join-none
      (generated-conceal-⊢↓-absent X∉A X∈)
      (generated-reveal-⊢↑-absent X∉B X∈)
  generated-reveal-⊢↑-absent (∉-all X∉B) X∈ =
    CTI2.⊢↑-∀-idˣ
      (generated-reveal-⊢↑-absent X∉B (S-lift∋ X∈ refl))

  generated-conceal-⊢↓-present :
      ∀ {Δ : TyCtx} {Σ : TyStore.TyStore Δ}
        {X : TyVar Δ} {R B : Ty Δ}
    → X ∈ᵗ B
    → Σ ∋ X ⦂ R
    → Σ CTI2.⊢↓[ just X ] makeConceal X R B
  generated-conceal-⊢↓-present {X = X} var-∈ X∈ with X ≟ X
  generated-conceal-⊢↓-present {X = X} var-∈ X∈ | yes refl =
    CTI2.⊢↓-sealˣ X∈
  generated-conceal-⊢↓-present {X = X} var-∈ X∈ | no X≢X =
    ⊥-elim (X≢X refl)
  generated-conceal-⊢↓-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ with occurs? X B
  generated-conceal-⊢↓-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ | present X∈B =
    CTI2.⊢↓-⇒ˣ CTI2.join-both
      (generated-reveal-⊢↑-present X∈A X∈)
      (generated-conceal-⊢↓-present X∈B X∈)
  generated-conceal-⊢↓-present {X = X} {R = R} {B = A ⇒ B}
      (∈-fun-left X∈A) X∈ | absent X∉B =
    CTI2.⊢↓-⇒ˣ CTI2.join-left
      (generated-reveal-⊢↑-present X∈A X∈)
      (generated-conceal-⊢↓-absent X∉B X∈)
  generated-conceal-⊢↓-present
      (∈-fun-right X∉A X∈B) X∈ =
    CTI2.⊢↓-⇒ˣ CTI2.join-right
      (generated-reveal-⊢↑-absent X∉A X∈)
      (generated-conceal-⊢↓-present X∈B X∈)
  generated-conceal-⊢↓-present (∈-all X∈B) X∈ =
    CTI2.⊢↓-∀ˣ
      (generated-conceal-⊢↓-present X∈B (S-lift∋ X∈ refl))

  generated-conceal-⊢↓-absent :
      ∀ {Δ : TyCtx} {Σ : TyStore.TyStore Δ}
        {X : TyVar Δ} {R B : Ty Δ}
    → X ∉ᵗ B
    → Σ ∋ X ⦂ R
    → Σ CTI2.⊢↓[ nothing ] makeConceal X R B
  generated-conceal-⊢↓-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      with X ≟ Y
  generated-conceal-⊢↓-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      | yes refl =
    ⊥-elim (≢ᶠ→≢ X≢Y refl)
  generated-conceal-⊢↓-absent {X = X} (∉-var {Y = Y} X≢Y) X∈
      | no X≢Y′ =
    CTI2.⊢↓-idˣ
  generated-conceal-⊢↓-absent ∉-base X∈ = CTI2.⊢↓-idˣ
  generated-conceal-⊢↓-absent ∉-star X∈ = CTI2.⊢↓-idˣ
  generated-conceal-⊢↓-absent (∉-fun X∉A X∉B) X∈ =
    CTI2.⊢↓-⇒ˣ CTI2.join-none
      (generated-reveal-⊢↑-absent X∉A X∈)
      (generated-conceal-⊢↓-absent X∉B X∈)
  generated-conceal-⊢↓-absent (∉-all X∉B) X∈ =
    CTI2.⊢↓-∀-idˣ
      (generated-conceal-⊢↓-absent X∉B (S-lift∋ X∈ refl))


rename-as-subst : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl


replaceEnv : ∀ {Δ} → TyVar Δ → Ty Δ → Δ ⇒ˢ Δ
replaceEnv X R Y with X ≟ Y
replaceEnv X R .X | yes refl = R
replaceEnv X R Y | no X≠Y = ＇ Y


replaceEnv-ext : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
    (Y : TyVar (suc Δ))
  → replaceEnv (Fin.suc X) (⇑ᵗ R) Y ≡ extsᵗ (replaceEnv X R) Y
replaceEnv-ext X R Fin.zero = refl
replaceEnv-ext X R (Fin.suc Y) with X ≟ Y
replaceEnv-ext X R (Fin.suc .X) | yes refl = refl
replaceEnv-ext X R (Fin.suc Y) | no X≠Y = refl


replaceTy-subst : ∀ {Δ} (X : TyVar Δ) (R B : Ty Δ)
  → replaceTy X R B ≡ substᵗ (replaceEnv X R) B
replaceTy-subst X R (＇ Y) with X ≟ Y
replaceTy-subst X R (＇ .X) | yes refl = refl
replaceTy-subst X R (＇ Y) | no X≠Y = refl
replaceTy-subst X R (‵ ι) = refl
replaceTy-subst X R ★ = refl
replaceTy-subst X R (A ⇒ B)
    rewrite replaceTy-subst X R A | replaceTy-subst X R B =
  refl
replaceTy-subst X R (`∀ B) =
  cong `∀
    (trans (replaceTy-subst (Fin.suc X) (⇑ᵗ R) B)
      (substᵗ-cong B (replaceEnv-ext X R)))

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
    with InstPostCatalogPackageAt.at-spine-descent pkg
inst-post-at-finish {γ = γ} {B′ = B′} {χs₂ = χs₂}
    fuel-step catchup⁻-embed rel vM vM′ c′
    B′≢★ c<fuel q ext₂ pkg
  | record { Δᴿ′ = Δᴿᵈ ; χs = δs ; Δ′ = Δᵈ ; W′ = Wᵈ
      ; ext = extᵈ ; final = final ; final-value = vFinal
      ; post-reduction = post↠Final ; final-relation = relFinal }
    with FuelStepSurface.smaller-extra fuel-step
      (subst≡ (λ n → suc n < _)
        (sym (castSize-applyConsistencies δs residual-cast))
        (InstPostCatalogPackageAt.at-residual-fuel pkg))
      relFinal vM vFinal
      (applyConsistencies δs residual-cast)
      (n<1+n (castSize (applyConsistencies δs residual-cast)))
      (ECR.transport⊑ᵂ extᵈ
        (InstPostCatalogPackageAt.at-residual-q pkg))
      (catchup⁻-embed final
        (transportCatchup⁻ extᵈ
          (InstPostCatalogPackageAt.at-residual-provenance pkg)))
  where
  residual-cast = InstPostCatalogPackageAt.at-residual-cast pkg
inst-post-at-finish {γ = γ} {B′ = B′} {χs₂ = χs₂}
    fuel-step catchup⁻-embed rel vM vM′ c′
    B′≢★ c<fuel q ext₂ pkg
  | record { Δᴿ′ = Δᴿᵈ ; χs = δs ; Δ′ = Δᵈ ; W′ = Wᵈ
      ; ext = extᵈ ; final = final ; final-value = vFinal
      ; post-reduction = post↠Final ; final-relation = relFinal }
  | Δᴿ′ , ψs , Δ′ , W′ , ext′ , N′ ,
    (vN′ , post↠N′ , rel′) =
  Δᴿ′ , _ , Δ′ , W′ , composeWorldExtendᴿ ext₂ᵈ ext′ , N′ ,
  vN′ ,
  composeReduction
    (composeReduction
      (InstPostCatalogPackageAt.at-prefix-reduction pkg)
      (cast-↠ residual-cast post↠Final))
    post↠N′ ,
  subst≡
    (λ γ′ → W′ CTI2.∣ γ′ ⊢² _ ⊑ _ ∶
      ECR.transport⊑ᵂ (composeWorldExtendᴿ ext₂ᵈ ext′) q)
    context-eq
    (rel-target-transportᴿ (applyTys-++ (χs₂ ++χ δs) ψs B′)
      (ECR.transport⊑ᵂ ext′ (ECR.transport⊑ᵂ ext₂ᵈ q))
      (TBL.⊢²-retarget
        {q = ECR.transport⊑ᵂ ext′ (ECR.transport⊑ᵂ ext₂ᵈ q)}
        (rel-target-transportᴿ
          (cong (applyTys ψs) residual-target-eq)
          (ECR.transport⊑ᵂ ext′
            (ECR.transport⊑ᵂ extᵈ
              (InstPostCatalogPackageAt.at-residual-q pkg)))
          rel′)))
  where
  residual-cast = InstPostCatalogPackageAt.at-residual-cast pkg

  ext₂ᵈ = composeWorldExtendᴿ ext₂ extᵈ

  residual-target-eq =
    trans
      (cong (applyTys δs)
        (InstPostCatalogPackageAt.at-residual-target-eq pkg))
      (applyTys-++ χs₂ δs B′)

  context-eq =
    trans
      (cong (ECR.mapCtxᴿ ext′) (mapCtxᴿ-compose ext₂ extᵈ γ))
      (mapCtxᴿ-compose ext₂ᵈ ext′ γ)


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


right-bind-right-bind-under-left-lift : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ W)
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★)
          (＇ Fin.zero)))
right-bind-right-bind-under-left-lift {W = W} =
  composeWorldExtendᴿ
    (right-bind-under-left-lift {W = W} {B = ★})
    (right-bind-under-left-lift
      {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})


target-insert-bind-world-extendᴿ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {B : Ty Δᴿ}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → CTI2.targetStoreʷ W′
      ≡ applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
  → ECR.WorldExtendᴿ (bind B ∷ []) W W′
target-insert-bind-world-extendᴿ {W′ = W′} {B = B} ins target-follows =
  record
    { sourceStore-kept = TE.sourceStore-kept ins
    ; targetStore-follows = target-follows
    ; transport⊑ᵂ = λ {A = A} {C = C} p →
        subst≡ (λ C′ → A CTI2.⊑ᵂ⟨ W′ ⟩ C′)
          (renameᵗ-wk-eq C)
          (TE.transport⊑ᵂ ins p)
    }


smart-fresh-bind-world-extendᴿ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {B : Ty Δᴿ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ECR.WorldExtendᴿ (bind B ∷ []) Wᵐ
      (TE.smartFreshInsertWorld
        (TE.rightBindTargetInsert {W = W} {B = B}) guard)
smart-fresh-bind-world-extendᴿ {B = B} guard =
  target-insert-bind-world-extendᴿ
    (TE.smartFreshTargetInsert TE.rightBindTargetInsert guard)
    (cong (applyStores (bind B ∷ []))
      (sym (CTI2.SmartFreshBehindGuard.targetStore-same guard)))


smart-alias-bind-world-extendᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
    {B : Ty Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ECR.WorldExtendᴿ (bind B ∷ []) Wᵐ
      (TE.smartAliasInsertWorld
        (TE.rightBindTargetInsert {W = W} {B = B}) Wᵐ)
smart-alias-bind-world-extendᴿ {B = B} guard =
  target-insert-bind-world-extendᴿ
    (TE.smartAliasTargetInsert TE.rightBindTargetInsert guard)
    (cong (applyStores (bind B ∷ []))
      (sym (CTI2.SmartAliasMergeGuard.targetStore-same guard)))


mapCtxᴿ-smart-liftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ₂ Δᵐ₂}
    {χs : StoreChanges Δᴿ (suc (suc Δᴿ))}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᵐ₂ : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) Δᵐ₂}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → {ext₂ : ECR.WorldExtendᴿ χs W W₂}
  → {extᵐ₂ : ECR.WorldExtendᴿ χs Wᵐ Wᵐ₂}
  → CTI2.SmartLiftCtxᴸ γ γᵐ
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᵐ₂ γᵐ)
mapCtxᴿ-smart-liftᴸ CTI2.smart-lift-[] = CTI2.smart-lift-[]
mapCtxᴿ-smart-liftᴸ (CTI2.smart-lift-∷ liftγ) =
  CTI2.smart-lift-∷ (mapCtxᴿ-smart-liftᴸ liftγ)


mapCtxᴿ-liftᴸ : MapCtxᴿLiftᴸᵀ right-bind-under-left-lift
mapCtxᴿ-liftᴸ ext CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftᴸ ext (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftᴸ ext liftγ)


mapCtxᴿ-liftᴸ-at : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ₂}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ Δᴿ′ Δ₂}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {ext₂ : ECR.WorldExtendᴿ χs W W₂}
    {extᴸ₂ : ECR.WorldExtendᴿ χs
      (CTI2.liftWorldLeft I.X⊑★ W)
      (CTI2.liftWorldLeft I.X⊑★ W₂)}
  → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
  → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
      (ECR.mapCtxᴿ extᴸ₂ γᴸ)
mapCtxᴿ-liftᴸ-at CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftᴸ-at (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftᴸ-at liftγ)


target-insert-bind-under-left-liftᴿ : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {π : Δ ↪ᵗ Δ′} {B : Ty Δᴿ}
  → (ins : TE.TargetInsert wk↪ᵗ π W W′)
  → CTI2.targetStoreʷ W′
      ≡ applyStores (bind B ∷ []) (CTI2.targetStoreʷ W)
  → ECR.WorldExtendᴿ (bind B ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ W)
      (CTI2.liftWorldLeft I.X⊑★ W′)
target-insert-bind-under-left-liftᴿ ins target-follows =
  target-insert-bind-world-extendᴿ
    (TE.liftLeftTargetInsert {v = I.X⊑★} ins)
    target-follows


smart-alias-bind-under-left-liftᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
    {B : Ty Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ECR.WorldExtendᴿ (bind B ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ Wᵐ)
      (CTI2.liftWorldLeft I.X⊑★
        (TE.smartAliasInsertWorld
          (TE.rightBindTargetInsert {W = W} {B = B}) Wᵐ))
smart-alias-bind-under-left-liftᴿ {W = W} {B = B} guard =
  target-insert-bind-under-left-liftᴿ
    (TE.smartAliasTargetInsert
      (TE.rightBindTargetInsert {W = W} {B = B}) guard)
    (ECR.targetStore-follows
      (smart-alias-bind-world-extendᴿ {W = W} {B = B} guard))


smart-fresh-bind-under-left-liftᴿ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {B : Ty Δᴿ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ECR.WorldExtendᴿ (bind B ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ Wᵐ)
      (CTI2.liftWorldLeft I.X⊑★
        (TE.smartFreshInsertWorld
          (TE.rightBindTargetInsert {W = W} {B = B}) guard))
smart-fresh-bind-under-left-liftᴿ {W = W} {B = B} guard =
  target-insert-bind-under-left-liftᴿ
    (TE.smartFreshTargetInsert
      (TE.rightBindTargetInsert {W = W} {B = B}) guard)
    (ECR.targetStore-follows
      (smart-fresh-bind-world-extendᴿ {W = W} {B = B} guard))

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
