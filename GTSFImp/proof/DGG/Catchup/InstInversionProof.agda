module proof.DGG.Catchup.InstInversionProof where

-- File Charter:
--   * Proves support lemmas for the M5 target-instantiation inversion
--     packages.
--   * Starts with residual `CatchupCast⁻` provenance for the Λ package.
--   * Imports only the live Def surface plus core/proof-only consistency
--     support; it does not consume other catch-up Proof modules.

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
   applyStores; applyTys; applyBody; applyVar; applyConsistency)
import TermCtx as T
import CastTerms as CT
open import CastTerms using
  (⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _⦂∀_[_]; _↑_; Λ_; ⇑ᵗᵐ;
   Value; RevealValue)
open import FunExt using (funext)
open import proof.Consistency using
  (gen-safe; castSize-subst-left-∼; castSize-subst-right-∼)
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; nonstar-from-≢★; rename-⊑;
   source-nonvar-target; source-occurs-target; subst-⊑;
   subst-zero-occurs-exts; toRenameᵗ-injective)
import proof.ImprecisionConsistency as PIC
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value; rename-occurs; StoreTransport-lift-bind;
   StoreRename-suc-bind; toRename-id-eq; toRename-keep-eq;
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
   Λ⊑²AtRewrapᵀ;
   Λ⊑Λ²BodyAfter★; Λ⊑Λ²PostTerm; Λ⊑Λ²TargetSplit₂;
   Λ⊑²CPSRewrapᵀ; MapCtxᴿLiftᴸᵀ; RightBindUnderLeftLiftᵀ)
open import proof.DGG.Catchup.InstCatchupRightDef using
  (InstCastAllocPrefixᵀ; AllValueViewStepCatalogᵀ)
open import proof.DGG.Catchup.InstCatchupRightProof using
  (right-bind-right-bind-world-extendᴿ)
open import proof.DGG.Catchup.ColumnSupportProof using
  (castSize-applyConsistency)


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


------------------------------------------------------------------------
-- Λ⊑Λ² post-body transport
------------------------------------------------------------------------

Λ⊑Λ²-route1-entry-p : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
Λ⊑Λ²-route1-entry-p {W = W} p =
  TBL.move⊑ᵂ (TBL.baseMove mv)
    (CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)}
      wk↪ᵗ
      (WD.decay⊑ᵂ
        {W = CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★)}
        {Wᵈ = CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)}
        TD.liftBothBinderDecay
        (TE.transport⊑ᵂ ins₁ p)))
  where
  ins₁ = TE.keepRightBindTargetInsert {W = W} {B = ★} {v = I.X⊑X}
  mv = TBL.freshLiftToBindTargetMove★ {W = W}


Λ⊑Λ²-route1-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)
  → CTI2.CtxImp (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
Λ⊑Λ²-route1-ctx List.[] = List.[]
Λ⊑Λ²-route1-ctx {W = W} (CTI2.ctx-imp A B p List.∷ γᴮ) =
  CTI2.ctx-imp A (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
    (Λ⊑Λ²-route1-entry-p {W = W} p) List.∷
  Λ⊑Λ²-route1-ctx γᴮ


Λ⊑Λ²-route1-map-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)
  → CTI2.CtxImp (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
Λ⊑Λ²-route1-map-ctx {W = W} γᴮ =
  TBL.moveCtx (TBL.baseMove mv)
    (CR.renameCtx wk↪ᵗ
      (WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ
          (TE.keepRightBindTargetInsert {W = W} {B = ★} {v = I.X⊑X})
          γᴮ)))
  where
  mv = TBL.freshLiftToBindTargetMove★ {W = W}


Λ⊑Λ²-route1-map-ctx-eq : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W))
  → Λ⊑Λ²-route1-map-ctx γᴮ ≡ Λ⊑Λ²-route1-ctx γᴮ
Λ⊑Λ²-route1-map-ctx-eq List.[] = refl
Λ⊑Λ²-route1-map-ctx-eq {W = W}
    (CTI2.ctx-imp A B p List.∷ γᴮ) =
  cong (CTI2.ctx-imp A (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
    (Λ⊑Λ²-route1-entry-p {W = W} p) List.∷_)
    (Λ⊑Λ²-route1-map-ctx-eq γᴮ)


Λ⊑Λ²-route1-prefix : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ pᵇ ∈ A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B ]
      TBL.ΛLiftToBindFreshWorld I.X⊑★ W CTI2.∣
        Λ⊑Λ²-route1-ctx γᴮ ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
Λ⊑Λ²-route1-prefix {W = W} {γᴮ = γᴮ} {V = V} {V′ = V′}
    {A = A} {B = B} {body-p = body-p} rel =
  pᵇ ,
  subst≡
    (λ γᵇ → TBL.ΛLiftToBindFreshWorld I.X⊑★ W CTI2.∣ γᵇ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ)
    (Λ⊑Λ²-route1-map-ctx-eq γᴮ)
    (TBL.⊢²-target-bind-lift-move mv relʳ)
  where
  ins₁ : TE.TargetInsert (keep wk↪ᵗ) (keep wk↪ᵗ)
      (CTI2.liftWorldBoth I.X⊑X W)
      (CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★))
  ins₁ = TE.keepRightBindTargetInsert {W = W} {B = ★} {v = I.X⊑X}

  p₁ : A CTI2.⊑ᵂ⟨
        CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  p₁ =
    TE.transport⊑ᵂ ins₁ body-p

  rel₁ : CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★)
      CTI2.∣ TE.mapCtxᵀ ins₁ γᴮ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p₁
  rel₁ =
    TE.⊢²-target-insert ins₁ rel

  pᵈ : A CTI2.⊑ᵂ⟨
        CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵈ =
    WD.decay⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★)}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)}
      TD.liftBothBinderDecay p₁

  relᵈ : CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)
      CTI2.∣ WD.decayCtx TD.liftBothBinderDecay (TE.mapCtxᵀ ins₁ γᴮ)
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵈ
  relᵈ =
    TD.⊢²-decay
      {W = CTI2.liftWorldBoth I.X⊑X (CTI2.rightOnlyWorld W ★)}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)}
      TD.liftBothBinderDecay rel₁

  pʳ : A CTI2.⊑ᵂ⟨
        CR.renameWorld wk↪ᵗ
          (CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★))
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★)}
      wk↪ᵗ pᵈ

  relʳ : CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth I.X⊑★ (CTI2.rightOnlyWorld W ★))
      CTI2.∣ CR.renameCtx wk↪ᵗ
        (WD.decayCtx TD.liftBothBinderDecay (TE.mapCtxᵀ ins₁ γᴮ))
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pʳ
  relʳ =
    CR.⊢²-extend-center relᵈ pʳ

  mv = TBL.freshLiftToBindTargetMove★ {W = W}

  pᵇ : A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵇ =
    TBL.move⊑ᵂ (TBL.baseMove mv) pʳ


Λ⊑Λ²-route1ᴸ-entry-p : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W) ⟩ B
  → A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
Λ⊑Λ²-route1ᴸ-entry-p {W = W} p =
  TBL.move⊑ᵂ (TBL.baseMove mv)
    (CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      wk↪ᵗ
      (WD.decay⊑ᵂ
        {W = CTI2.liftWorldBoth I.X⊑X
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
        {Wᵈ = CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
        TD.liftBothBinderDecay
        (TE.transport⊑ᵂ ins₁ p)))
  where
  ins₁ : TE.TargetInsert (keep wk↪ᵗ) (keep (keep wk↪ᵗ))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★)))
  ins₁ =
    TE.liftBothTargetInsert {v = I.X⊑X}
      (TE.liftLeftTargetInsert {v = I.X⊑★}
        (TE.rightBindTargetInsert {W = W} {B = ★}))

  mv = TBL.freshLiftToBindTargetMove★ᴸ {W = W}


Λ⊑Λ²-route1ᴸ-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W))
  → CTI2.CtxImp (TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W)
Λ⊑Λ²-route1ᴸ-ctx List.[] = List.[]
Λ⊑Λ²-route1ᴸ-ctx {W = W}
    (CTI2.ctx-imp A B p List.∷ γᴮ) =
  CTI2.ctx-imp A (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
    (Λ⊑Λ²-route1ᴸ-entry-p {W = W} p) List.∷
  Λ⊑Λ²-route1ᴸ-ctx γᴮ


Λ⊑Λ²-route1ᴸ-map-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W))
  → CTI2.CtxImp (TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W)
Λ⊑Λ²-route1ᴸ-map-ctx {W = W} γᴮ =
  TBL.moveCtx (TBL.baseMove mv)
    (CR.renameCtx wk↪ᵗ
      (WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ ins₁ γᴮ)))
  where
  ins₁ : TE.TargetInsert (keep wk↪ᵗ) (keep (keep wk↪ᵗ))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★)))
  ins₁ =
    TE.liftBothTargetInsert {v = I.X⊑X}
      (TE.liftLeftTargetInsert {v = I.X⊑★}
        (TE.rightBindTargetInsert {W = W} {B = ★}))

  mv = TBL.freshLiftToBindTargetMove★ᴸ {W = W}


Λ⊑Λ²-route1ᴸ-map-ctx-eq : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W)))
  → Λ⊑Λ²-route1ᴸ-map-ctx γᴮ ≡ Λ⊑Λ²-route1ᴸ-ctx γᴮ
Λ⊑Λ²-route1ᴸ-map-ctx-eq List.[] = refl
Λ⊑Λ²-route1ᴸ-map-ctx-eq {W = W}
    (CTI2.ctx-imp A B p List.∷ γᴮ) =
  cong (CTI2.ctx-imp A (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
    (Λ⊑Λ²-route1ᴸ-entry-p {W = W} p) List.∷_)
    (Λ⊑Λ²-route1ᴸ-map-ctx-eq γᴮ)


Λ⊑Λ²-route1ᴸ-prefix : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W) ⟩ B}
  → CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ pᵇ ∈ A CTI2.⊑ᵂ⟨
        TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B ]
      TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W CTI2.∣
        Λ⊑Λ²-route1ᴸ-ctx γᴮ ⊢² V
          ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
Λ⊑Λ²-route1ᴸ-prefix {W = W} {γᴮ = γᴮ} {V = V} {V′ = V′}
    {A = A} {B = B} {body-p = body-p} rel =
  pᵇ ,
  subst≡
    (λ γᵇ → TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W CTI2.∣ γᵇ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ)
    (Λ⊑Λ²-route1ᴸ-map-ctx-eq γᴮ)
    (TBL.⊢²-target-bind-lift-move mv relʳ)
  where
  ins₁ : TE.TargetInsert (keep wk↪ᵗ) (keep (keep wk↪ᵗ))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★)))
  ins₁ =
    TE.liftBothTargetInsert {v = I.X⊑X}
      (TE.liftLeftTargetInsert {v = I.X⊑★}
        (TE.rightBindTargetInsert {W = W} {B = ★}))

  p₁ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))
        ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  p₁ = TE.transport⊑ᵂ ins₁ body-p

  rel₁ : CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))
      CTI2.∣ TE.mapCtxᵀ ins₁ γᴮ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p₁
  rel₁ = TE.⊢²-target-insert ins₁ rel

  pᵈ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))
        ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵈ =
    WD.decay⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      TD.liftBothBinderDecay p₁

  relᵈ : CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))
      CTI2.∣ WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ ins₁ γᴮ)
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵈ
  relᵈ =
    TD.⊢²-decay
      {W = CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      TD.liftBothBinderDecay rel₁

  pʳ : A CTI2.⊑ᵂ⟨ CR.renameWorld wk↪ᵗ
          (CTI2.liftWorldBoth I.X⊑★
            (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★)))
        ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★))}
      wk↪ᵗ pᵈ

  relʳ : CR.renameWorld wk↪ᵗ
        (CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W ★)))
      CTI2.∣ CR.renameCtx wk↪ᵗ
        (WD.decayCtx TD.liftBothBinderDecay
          (TE.mapCtxᵀ ins₁ γᴮ))
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pʳ
  relʳ = CR.⊢²-extend-center relᵈ pʳ

  mv = TBL.freshLiftToBindTargetMove★ᴸ {W = W}

  pᵇ : A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorldᴸ I.X⊑★ W ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵇ = TBL.move⊑ᵂ (TBL.baseMove mv) pʳ


ΛPostMidWorld : ∀ {Δᴸ Δᴿ Δ}
  → CTI2.World Δᴸ Δᴿ Δ
  → CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
ΛPostMidWorld W =
  CTI2.world
    (skip (skip (keep (CTI2.ηᴸʷ W))))
    (skip (keep (keep (CTI2.ηᴿʷ W))))
    (I.instᵐ (I.instᵐ (I.instᵐ (CTI2.impEnvʷ W))))
    (store-lift (CTI2.sourceStoreʷ W))
    (store-bind (store-bind (CTI2.targetStoreʷ W) ★) (＇ Fin.zero))


Λ-route1-context-target-eq : ∀ {Δ} (B : Ty Δ)
  → applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
    ≡ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
Λ-route1-context-target-eq B =
  trans (renameᵗ-comp Fin.suc Fin.suc B)
    (trans (renameᵗ-cong B var-eq)
      (sym (renameᵗ-comp Fin.suc
        (toRenameᵗ (keep wk↪ᵗ)) B)))
  where
  var-eq : ∀ X
    → Fin.suc (Fin.suc X) ≡
      toRenameᵗ (keep wk↪ᵗ) (Fin.suc X)
  var-eq X = cong Fin.suc (sym (toRename-wk-eq X))


applyBody-bind★-eq : ∀ {Δ} (B : Ty (suc Δ))
  → applyBody (bind ★) B
    ≡ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
applyBody-bind★-eq B = renameᵗ-cong B var-eq
  where
  var-eq : ∀ X
    → extᵗ Fin.suc X ≡ toRenameᵗ (keep wk↪ᵗ) X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = cong Fin.suc (sym (toRename-wk-eq X))


shifted-source-rename-eq : ∀ {Δ Δ′}
    (ρ₁ ρ₂ : TyVar (suc Δ) → TyVar Δ′)
  → (∀ X → ρ₁ (Fin.suc X) ≡ ρ₂ (Fin.suc X))
  → (A : Ty Δ)
  → renameᵗ ρ₁ (⇑ᵗ A) ≡ renameᵗ ρ₂ (⇑ᵗ A)
shifted-source-rename-eq ρ₁ ρ₂ eq A =
  trans (renameᵗ-comp Fin.suc ρ₁ A)
    (trans (renameᵗ-cong A eq)
      (sym (renameᵗ-comp Fin.suc ρ₂ A)))


target-left-lift-eq : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ) (B : Ty Δ₀)
  → renameᵗ (toRenameᵗ (skip η)) B
    ≡ ⇑ᵗ (renameᵗ (toRenameᵗ η) B)
target-left-lift-eq η B =
  trans (renameᵗ-cong B (λ X → refl))
    (sym (renameᵗ-comp (toRenameᵗ η) Fin.suc B))


Λ-fresh-mid-env-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.impEnvʷ (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
    ≡ CTI2.impEnvʷ (ΛPostMidWorld W)
Λ-fresh-mid-env-eq W =
  funext λ
    { Fin.zero → refl
    ; (Fin.suc Fin.zero) → refl
    ; (Fin.suc (Fin.suc Fin.zero)) → refl
    ; (Fin.suc (Fin.suc (Fin.suc Z))) → refl
    }


Λ-mid-out-env-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.impEnvʷ (ΛPostMidWorld W)
    ≡ CTI2.impEnvʷ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
Λ-mid-out-env-eq W =
  funext λ
    { Fin.zero → refl
    ; (Fin.suc Fin.zero) → refl
    ; (Fin.suc (Fin.suc Fin.zero)) → refl
    ; (Fin.suc (Fin.suc (Fin.suc Z))) → refl
    }


Λ-fresh-mid-source-shift-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ)
  → CTI2.embedᴸ (TBL.ΛLiftToBindFreshWorld I.X⊑★ W) (⇑ᵗ A)
    ≡ CTI2.embedᴸ (ΛPostMidWorld W) (⇑ᵗ A)
Λ-fresh-mid-source-shift-eq W A =
  shifted-source-rename-eq
    (toRenameᵗ (CTI2.ηᴸʷ (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)))
    (toRenameᵗ (CTI2.ηᴸʷ (ΛPostMidWorld W)))
    (λ X → refl)
    A


Λ-mid-out-source-shift-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty Δᴸ)
  → CTI2.embedᴸ (ΛPostMidWorld W) (⇑ᵗ A)
    ≡ CTI2.embedᴸ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      (⇑ᵗ A)
Λ-mid-out-source-shift-eq W A =
  shifted-source-rename-eq
    (toRenameᵗ (CTI2.ηᴸʷ (ΛPostMidWorld W)))
    (toRenameᵗ (CTI2.ηᴸʷ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))))
    (λ X → refl)
    A


Λ-fresh-mid-target-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (B : Ty (suc (suc Δᴿ)))
  → CTI2.embedᴿ (TBL.ΛLiftToBindFreshWorld I.X⊑★ W) B
    ≡ CTI2.embedᴿ (ΛPostMidWorld W) B
Λ-fresh-mid-target-eq W B = renameᵗ-cong B (λ X → refl)


Λ-mid-out-target-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (B : Ty (suc (suc Δᴿ)))
  → CTI2.embedᴿ (ΛPostMidWorld W) B
    ≡ CTI2.embedᴿ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      B
Λ-mid-out-target-eq W B = renameᵗ-cong B (λ X → refl)


Λ-fresh-to-mid-shifted-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty (suc (suc Δᴿ))}
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨
      TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ B
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ ΛPostMidWorld W ⟩ B
Λ-fresh-to-mid-shifted-⊑ᵂ {W = W} {A = A} {B = B} p =
  subst≡
    (λ μ → μ ⊢ CTI2.embedᴸ (ΛPostMidWorld W) (⇑ᵗ A)
      ⊑ CTI2.embedᴿ (ΛPostMidWorld W) B)
    (Λ-fresh-mid-env-eq W)
    (subst≡
      (λ R → CTI2.impEnvʷ
          (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
        ⊢ CTI2.embedᴸ (ΛPostMidWorld W) (⇑ᵗ A) ⊑ R)
      (Λ-fresh-mid-target-eq W B)
      (subst≡
        (λ L → CTI2.impEnvʷ
            (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
          ⊢ L ⊑ CTI2.embedᴿ
            (TBL.ΛLiftToBindFreshWorld I.X⊑★ W) B)
        (Λ-fresh-mid-source-shift-eq W A)
        p))


Λ-mid-to-out-shifted-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty (suc (suc Δᴿ))}
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ ΛPostMidWorld W ⟩ B
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      ⟩ B
Λ-mid-to-out-shifted-⊑ᵂ {W = W} {A = A} {B = B} p =
  subst≡
    (λ μ → μ ⊢ CTI2.embedᴸ Wout (⇑ᵗ A)
      ⊑ CTI2.embedᴿ Wout B)
    (Λ-mid-out-env-eq W)
    (subst≡
      (λ R → CTI2.impEnvʷ (ΛPostMidWorld W)
        ⊢ CTI2.embedᴸ Wout (⇑ᵗ A) ⊑ R)
      (Λ-mid-out-target-eq W B)
      (subst≡
        (λ L → CTI2.impEnvʷ (ΛPostMidWorld W)
          ⊢ L ⊑ CTI2.embedᴿ (ΛPostMidWorld W) B)
        (Λ-mid-out-source-shift-eq W A)
        p))
  where
  Wout =
    CTI2.liftWorldLeft I.X⊑★
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))


Λ-route1-fresh-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
Λ-route1-fresh-ctx CTI2.lift-[] = List.[]
Λ-route1-fresh-ctx {W = W}
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (subst≡
      (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
        TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ C)
      (sym (Λ-route1-context-target-eq B))
      (Λ⊑Λ²-route1-entry-p {W = W} p′)) List.∷
  Λ-route1-fresh-ctx liftγ


Λ-route1-mid-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp (ΛPostMidWorld W)
Λ-route1-mid-ctx CTI2.lift-[] = List.[]
Λ-route1-mid-ctx {W = W}
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (Λ-fresh-to-mid-shifted-⊑ᵂ {W = W} {A = A}
      {B = applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B}
      (subst≡
        (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
          TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ C)
        (sym (Λ-route1-context-target-eq B))
        (Λ⊑Λ²-route1-entry-p {W = W} p′))) List.∷
  Λ-route1-mid-ctx liftγ


Λ-route1-out-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
Λ-route1-out-ctx CTI2.lift-[] = List.[]
Λ-route1-out-ctx {W = W}
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (Λ-mid-to-out-shifted-⊑ᵂ {W = W} {A = A}
      {B = applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B}
      (Λ-fresh-to-mid-shifted-⊑ᵂ {W = W} {A = A}
        {B = applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B}
        (subst≡
          (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
            TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ C)
          (sym (Λ-route1-context-target-eq B))
          (Λ⊑Λ²-route1-entry-p {W = W} p′)))) List.∷
  Λ-route1-out-ctx liftγ


Λ-route1-ctx-fresh-eq : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → Λ⊑Λ²-route1-ctx γᴮ ≡ Λ-route1-fresh-ctx liftγ
Λ-route1-ctx-fresh-eq CTI2.lift-[] = refl
Λ-route1-ctx-fresh-eq {W = W}
    (CTI2.lift-∷ {B = B} {p′ = p′} liftγ) =
  cong₂ List._∷_
    (ctx-imp-transportᴿ
      (sym (Λ-route1-context-target-eq B))
      (Λ⊑Λ²-route1-entry-p {W = W} p′))
    (Λ-route1-ctx-fresh-eq liftγ)


Λ-route1-mid-fresh-same : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.SameCtx (Λ-route1-mid-ctx liftγ)
      (Λ-route1-fresh-ctx liftγ)
Λ-route1-mid-fresh-same CTI2.lift-[] = CTI2.same-[]
Λ-route1-mid-fresh-same (CTI2.lift-∷ liftγ) =
  CTI2.same-∷ (Λ-route1-mid-fresh-same liftγ)


Λ-route1-out-mid-same : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.SameCtx (Λ-route1-out-ctx liftγ)
      (Λ-route1-mid-ctx liftγ)
Λ-route1-out-mid-same CTI2.lift-[] = CTI2.same-[]
Λ-route1-out-mid-same (CTI2.lift-∷ liftγ) =
  CTI2.same-∷ (Λ-route1-out-mid-same liftγ)


Λ-route1-out-liftCtxᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
      (Λ-route1-out-ctx liftγ)
Λ-route1-out-liftCtxᴸ ext₂ CTI2.lift-[] = CTI2.liftᴸ-[]
Λ-route1-out-liftCtxᴸ ext₂ (CTI2.lift-∷ liftγ) =
  CTI2.liftᴸ-∷ (Λ-route1-out-liftCtxᴸ ext₂ liftγ)


liftCtxᴸ-target : ∀ {Δᴸ Δᴿ Δ} {v}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γ′ : CTI2.CtxImp (CTI2.liftWorldLeft v W)}
  → CTI2.LiftCtxᴸ v γ γ′
  → CTI2.tgtCtxʷ γ′ ≡ CTI2.tgtCtxʷ γ
liftCtxᴸ-target CTI2.liftᴸ-[] = refl
liftCtxᴸ-target (CTI2.liftᴸ-∷ liftγ) =
  cong (_ List.∷_) (liftCtxᴸ-target liftγ)


Λ-mid-fresh-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.ImpEnvMono (ΛPostMidWorld W)
      (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)
Λ-mid-fresh-mono W Fin.zero eq = refl
Λ-mid-fresh-mono W (Fin.suc Fin.zero) eq = refl
Λ-mid-fresh-mono W (Fin.suc (Fin.suc Fin.zero)) eq = refl
Λ-mid-fresh-mono W (Fin.suc (Fin.suc (Fin.suc Z))) eq = eq


Λ-out-mid-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.ImpEnvMono
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      (ΛPostMidWorld W)
Λ-out-mid-mono W Fin.zero eq = refl
Λ-out-mid-mono W (Fin.suc Fin.zero) eq = refl
Λ-out-mid-mono W (Fin.suc (Fin.suc Fin.zero)) eq = refl
Λ-out-mid-mono W (Fin.suc (Fin.suc (Fin.suc Z))) eq = eq


Λ-inner-rebaseᴿ : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.RebaseAtᴿ (ΛPostMidWorld W)
      (TBL.ΛLiftToBindFreshWorld I.X⊑★ W) (just Fin.zero)
Λ-inner-rebaseᴿ W =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at (CTI2.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTI2.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ
        (TBL.ΛLiftToBindFreshWorld I.X⊑★ W)) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ (ΛPostMidWorld W)) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc Y} neq = refl


Λ-outer-rebaseᴿ : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → CTI2.RebaseAtᴿ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      (ΛPostMidWorld W) (just (Fin.suc Fin.zero))
Λ-outer-rebaseᴿ W =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at (CTI2.same-runtime refl refl)
      source-off (λ Y → refl) refl
      (CTI2.store-rep-imp (I.X⊑★ refl)))
  where
  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ (ΛPostMidWorld W)) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ
        (CTI2.liftWorldLeft I.X⊑★
          (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★)
            (＇ Fin.zero)))) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc Y} neq = refl


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


subst₂-star-map-exts : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {ν : I.ImpEnv Δ′} {σᴸ : Δ ⇒ˢ Δ′}
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σᴸ X ⊑ ★)
  → ∀ X → I.extᵐ μ X ≡ I.X⊑★
      → I.extᵐ ν ⊢ extsᵗ σᴸ X ⊑ ★
subst₂-star-map-exts star Fin.zero ()
subst₂-star-map-exts star (Fin.suc X) eq =
  rename-⊑ Fin.suc fin-suc-injective (λ Y eq′ → eq′) (star X eq)


subst₂-star-map-insts : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {ν : I.ImpEnv Δ′} {σᴸ : Δ ⇒ˢ Δ′}
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σᴸ X ⊑ ★)
  → ∀ X → I.instᵐ μ X ≡ I.X⊑★
      → I.instᵐ ν ⊢ extsᵗ σᴸ X ⊑ ★
subst₂-star-map-insts star Fin.zero eq = I.X⊑★ refl
subst₂-star-map-insts star (Fin.suc X) eq =
  rename-⊑ Fin.suc fin-suc-injective (λ Y eq′ → eq′) (star X eq)


subst₂-same-map-exts : ∀ {Δ Δ′}
    {ν : I.ImpEnv Δ′} {σᴸ σᴿ : Δ ⇒ˢ Δ′}
  → (∀ X → ν ⊢ σᴸ X ⊑ σᴿ X)
  → ∀ X
      → I.extᵐ ν ⊢ extsᵗ σᴸ X ⊑ extsᵗ σᴿ X
subst₂-same-map-exts same Fin.zero = I.X⊑X
subst₂-same-map-exts same (Fin.suc X) =
  rename-⊑ Fin.suc fin-suc-injective (λ Y eq′ → eq′) (same X)


subst₂-same-map-insts : ∀ {Δ Δ′}
    {ν : I.ImpEnv Δ′} {σᴸ σᴿ : Δ ⇒ˢ Δ′}
  → (∀ X → ν ⊢ σᴸ X ⊑ σᴿ X)
  → ∀ X
      → I.instᵐ ν ⊢ extsᵗ σᴸ X ⊑ extsᵗ σᴿ X
subst₂-same-map-insts same Fin.zero = I.X⊑X
subst₂-same-map-insts same (Fin.suc X) =
  rename-⊑ Fin.suc fin-suc-injective (λ Y eq′ → eq′) (same X)


subst₂-⊑ : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {ν : I.ImpEnv Δ′} {σᴸ σᴿ : Δ ⇒ˢ Δ′}
    {A B : Ty Δ}
  → (∀ X → ν ⊢ σᴸ X ⊑ σᴿ X)
  → (∀ X → μ X ≡ I.X⊑★ → ν ⊢ σᴸ X ⊑ ★)
  → μ ⊢ A ⊑ B
  → ν ⊢ substᵗ σᴸ A ⊑ substᵗ σᴿ B
subst₂-⊑ same star I.★⊑★ = I.★⊑★
subst₂-⊑ same star I.ι⊑ι = I.ι⊑ι
subst₂-⊑ same star I.X⊑X = same _
subst₂-⊑ same star (I.⇒⊑⇒ A⊑B C⊑D) =
  I.⇒⊑⇒ (subst₂-⊑ same star A⊑B)
    (subst₂-⊑ same star C⊑D)
subst₂-⊑ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ} same star
    (I.∀⊑∀ A⊑B) =
  I.∀⊑∀
    (subst₂-⊑ {μ = I.extᵐ μ} {ν = I.extᵐ ν}
      {σᴸ = extsᵗ σᴸ} {σᴿ = extsᵗ σᴿ}
      (subst₂-same-map-exts same)
      (subst₂-star-map-exts star) A⊑B)
subst₂-⊑ same star (I.⇒⊑★ A⊑★ B⊑★) =
  I.⇒⊑★ (subst₂-⊑ same star A⊑★)
    (subst₂-⊑ same star B⊑★)
subst₂-⊑ same star I.ι⊑★ = I.ι⊑★
subst₂-⊑ same star (I.X⊑★ x⊑★) = star _ x⊑★
subst₂-⊑ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ} same star
    (I.∀⊑ {A = A} {B = B} Anv zero∈A A⊑B) =
  I.∀⊑ (substNonVar (extsᵗ σᴸ) Anv)
    (subst-zero-occurs-exts zero∈A)
    (subst≡ (λ T → I.instᵐ ν ⊢ substᵗ (extsᵗ σᴸ) A ⊑ T)
      (substᵗ-shift σᴿ B)
      (subst₂-⊑ {μ = I.instᵐ μ} {ν = I.instᵐ ν}
        {σᴸ = extsᵗ σᴸ} {σᴿ = extsᵗ σᴿ}
        (subst₂-same-map-insts same)
        (subst₂-star-map-insts star) A⊑B))
subst₂-⊑ same star I.∀★⊑★ = I.∀★⊑★
subst₂-⊑ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ}
    same star (I.∀⊑★ {A = A} Ans A⊑★)
    with substᵗ (extsᵗ σᴸ) A ≟Ty ★
subst₂-⊑ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ}
    same star (I.∀⊑★ {A = A} Ans A⊑★)
    | yes Aσ≡★ =
  subst≡ (λ T → _ ⊢ `∀ T ⊑ ★) (sym Aσ≡★) I.∀★⊑★
subst₂-⊑ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ}
    same star (I.∀⊑★ {A = A} Ans A⊑★)
    | no Aσ≢★ =
  I.∀⊑★ (nonstar-from-≢★ Aσ≢★)
    (subst₂-⊑ {μ = I.extᵐ μ} {ν = I.extᵐ ν}
      {σᴸ = extsᵗ σᴸ} {σᴿ = extsᵗ σᴿ}
      (subst₂-same-map-exts same)
      (subst₂-star-map-exts star) A⊑★)
subst₂-⊑ same star I.bot-elim = I.bot-elim
subst₂-⊑ same star I.bot⊑★ = I.bot⊑★


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
    ⊥-elim (X≢Y refl)
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
    ⊥-elim (X≢Y refl)
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


inner-reveal-target-eq : ∀ {Δ} (B : Ty (suc Δ))
  → replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
      (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
    ≡ renameᵗ Fin.suc B
inner-reveal-target-eq B =
  trans
    (replaceTy-subst Fin.zero (⇑ᵗ (＇ Fin.zero))
      (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B))
    (trans
      (substᵗ-rename
        (replaceEnv Fin.zero (⇑ᵗ (＇ Fin.zero)))
        (toRenameᵗ (keep wk↪ᵗ)) B)
      (trans (substᵗ-cong B var-eq)
        (rename-as-subst Fin.suc B)))
  where
  var-eq : ∀ X
    → replaceEnv Fin.zero (⇑ᵗ (＇ Fin.zero))
        (toRenameᵗ (keep wk↪ᵗ) X)
      ≡ ＇ Fin.suc X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = cong (λ Z → ＇ Fin.suc Z) (toRename-wk-eq X)


inner-reveal-target-eq-applyBody : ∀ {Δ} (B : Ty (suc Δ))
  → replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) (applyBody (bind ★) B)
    ≡ renameᵗ Fin.suc B
inner-reveal-target-eq-applyBody B =
  trans
    (cong (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)))
      (applyBody-bind★-eq B))
    (inner-reveal-target-eq B)


ΛResidualSource₂ : ∀ {Δ} → Ty (suc Δ) → Ty (suc (suc Δ))
ΛResidualSource₂ B = ⇑ᵗ (renameᵗ (toRenameᵗ wk↪ᵗ) (B [ ★ ]ᵗ))


ΛResidualTarget₂ : ∀ {Δ} → Ty Δ → Ty (suc (suc Δ))
ΛResidualTarget₂ B = ⇑ᵗ (renameᵗ (toRenameᵗ wk↪ᵗ) B)


residual-source₂-eq : ∀ {Δ} (B : Ty (suc Δ))
  → substᵗ Λ⊑Λ²TargetSplit₂ B ≡ ΛResidualSource₂ B
residual-source₂-eq B =
  sym
    (trans
      (renameᵗ-comp (toRenameᵗ wk↪ᵗ) Fin.suc (B [ ★ ]ᵗ))
      (trans
        (renameᵗ-subst
          (λ X → Fin.suc (toRenameᵗ wk↪ᵗ X))
          (singleSubᵗ ★) B)
        (substᵗ-cong B var-eq)))
  where
  var-eq : ∀ X
    → renameᵗ (λ Y → Fin.suc (toRenameᵗ wk↪ᵗ Y))
        (singleSubᵗ ★ X)
      ≡ Λ⊑Λ²TargetSplit₂ X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) =
    cong (λ Y → ＇ Fin.suc Y) (toRename-wk-eq X)


residual-target₂-eq : ∀ {Δ} (B : Ty Δ)
  → applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
    ≡ ΛResidualTarget₂ B
residual-target₂-eq B =
  trans (renameᵗ-comp Fin.suc Fin.suc B)
    (trans (renameᵗ-cong B var-eq)
      (sym (renameᵗ-comp (toRenameᵗ wk↪ᵗ) Fin.suc B)))
  where
  var-eq : ∀ X
    → Fin.suc (Fin.suc X) ≡ Fin.suc (toRenameᵗ wk↪ᵗ X)
  var-eq X = cong Fin.suc (sym (toRename-wk-eq X))


outer-reveal-target-eq : ∀ {Δ} (B : Ty (suc Δ))
  → renameᵗ Fin.suc (replaceTy Fin.zero ★ B)
    ≡ substᵗ Λ⊑Λ²TargetSplit₂ B
outer-reveal-target-eq B =
  trans (cong (renameᵗ Fin.suc) (replaceTy-subst Fin.zero ★ B))
    (trans (renameᵗ-subst Fin.suc (replaceEnv Fin.zero ★) B)
      (substᵗ-cong B var-eq))
  where
  var-eq : ∀ X
    → renameᵗ Fin.suc (replaceEnv Fin.zero ★ X)
      ≡ Λ⊑Λ²TargetSplit₂ X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


outer-reveal-target-generated-eq : ∀ {Δ} (B : Ty (suc Δ))
  → replaceTy (Fin.suc Fin.zero) ★ (renameᵗ Fin.suc B)
    ≡ substᵗ Λ⊑Λ²TargetSplit₂ B
outer-reveal-target-generated-eq B =
  trans
    (replaceTy-subst (Fin.suc Fin.zero) ★ (renameᵗ Fin.suc B))
    (trans
      (substᵗ-rename (replaceEnv (Fin.suc Fin.zero) ★)
        Fin.suc B)
      (substᵗ-cong B var-eq))
  where
  var-eq : ∀ X
    → replaceEnv (Fin.suc Fin.zero) ★ (Fin.suc X)
      ≡ Λ⊑Λ²TargetSplit₂ X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


splitSource₃ : ∀ {Δ}
  → TyVar (suc Δ)
  → Ty (suc (suc (suc Δ)))
splitSource₃ Fin.zero = ＇ Fin.zero
splitSource₃ (Fin.suc X) = ＇ (Fin.suc (Fin.suc (Fin.suc X)))


splitTarget★₃ : ∀ {Δ}
  → TyVar (suc Δ)
  → Ty (suc (suc (suc Δ)))
splitTarget★₃ Fin.zero = ★
splitTarget★₃ (Fin.suc X) = ＇ (Fin.suc (Fin.suc (Fin.suc X)))


innerρ₃ : ∀ {Δ}
  → TyVar (suc Δ)
  → TyVar (suc (suc (suc Δ)))
innerρ₃ Fin.zero = Fin.suc (Fin.suc Fin.zero)
innerρ₃ (Fin.suc X) = Fin.suc (Fin.suc (Fin.suc X))


innerρ₃-injective : ∀ {Δ} {X Y : TyVar (suc Δ)}
  → innerρ₃ X ≡ innerρ₃ Y
  → X ≡ Y
innerρ₃-injective {X = Fin.zero} {Y = Fin.zero} eq = refl
innerρ₃-injective {X = Fin.zero} {Y = Fin.suc Y} ()
innerρ₃-injective {X = Fin.suc X} {Y = Fin.zero} ()
innerρ₃-injective {X = Fin.suc X} {Y = Fin.suc Y} eq =
  cong Fin.suc
    (fin-suc-injective (fin-suc-injective (fin-suc-injective eq)))


innerρ₃-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X → I.extendᵐ I.X⊑X μ X ≡ I.X⊑★
      → I.instᵐ (I.instᵐ (I.instᵐ μ)) (innerρ₃ X) ≡ I.X⊑★
innerρ₃-star-map Fin.zero ()
innerρ₃-star-map (Fin.suc X) eq = eq


split★-same : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.instᵐ (I.instᵐ (I.instᵐ μ))
      ⊢ splitSource₃ X ⊑ splitTarget★₃ X
split★-same Fin.zero = I.X⊑★ refl
split★-same (Fin.suc X) = I.X⊑X


split★-star : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.extendᵐ I.X⊑X μ X ≡ I.X⊑★
  → I.instᵐ (I.instᵐ (I.instᵐ μ)) ⊢ splitSource₃ X ⊑ ★
split★-star Fin.zero ()
split★-star (Fin.suc X) eq = I.X⊑★ eq


source-split₃-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty (suc Δᴸ))
  → substᵗ splitSource₃
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
    ≡ CTI2.embedᴸ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      A
source-split₃-eq W A =
  trans (substᵗ-rename splitSource₃ (toRenameᵗ (keep (CTI2.ηᴸʷ W))) A)
    (trans (substᵗ-cong A var-eq)
      (rename-as-subst
        (toRenameᵗ (keep (skip (skip (CTI2.ηᴸʷ W))))) A))
  where
  var-eq : ∀ X
    → splitSource₃ (toRenameᵗ (keep (CTI2.ηᴸʷ W)) X)
      ≡ ＇ toRenameᵗ (keep (skip (skip (CTI2.ηᴸʷ W)))) X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


target-split★₃-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (B : Ty (suc Δᴿ))
  → substᵗ splitTarget★₃
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
    ≡ CTI2.embedᴿ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      (substᵗ Λ⊑Λ²TargetSplit₂ B)
target-split★₃-eq W B =
  trans (substᵗ-rename splitTarget★₃ (toRenameᵗ (keep (CTI2.ηᴿʷ W))) B)
    (trans (substᵗ-cong B var-eq)
      (sym (renameᵗ-subst
        (toRenameᵗ (skip (keep (keep (CTI2.ηᴿʷ W)))))
        Λ⊑Λ²TargetSplit₂ B)))
  where
  var-eq : ∀ X
    → splitTarget★₃ (toRenameᵗ (keep (CTI2.ηᴿʷ W)) X)
      ≡ renameᵗ
          (toRenameᵗ (skip (keep (keep (CTI2.ηᴿʷ W)))))
          (Λ⊑Λ²TargetSplit₂ X)
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


Λ-final-body-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B
Λ-final-body-⊑ᵂ {W = W} {A = A} {B = B} body-p =
  subst≡
    (λ L → CTI2.impEnvʷ Wout ⊢ L ⊑
      CTI2.embedᴿ Wout (substᵗ Λ⊑Λ²TargetSplit₂ B))
    (source-split₃-eq W A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wout ⊢
        substᵗ splitSource₃
          (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
        ⊑ R)
      (target-split★₃-eq W B)
      (subst₂-⊑ split★-same split★-star body-p))
  where
  Wout =
    CTI2.liftWorldLeft I.X⊑★
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))


source-inner₃-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (A : Ty (suc Δᴸ))
  → renameᵗ innerρ₃
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
    ≡ CTI2.embedᴸ (ΛPostMidWorld W) A
source-inner₃-eq W A =
  trans (renameᵗ-comp (toRenameᵗ (keep (CTI2.ηᴸʷ W))) innerρ₃ A)
    (renameᵗ-cong A var-eq)
  where
  var-eq : ∀ X
    → innerρ₃ (toRenameᵗ (keep (CTI2.ηᴸʷ W)) X)
      ≡ toRenameᵗ (skip (skip (keep (CTI2.ηᴸʷ W)))) X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


target-inner₃-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) (B : Ty (suc Δᴿ))
  → renameᵗ innerρ₃
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
    ≡ CTI2.embedᴿ (ΛPostMidWorld W)
        (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
          (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B))
target-inner₃-eq W B =
  trans
    (renameᵗ-comp (toRenameᵗ (keep (CTI2.ηᴿʷ W))) innerρ₃ B)
    (trans (renameᵗ-cong B var-eq)
      (trans (sym (renameᵗ-comp Fin.suc
        (toRenameᵗ (skip (keep (keep (CTI2.ηᴿʷ W))))) B))
        (sym (cong (CTI2.embedᴿ (ΛPostMidWorld W))
          (inner-reveal-target-eq B)))))
  where
  var-eq : ∀ X
    → innerρ₃ (toRenameᵗ (keep (CTI2.ηᴿʷ W)) X)
      ≡ toRenameᵗ (skip (keep (keep (CTI2.ηᴿʷ W)))) (Fin.suc X)
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) = refl


Λ-inner-body-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ ΛPostMidWorld W ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
        (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
Λ-inner-body-⊑ᵂ {W = W} {A = A} {B = B} body-p =
  subst≡
    (λ L → CTI2.impEnvʷ (ΛPostMidWorld W) ⊢ L ⊑
      CTI2.embedᴿ (ΛPostMidWorld W)
        (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
          (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)))
    (source-inner₃-eq W A)
    (subst≡
      (λ R → CTI2.impEnvʷ (ΛPostMidWorld W) ⊢
        renameᵗ innerρ₃
          (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
        ⊑ R)
      (target-inner₃-eq W B)
      (rename-⊑ innerρ₃ innerρ₃-injective innerρ₃-star-map body-p))


Λ-inner-body-⊑ᵂ-applyBody : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ ΛPostMidWorld W ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) (applyBody (bind ★) B)
Λ-inner-body-⊑ᵂ-applyBody {W = W} {A = A} {B = B} body-p =
  subst≡
    (λ C → A CTI2.⊑ᵂ⟨ ΛPostMidWorld W ⟩ C)
    (sym (cong (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)))
      (applyBody-bind★-eq B)))
    (Λ-inner-body-⊑ᵂ {W = W} {A = A} {B = B} body-p)


Λ⊑Λ²-post-body-transport : Λ⊑Λ²PostBodyTransportᵀ
Λ⊑Λ²-post-body-transport {Δᴿ = Δᴿ} {W = W} {γ = γ} {γᴮ = γᴮ}
    {V = V} {V′ = V′} {A = A} {B = B} {body-p = body-p}
    ext₂ Anv zero∈A liftγ vV vV′ bodyRel
    with Λ⊑Λ²-route1-prefix bodyRel
Λ⊑Λ²-post-body-transport {Δᴿ = Δᴿ} {W = W} {γ = γ}
    {γᴮ = γᴮ}
    {V = V} {V′ = V′} {A = A} {B = B} {body-p = body-p}
    ext₂ Anv zero∈A liftγ vV vV′ bodyRel
  | pᵇ , relFreshRoute =
  γout , body-p₂ , top-p₂ ,
  liftOut , postVal , post⊢ , relOut
  where
  Wfresh =
    TBL.ΛLiftToBindFreshWorld I.X⊑★ W

  Wmid =
    ΛPostMidWorld W

  Wout =
    CTI2.liftWorldLeft I.X⊑★
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))

  γfresh = Λ-route1-fresh-ctx liftγ
  γmid = Λ-route1-mid-ctx liftγ
  γout = Λ-route1-out-ctx liftγ

  Bpre : Ty (suc (suc Δᴿ))
  Bpre = applyBody (bind ★) B

  Bmid : Ty (suc (suc Δᴿ))
  Bmid = replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) Bpre

  BouterIn : Ty (suc (suc Δᴿ))
  BouterIn = renameᵗ Fin.suc B

  BouterOut : Ty (suc (suc Δᴿ))
  BouterOut = renameᵗ Fin.suc (replaceTy Fin.zero ★ B)

  B₂ : Ty (suc (suc Δᴿ))
  B₂ = substᵗ Λ⊑Λ²TargetSplit₂ B

  cInner = 〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑ Bpre 〗

  cOuter = rename↑ Fin.suc (〖 Fin.zero , ★ ↑ B 〗)

  post₁ : CT.Term (suc (suc Δᴿ))
  post₁ = CT.renameᵗᵐ (keep wk↪ᵗ) V′ ↑ cInner

  post : CT.Term (suc (suc Δᴿ))
  post = post₁ ↑ cOuter

  pᵇBody : A CTI2.⊑ᵂ⟨ Wfresh ⟩ Bpre
  pᵇBody =
    subst≡ (λ C → A CTI2.⊑ᵂ⟨ Wfresh ⟩ C)
      (sym (applyBody-bind★-eq B)) pᵇ

  relFreshRouteCtx : Wfresh CTI2.∣ γfresh
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
  relFreshRouteCtx =
    subst≡
      (λ γᶠ → Wfresh CTI2.∣ γᶠ
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ)
      (Λ-route1-ctx-fresh-eq liftγ)
      relFreshRoute

  relFresh : Wfresh CTI2.∣ γfresh
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇBody
  relFresh =
    rel-target-transportᴿ (sym (applyBody-bind★-eq B))
      pᵇ relFreshRouteCtx

  rawAnv : NonVar
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
  rawAnv = renameNonVar (toRenameᵗ (keep (CTI2.ηᴸʷ W))) Anv

  rawBnv : NonVar
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
  rawBnv = source-nonvar-target body-p rawAnv

  Bnv : NonVar B
  Bnv = unrenameNonVar (toRenameᵗ (keep (CTI2.ηᴿʷ W))) rawBnv

  rawSrcOcc :
      toRenameᵗ (keep (CTI2.ηᴸʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A
  rawSrcOcc =
    rename-occurs (toRenameᵗ (keep (CTI2.ηᴸʷ W))) zero∈A

  rawTgtOcc :
      toRenameᵗ (keep (CTI2.ηᴿʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B
  rawTgtOcc =
    source-occurs-target refl body-p rawSrcOcc

  zero∈B : Fin.zero ∈ᵗ B
  zero∈B =
    PIC.unrename-occurs
      (toRenameᵗ (keep (CTI2.ηᴿʷ W)))
      (toRenameᵗ-injective (keep (CTI2.ηᴿʷ W)))
      rawTgtOcc

  Bpre-nv : NonVar Bpre
  Bpre-nv = renameNonVar (extᵗ Fin.suc) Bnv

  Bpre-zero∈ : Fin.zero ∈ᵗ Bpre
  Bpre-zero∈ =
    rename-occurs (extᵗ Fin.suc) zero∈B

  Bouter-nv : NonVar BouterIn
  Bouter-nv = renameNonVar Fin.suc Bnv

  Bouter-zero∈ : Fin.suc Fin.zero ∈ᵗ BouterIn
  Bouter-zero∈ = rename-occurs Fin.suc zero∈B

  cInner⊢ :
      CTI2.targetStoreʷ Wmid CTI2.⊢↑[ just Fin.zero ] cInner
  cInner⊢ =
    generated-reveal-⊢↑-present Bpre-zero∈ (Z∋ refl)

  cOuter⊢ :
      CTI2.targetStoreʷ Wout
        CTI2.⊢↑[ just (Fin.suc Fin.zero) ] cOuter
  cOuter⊢ =
    TE.reveal-renameˣ StoreRename-suc-bind
      (generated-reveal-⊢↑-present zero∈B (Z∋ refl))

  rvInner : RevealValue cInner
  rvInner = generated-reveal-value Bpre-nv Bpre-zero∈

  rvOuter : RevealValue cOuter
  rvOuter =
    reveal-value-rename Fin.suc
      (generated-reveal-value Bnv zero∈B)

  postVal : Value post
  postVal =
    (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV′ ↑ rvInner) ↑ rvOuter

  qInner : A CTI2.⊑ᵂ⟨ Wmid ⟩ Bmid
  qInner = Λ-inner-body-⊑ᵂ-applyBody {W = W} {A = A} {B = B} body-p

  relMid : Wmid CTI2.∣ γmid ⊢² V ⊑ post₁ ∶ qInner
  relMid =
    CTI2.⊑reveal² (Λ-mid-fresh-mono W) (Λ-inner-rebaseᴿ W)
      (Λ-route1-mid-fresh-same liftγ) cInner⊢ relFresh qInner

  relMidOuterPrem : Wmid CTI2.∣ γmid
      ⊢² V ⊑ post₁ ∶
        subst≡ (λ C → A CTI2.⊑ᵂ⟨ Wmid ⟩ C)
          (inner-reveal-target-eq-applyBody B) qInner
  relMidOuterPrem =
    rel-target-transportᴿ (inner-reveal-target-eq-applyBody B) qInner relMid

  body-p₂ : A CTI2.⊑ᵂ⟨ Wout ⟩ B₂
  body-p₂ = Λ-final-body-⊑ᵂ {W = W} {A = A} {B = B} body-p

  qOuter : A CTI2.⊑ᵂ⟨ Wout ⟩ BouterOut
  qOuter =
    subst≡ (λ C → A CTI2.⊑ᵂ⟨ Wout ⟩ C)
      (sym (outer-reveal-target-eq B))
      body-p₂

  relOutConv : Wout CTI2.∣ γout ⊢² V ⊑ post ∶ qOuter
  relOutConv =
    CTI2.⊑reveal² (Λ-out-mid-mono W) (Λ-outer-rebaseᴿ W)
      (Λ-route1-out-mid-same liftγ) cOuter⊢ relMidOuterPrem qOuter

  relOut : Wout CTI2.∣ γout ⊢² V ⊑ post ∶ body-p₂
  relOut =
    TBL.⊢²-retarget {q = body-p₂}
      (rel-target-transportᴿ
        {W = Wout} {γ = γout} {M = V} {N = post}
        {A = A} {B = BouterOut} {B′ = B₂}
        (outer-reveal-target-eq B)
        qOuter relOutConv)

  top-p₂ : `∀ A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
    ⟩ B₂
  top-p₂ =
    subst≡
      (λ L → CTI2.impEnvʷ Wbase₂ ⊢ `∀ L
        ⊑ CTI2.embedᴿ Wbase₂ B₂)
      (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ Wbase₂)))
      (I.∀⊑
        (renameNonVar
          (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) Anv)
        (rename-occurs
          (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) zero∈A)
        (subst≡
          (λ R → I.instᵐ (CTI2.impEnvʷ Wbase₂)
            ⊢ renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) A
              ⊑ R)
          (target-left-lift-eq (CTI2.ηᴿʷ Wbase₂) B₂)
          body-p₂))
    where
    Wbase₂ =
      CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)

  liftOut : CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ) γout
  liftOut = Λ-route1-out-liftCtxᴸ ext₂ liftγ

  post⊢ :
      ⟨ suc (suc Δᴿ) ,
        CTI2.targetStoreʷ
          (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★)
            (＇ Fin.zero)) ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
      ⊢ post ⦂ B₂
  post⊢ =
    subst≡
      (λ Γ → ⟨ _ , CTI2.targetStoreʷ
          (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★)
            (＇ Fin.zero)) , Γ ⟩
        ⊢ post ⦂ B₂)
      (liftCtxᴸ-target liftOut)
      (CTI2T.target-typing² relOut)


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
      (InstPostCatalogPackageAt.at-residual-q pkg)
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
      (TBL.⊢²-retarget
        {q = ECR.transport⊑ᵂ ext′ (ECR.transport⊑ᵂ ext₂ q)}
        (rel-target-transportᴿ
          (cong (applyTys ψs)
            (InstPostCatalogPackageAt.at-residual-target-eq pkg))
          (ECR.transport⊑ᵂ ext′
            (InstPostCatalogPackageAt.at-residual-q pkg))
          rel′)))


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


Λ⊑²-smart-fresh-world : ∀ {Δᴸ Δᴿ Δ}
  → CTI2.World Δᴸ Δᴿ Δ
  → CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
Λ⊑²-smart-fresh-world W =
  CTI2.rightOnlyWorld
    (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) ★)
    (＇ Fin.zero)


Λ⊑²-smart-front-world : ∀ {Δᴸ Δᴿ Δ}
  → CTI2.World Δᴸ Δᴿ Δ
  → CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
Λ⊑²-smart-front-world W =
  CTI2.liftWorldLeft I.X⊑★
    (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))


Λ⊑²-smart-fresh-oldCenters : ∀ {Δ}
  → suc (suc Δ) ↪ᵗ suc (suc (suc Δ))
Λ⊑²-smart-fresh-oldCenters = keep (keep (skip id↪ᵗ))


Λ⊑²-smart-fresh-subst : ∀ {Δ}
  → TyVar (suc (suc (suc Δ)))
  → Ty (suc (suc (suc Δ)))
Λ⊑²-smart-fresh-subst Fin.zero = ＇ (Fin.suc (Fin.suc Fin.zero))
Λ⊑²-smart-fresh-subst (Fin.suc Fin.zero) = ＇ Fin.zero
Λ⊑²-smart-fresh-subst (Fin.suc (Fin.suc Fin.zero)) =
  ＇ (Fin.suc Fin.zero)
Λ⊑²-smart-fresh-subst (Fin.suc (Fin.suc (Fin.suc Z))) =
  ＇ (Fin.suc (Fin.suc (Fin.suc Z)))


Λ⊑²-smart-fresh-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ∀ Z
  → CTI2.impEnvʷ
      (CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))
      Z ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W))
      (Λ⊑²-smart-fresh-subst Z) ★
Λ⊑²-smart-fresh-star Fin.zero eq = I.X⊑★ refl
Λ⊑²-smart-fresh-star (Fin.suc Fin.zero) eq = I.X⊑★ refl
Λ⊑²-smart-fresh-star (Fin.suc (Fin.suc Fin.zero)) eq =
  I.X⊑★ refl
Λ⊑²-smart-fresh-star (Fin.suc (Fin.suc (Fin.suc Z))) eq =
  I.X⊑★ eq


Λ⊑²-smart-fresh-source-point : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ X
  → Λ⊑²-smart-fresh-subst
      (toRenameᵗ
        (CTI2.ηᴸʷ
          (CTI2.liftWorldLeft I.X⊑★
            (CTI2.rightOnlyWorld
              (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))) X)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W)) X)
Λ⊑²-smart-fresh-source-point W Fin.zero = refl
Λ⊑²-smart-fresh-source-point W (Fin.suc X) = refl


Λ⊑²-smart-fresh-target-point : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Y
  → Λ⊑²-smart-fresh-subst
      (toRenameᵗ
        (CTI2.ηᴿʷ
          (CTI2.liftWorldLeft I.X⊑★
            (CTI2.rightOnlyWorld
              (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)))) Y)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W)) Y)
Λ⊑²-smart-fresh-target-point W Fin.zero = refl
Λ⊑²-smart-fresh-target-point W (Fin.suc Fin.zero) = refl
Λ⊑²-smart-fresh-target-point W (Fin.suc (Fin.suc Y)) = refl


Λ⊑²-smart-fresh-source-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) C
  → substᵗ Λ⊑²-smart-fresh-subst
      (CTI2.embedᴸ
        (CTI2.liftWorldLeft I.X⊑★
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) C)
    ≡ CTI2.embedᴸ (Λ⊑²-smart-fresh-world W) C
Λ⊑²-smart-fresh-source-eq W C =
  trans (substᵗ-rename Λ⊑²-smart-fresh-subst
      (toRenameᵗ
        (CTI2.ηᴸʷ
          (CTI2.liftWorldLeft I.X⊑★
            (CTI2.rightOnlyWorld
              (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))))) C)
    (trans (substᵗ-cong C (Λ⊑²-smart-fresh-source-point W))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W))) C))


Λ⊑²-smart-fresh-target-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) C
  → substᵗ Λ⊑²-smart-fresh-subst
      (CTI2.embedᴿ
        (CTI2.liftWorldLeft I.X⊑★
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) C)
    ≡ CTI2.embedᴿ (Λ⊑²-smart-fresh-world W) C
Λ⊑²-smart-fresh-target-eq W C =
  trans (substᵗ-rename Λ⊑²-smart-fresh-subst
      (toRenameᵗ
        (CTI2.ηᴿʷ
          (CTI2.liftWorldLeft I.X⊑★
            (CTI2.rightOnlyWorld
              (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))))) C)
    (trans (substᵗ-cong C (Λ⊑²-smart-fresh-target-point W))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W))) C))


Λ⊑²-smart-fresh-transport : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
  → A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★
        (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
    ⟩ B
  → A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B
Λ⊑²-smart-fresh-transport {W = W} {A = A} {B = B} p =
  subst≡
    (λ L → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W) ⊢ L ⊑
      CTI2.embedᴿ (Λ⊑²-smart-fresh-world W) B)
    (Λ⊑²-smart-fresh-source-eq W A)
    (subst≡
      (λ R → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W) ⊢
        substᵗ Λ⊑²-smart-fresh-subst
          (CTI2.embedᴸ
            (CTI2.liftWorldLeft I.X⊑★
              (CTI2.rightOnlyWorld
                (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) A)
        ⊑ R)
      (Λ⊑²-smart-fresh-target-eq W B)
      (subst-⊑ (Λ⊑²-smart-fresh-star {W = W}) p))


Λ⊑²-smart-front-subst : ∀ {Δ}
  → TyVar (suc (suc (suc Δ)))
  → Ty (suc (suc (suc Δ)))
Λ⊑²-smart-front-subst Fin.zero = ＇ (Fin.suc Fin.zero)
Λ⊑²-smart-front-subst (Fin.suc Fin.zero) =
  ＇ (Fin.suc (Fin.suc Fin.zero))
Λ⊑²-smart-front-subst (Fin.suc (Fin.suc Fin.zero)) = ＇ Fin.zero
Λ⊑²-smart-front-subst (Fin.suc (Fin.suc (Fin.suc Z))) =
  ＇ (Fin.suc (Fin.suc (Fin.suc Z)))


Λ⊑²-smart-front-star : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ∀ Z
  → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W) Z ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ (Λ⊑²-smart-front-world W))
      (Λ⊑²-smart-front-subst Z) ★
Λ⊑²-smart-front-star Fin.zero eq = I.X⊑★ refl
Λ⊑²-smart-front-star (Fin.suc Fin.zero) eq = I.X⊑★ refl
Λ⊑²-smart-front-star (Fin.suc (Fin.suc Fin.zero)) eq =
  I.X⊑★ refl
Λ⊑²-smart-front-star (Fin.suc (Fin.suc (Fin.suc Z))) eq =
  I.X⊑★ eq


Λ⊑²-smart-front-source-point : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ X
  → Λ⊑²-smart-front-subst
      (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W)) X)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-front-world W)) X)
Λ⊑²-smart-front-source-point W Fin.zero = refl
Λ⊑²-smart-front-source-point W (Fin.suc X) = refl


Λ⊑²-smart-front-target-point : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Y
  → Λ⊑²-smart-front-subst
      (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W)) Y)
    ≡ ＇ (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-front-world W)) Y)
Λ⊑²-smart-front-target-point W Fin.zero = refl
Λ⊑²-smart-front-target-point W (Fin.suc Fin.zero) = refl
Λ⊑²-smart-front-target-point W (Fin.suc (Fin.suc Y)) = refl


Λ⊑²-smart-front-source-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) C
  → substᵗ Λ⊑²-smart-front-subst
      (CTI2.embedᴸ (Λ⊑²-smart-fresh-world W) C)
    ≡ CTI2.embedᴸ (Λ⊑²-smart-front-world W) C
Λ⊑²-smart-front-source-eq W C =
  trans (substᵗ-rename Λ⊑²-smart-front-subst
      (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W))) C)
    (trans (substᵗ-cong C (Λ⊑²-smart-front-source-point W))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-front-world W))) C))


Λ⊑²-smart-front-target-eq : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) C
  → substᵗ Λ⊑²-smart-front-subst
      (CTI2.embedᴿ (Λ⊑²-smart-fresh-world W) C)
    ≡ CTI2.embedᴿ (Λ⊑²-smart-front-world W) C
Λ⊑²-smart-front-target-eq W C =
  trans (substᵗ-rename Λ⊑²-smart-front-subst
      (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W))) C)
    (trans (substᵗ-cong C (Λ⊑²-smart-front-target-point W))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-front-world W))) C))


Λ⊑²-smart-fresh-untransport : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
  → A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B
  → A CTI2.⊑ᵂ⟨ Λ⊑²-smart-front-world W ⟩ B
Λ⊑²-smart-fresh-untransport {W = W} {A = A} {B = B} p =
  subst≡
    (λ L → CTI2.impEnvʷ (Λ⊑²-smart-front-world W) ⊢ L ⊑
      CTI2.embedᴿ (Λ⊑²-smart-front-world W) B)
    (Λ⊑²-smart-front-source-eq W A)
    (subst≡
      (λ R → CTI2.impEnvʷ (Λ⊑²-smart-front-world W) ⊢
        substᵗ Λ⊑²-smart-front-subst
          (CTI2.embedᴸ (Λ⊑²-smart-fresh-world W) A)
        ⊑ R)
      (Λ⊑²-smart-front-target-eq W B)
      (subst-⊑ (Λ⊑²-smart-front-star {W = W}) p))


Λ⊑²-smart-fresh-top : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B
  → `∀ A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
    ⟩ B
Λ⊑²-smart-fresh-top {W = W} {A = A} {B = B} Anv zero∈A p =
  subst≡
    (λ L → CTI2.impEnvʷ Wbase₂ ⊢ `∀ L
      ⊑ CTI2.embedᴿ Wbase₂ B)
    (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ Wbase₂)))
    (I.∀⊑
      (renameNonVar
        (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) Anv)
      (rename-occurs
        (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) zero∈A)
      (subst≡
        (λ R → I.instᵐ (CTI2.impEnvʷ Wbase₂)
          ⊢ renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ Wbase₂))) A
            ⊑ R)
        (target-left-lift-eq (CTI2.ηᴿʷ Wbase₂) B)
        (Λ⊑²-smart-fresh-untransport {W = W} p)))
  where
  Wbase₂ =
    CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)


Λ⊑²-smart-fresh-catchup⁻ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B B′ : Ty (suc (suc Δᴿ))}
    {ν : Env∼ (suc (suc Δᴿ))}
    {p : A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B}
    {c : ν ⊢ B ∼ B′}
    {q : A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B′}
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → CatchupCast⁻ {W = Λ⊑²-smart-fresh-world W} {A = A} p c q
  → CatchupCast⁻
      {W = CTI2.rightOnlyWorld
        (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)}
      {A = `∀ A}
      (Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p)
      c
      (Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q)
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    (catchup⁻-inert i) =
  catchup⁻-inert {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q} i
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    (catchup⁻-id a) =
  catchup⁻-id {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q} a
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    (catchup⁻-ground-other B≢G r k) =
  catchup⁻-ground-other
    {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q} B≢G
    (Λ⊑²-smart-fresh-top {W = W} Anv zero∈A r)
    (Λ⊑²-smart-fresh-catchup⁻ {W = W} Anv zero∈A k)
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    catchup⁻-inst =
  catchup⁻-inst {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q}
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    catchup⁻-bot-elim =
  catchup⁻-bot-elim
    {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q}
Λ⊑²-smart-fresh-catchup⁻ {W = W} {p = p} {q = q} Anv zero∈A
    catchup⁻-bot-intro =
  catchup⁻-bot-intro
    {p = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A p}
    {q = Λ⊑²-smart-fresh-top {W = W} Anv zero∈A q}


Λ⊑²-smart-fresh-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W)) Xᴿ
    ≡ toRenameᵗ Λ⊑²-smart-fresh-oldCenters
        (toRenameᵗ (CTI2.ηᴿʷ
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) Xᴿ)
Λ⊑²-smart-fresh-target-frozen W Fin.zero = refl
Λ⊑²-smart-fresh-target-frozen W (Fin.suc Fin.zero) = refl
Λ⊑²-smart-fresh-target-frozen W (Fin.suc (Fin.suc Xᴿ)) =
  cong (λ Z → Fin.suc (Fin.suc (Fin.suc Z)))
    (sym (toRename-id-eq (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)))


Λ⊑²-smart-fresh-old-source-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴸ
  → toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W)) (Fin.suc Xᴸ)
    ≡ toRenameᵗ Λ⊑²-smart-fresh-oldCenters
        (toRenameᵗ (CTI2.ηᴸʷ
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) Xᴸ)
Λ⊑²-smart-fresh-old-source-frozen W Xᴸ =
  cong (λ Z → Fin.suc (Fin.suc (Fin.suc Z)))
    (sym (toRename-id-eq (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))


Λ⊑²-smart-fresh-not-target : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W)) Xᴿ
    ≢ toRenameᵗ (CTI2.ηᴸʷ (Λ⊑²-smart-fresh-world W)) Fin.zero
Λ⊑²-smart-fresh-not-target W Fin.zero ()
Λ⊑²-smart-fresh-not-target W (Fin.suc Fin.zero) ()
Λ⊑²-smart-fresh-not-target W (Fin.suc (Fin.suc Xᴿ)) ()


Λ⊑²-smart-fresh-old-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Z
  → CTI2.impEnvʷ
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      Z
    ≡ I.X⊑★
  → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W)
      (toRenameᵗ Λ⊑²-smart-fresh-oldCenters Z)
    ≡ I.X⊑★
Λ⊑²-smart-fresh-old-mark-mono W Fin.zero old-star = refl
Λ⊑²-smart-fresh-old-mark-mono W (Fin.suc Fin.zero) old-star = refl
Λ⊑²-smart-fresh-old-mark-mono W (Fin.suc (Fin.suc Z)) old-star =
  subst≡
    (λ Y → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W)
      (Fin.suc (Fin.suc (Fin.suc Y))) ≡ I.X⊑★)
    (sym (toRename-id-eq Z))
    old-star


Λ⊑²-smart-fresh-target-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → CTI2.impEnvʷ
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (toRenameᵗ
        (CTI2.ηᴿʷ
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) Xᴿ)
    ≡ I.X⊑★
  → CTI2.impEnvʷ (Λ⊑²-smart-fresh-world W)
      (toRenameᵗ (CTI2.ηᴿʷ (Λ⊑²-smart-fresh-world W)) Xᴿ)
    ≡ I.X⊑★
Λ⊑²-smart-fresh-target-mark-mono W Fin.zero eq = refl
Λ⊑²-smart-fresh-target-mark-mono W (Fin.suc Fin.zero) eq = refl
Λ⊑²-smart-fresh-target-mark-mono W (Fin.suc (Fin.suc Xᴿ)) eq = eq


Λ⊑²-smart-fresh-guard : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.SmartFreshBehindGuard
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (Λ⊑²-smart-fresh-world W)
Λ⊑²-smart-fresh-guard {W = W} =
    CTI2.smart-fresh-behind-guard
    Λ⊑²-smart-fresh-oldCenters
    refl refl
    (λ {A} {B} p →
      Λ⊑²-smart-fresh-transport {W = W} {A = A} {B = B} p)
    (Λ⊑²-smart-fresh-old-mark-mono W)
    (Λ⊑²-smart-fresh-target-frozen W)
    (Λ⊑²-smart-fresh-old-source-frozen W)
    (Λ⊑²-smart-fresh-not-target W)
    refl
    (Λ⊑²-smart-fresh-target-mark-mono W)


mapCtxᴿ-liftᴸ : MapCtxᴿLiftᴸᵀ right-bind-under-left-lift
mapCtxᴿ-liftᴸ ext CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
mapCtxᴿ-liftᴸ ext (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (mapCtxᴿ-liftᴸ ext liftγ)


mapCtxᴿ-smart-fresh-liftᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
  → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
  → CTI2.SmartLiftCtxᴸ
      {W = CTI2.rightOnlyWorld
        (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)}
      {Wᵐ = Λ⊑²-smart-fresh-world W}
      (ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = W} {B = ★} {C = ＇ Fin.zero})
        γ)
      (ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = CTI2.liftWorldLeft I.X⊑★ W}
          {B = ★} {C = ＇ Fin.zero})
        γᴸ)
mapCtxᴿ-smart-fresh-liftᴸ CTI2.liftᴸ-[] = CTI2.smart-lift-[]
mapCtxᴿ-smart-fresh-liftᴸ (CTI2.liftᴸ-∷ liftγ) =
  CTI2.smart-lift-∷ (mapCtxᴿ-smart-fresh-liftᴸ liftγ)


mapCtxᴿ-smart-fresh-target-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
  → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
  → CTI2.tgtCtxʷ
      (ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = CTI2.liftWorldLeft I.X⊑★ W}
          {B = ★} {C = ＇ Fin.zero})
        γᴸ)
    ≡ CTI2.tgtCtxʷ
      (ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = W} {B = ★} {C = ＇ Fin.zero})
        γ)
mapCtxᴿ-smart-fresh-target-ctx CTI2.liftᴸ-[] = refl
mapCtxᴿ-smart-fresh-target-ctx (CTI2.liftᴸ-∷ liftγ) =
  cong (_ ∷_) (mapCtxᴿ-smart-fresh-target-ctx liftγ)


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


Λ⊑²-smart-fresh-at-rewrap : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {V : CT.Term (suc Δᴸ)} {post : CT.Term (suc (suc Δᴿ))}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
    {body-p : A CTI2.⊑ᵂ⟨ Λ⊑²-smart-fresh-world W ⟩ B}
    {top-p : `∀ A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
    ⟩ B}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → (liftγ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → Value V
  → Λ⊑²-smart-fresh-world W
      CTI2.∣
      ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = CTI2.liftWorldLeft I.X⊑★ W}
          {B = ★} {C = ＇ Fin.zero})
        γᴸ
      ⊢² V ⊑ post ∶ body-p
  → CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
      CTI2.∣
      ECR.mapCtxᴿ
        (right-bind-right-bind-world-extendᴿ
          {W = W} {B = ★} {C = ＇ Fin.zero})
        γ
      ⊢² Λ V ⊑ post ∶ top-p
Λ⊑²-smart-fresh-at-rewrap {W = W} Anv zero∈A liftγ vV bodyRel =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (CTI2.smart-fresh-behind (Λ⊑²-smart-fresh-guard {W = W}))
    (mapCtxᴿ-smart-fresh-liftᴸ liftγ)
    vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (mapCtxᴿ-smart-fresh-target-ctx liftγ)
      (CTI2T.target-typing² bodyRel))
    bodyRel
    _


Λ⊑²-smart-recursive-package-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vΛV : CT.Value (Λ V))
  → (vΛV′ : CT.Value (Λ V′))
  → (vV : CT.Value V)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (body-q : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ B′)
  → (q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → (liftγ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (bodyRel : CTI2.liftWorldLeft I.X⊑★ W CTI2.∣ γᴸ
      ⊢² V ⊑ Λ V′ ∶ body-p)
  → InstPostCatalogPackageAt fuel bodyRel vV vΛV′ c′
      B′≢★ c<fuel body-q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (Λ⊑²-smart-fresh-world W)
      (right-bind-right-bind-world-extendᴿ
        {W = CTI2.liftWorldLeft I.X⊑★ W}
        {B = ★} {C = ＇ Fin.zero})
  → InstPostCatalogPackageAt fuel rel vΛV vΛV′ c′
      B′≢★ c<fuel q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (right-bind-right-bind-world-extendᴿ
        {W = W} {B = ★} {C = ＇ Fin.zero})
Λ⊑²-smart-recursive-package-at {W = W}
    rel vΛV vΛV′ vV c′ B′≢★ c<fuel body-q q
    liftγ Anv zero∈A bodyRel bodyPkg =
  record
    { at-B₂ = InstPostCatalogPackageAt.at-B₂ bodyPkg
    ; at-post = InstPostCatalogPackageAt.at-post bodyPkg
    ; at-p₂ =
        Λ⊑²-smart-fresh-top {W = W} Anv zero∈A
          (InstPostCatalogPackageAt.at-p₂ bodyPkg)
    ; at-post-relation =
        Λ⊑²-smart-fresh-at-rewrap Anv zero∈A liftγ vV
          (InstPostCatalogPackageAt.at-post-relation bodyPkg)
    ; at-post-value = InstPostCatalogPackageAt.at-post-value bodyPkg
    ; at-ν₂ = InstPostCatalogPackageAt.at-ν₂ bodyPkg
    ; at-residual-target =
        InstPostCatalogPackageAt.at-residual-target bodyPkg
    ; at-residual-q =
        Λ⊑²-smart-fresh-top {W = W} Anv zero∈A
          (InstPostCatalogPackageAt.at-residual-q bodyPkg)
    ; at-residual-target-eq =
        InstPostCatalogPackageAt.at-residual-target-eq bodyPkg
    ; at-residual-cast =
        InstPostCatalogPackageAt.at-residual-cast bodyPkg
    ; at-residual-provenance =
        Λ⊑²-smart-fresh-catchup⁻ {W = W} Anv zero∈A
          (InstPostCatalogPackageAt.at-residual-provenance bodyPkg)
    ; at-residual-fuel =
        InstPostCatalogPackageAt.at-residual-fuel bodyPkg
    ; at-prefix-reduction =
        InstPostCatalogPackageAt.at-prefix-reduction bodyPkg
    ; at-spine-descent =
        spine-descent-zero
          (InstPostCatalogPackageAt.at-post-value bodyPkg)
          (Λ⊑²-smart-fresh-at-rewrap Anv zero∈A liftγ vV
            (InstPostCatalogPackageAt.at-post-relation bodyPkg))
    }


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


Λ⊑Λ²-prefix-reduction : ∀ {Δ} {V′ : CT.Term (suc Δ)}
    {B : Ty (suc Δ)} {B′ : Ty Δ} {ν : Env∼ Δ}
    {c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → Value V′
  → (B′≢★ : B′ ≢ ★)
  → (Λ V′) ⟨ (inst c′) B′≢★ ⟩
      —↠[ bind ★ ∷ bind {Δ = suc Δ} (＇ (Fin.zero {n = Δ})) ∷ [] ]
    ((CT.renameᵗᵐ (keep wk↪ᵗ) V′ ↑
        〖 Fin.zero , ⇑ᵗ (＇ (Fin.zero {n = Δ})) ↑
          Λ⊑Λ²BodyAfter★ B 〗)
      ↑ rename↑ Fin.suc (〖 (Fin.zero {n = Δ}) , ★ ↑ B 〗))
      ⟨ applyConsistency (bind {Δ = suc Δ} (＇ (Fin.zero {n = Δ})))
          (↑ᶜ (close-instᶜ c′)) ⟩
Λ⊑Λ²-prefix-reduction {Δ = Δ} {V′ = V′} {B = B} {c′ = c′}
    vV′ B′≢★ =
  (Λ V′) ⟨ (inst c′) B′≢★ ⟩
    —→[ bind ★ ]⟨ β-inst (CT.Λ vV′) B′≢★ ⟩
  ((_⦂∀_[_] {Δ = suc Δ}
      (Λ (CT.renameᵗᵐ (keep wk↪ᵗ) V′))
      (Λ⊑Λ²BodyAfter★ B)
      (＇ (Fin.zero {n = Δ}))
    ↑ 〖 (Fin.zero {n = Δ}) , ★ ↑ B 〗)
    ⟨ ↑ᶜ (close-instᶜ c′) ⟩)
    —→[ bind {Δ = suc Δ} (＇ (Fin.zero {n = Δ})) ]⟨ ξ-⟨⟩
      (ξ-reveal
        (β-Λ (renameᵗᵐ-preserves-Value (keep wk↪ᵗ) vV′))
        refl)
      refl ⟩
  ((CT.renameᵗᵐ (keep wk↪ᵗ) V′ ↑
      〖 Fin.zero , ⇑ᵗ (＇ (Fin.zero {n = Δ})) ↑
        Λ⊑Λ²BodyAfter★ B 〗)
    ↑ rename↑ Fin.suc (〖 (Fin.zero {n = Δ}) , ★ ↑ B 〗))
    ⟨ applyConsistency (bind {Δ = suc Δ} (＇ (Fin.zero {n = Δ})))
        (↑ᶜ (close-instᶜ c′)) ⟩ ∎[]


Λ⊑Λ²-base-package-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → inst-alloc-decreaseᵀ
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vΛV : CT.Value (Λ V))
  → (vΛV′ : CT.Value (Λ V′))
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : `∀ A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → InstPostCatalogPackageAt fuel rel vΛV vΛV′
      c′ B′≢★ c<fuel q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      right-bind-right-bind-world-extendᴿ
Λ⊑Λ²-base-package-at {fuel = fuel} {Δᴿ = Δᴿ} {W = W} {V′ = V′}
    {A = A} {B = B} {B′ = B′}
    fuel-step catchup⁻-embed inst-decrease rel
    vΛV vΛV′ vV vV′ c′ B′≢★ c<fuel q liftγ Anv zero∈A
    bodyRel
    with Λ⊑Λ²-post-body-transport
      right-bind-right-bind-world-extendᴿ Anv zero∈A
      liftγ vV vV′ bodyRel
Λ⊑Λ²-base-package-at {fuel = fuel} {Δᴿ = Δᴿ} {W = W} {V′ = V′}
    {A = A} {B = B} {B′ = B′}
    fuel-step catchup⁻-embed inst-decrease rel
    vΛV vΛV′ vV vV′ c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ c<fuel q liftγ Anv zero∈A
    bodyRel
  | γ₂ᴸ , body-p₂ , top-p₂ ,
    liftγ₂ , vPost , post⊢ , bodyRel₂ =
  record
    { at-B₂ = ΛResidualSource₂ B
    ; at-post = Λ⊑Λ²PostTerm V′ B
    ; at-p₂ =
        subst≡ (λ C → `∀ A CTI2.⊑ᵂ⟨
            CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
          ⟩ C)
          (residual-source₂-eq B) top-p₂
    ; at-post-relation =
        rel-target-transportᴿ (residual-source₂-eq B) top-p₂
          (CTI2.Λ⊑² Anv zero∈A liftγ₂ vV post⊢ bodyRel₂ top-p₂)
    ; at-post-value = vPost
    ; at-ν₂ = _
    ; at-residual-target = ΛResidualTarget₂ B′
    ; at-residual-q =
        subst≡ (λ C → `∀ A CTI2.⊑ᵂ⟨
            CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
          ⟩ C)
          (residual-target₂-eq B′)
          (ECR.transport⊑ᵂ
            (right-bind-right-bind-world-extendᴿ
              {W = W} {B = ★} {C = ＇ Fin.zero})
            q)
    ; at-residual-target-eq = sym (residual-target₂-eq B′)
    ; at-residual-cast =
        applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
          (↑ᶜ (close-instᶜ c′))
    ; at-residual-provenance =
        catchup⁻-nonstar
          (renameNonStar Fin.suc
            (renameNonStar (toRenameᵗ wk↪ᵗ)
              (inst-residual-source-nonstar Bnv zero∈B)))
          (renameNonStar Fin.suc
            (renameNonStar (toRenameᵗ wk↪ᵗ)
              (nonstar-from-≢★ B′≢★)))
          (applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
            (↑ᶜ (close-instᶜ c′)))
    ; at-residual-fuel =
        subst≡ (λ n → suc n < fuel)
          (sym (castSize-applyConsistency
            (bind {Δ = suc Δᴿ} (＇ Fin.zero))
            (↑ᶜ (close-instᶜ c′))))
          (≤-trans (s≤s (inst-decrease B′≢★)) c<fuel)
    ; at-prefix-reduction =
        Λ⊑Λ²-prefix-reduction vV′ B′≢★
    ; at-spine-descent =
        spine-descent-zero vPost
          (rel-target-transportᴿ (residual-source₂-eq B) top-p₂
            (CTI2.Λ⊑² Anv zero∈A liftγ₂ vV post⊢ bodyRel₂ top-p₂))
    }


inst-residual-provenance : InstResidualProvenanceᵀ
inst-residual-provenance {B = B} {B′ = B′} c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ =
  catchup⁻-nonstar
    (renameNonStar (toRenameᵗ wk↪ᵗ)
      (inst-residual-source-nonstar Bnv zero∈B))
    (renameNonStar (toRenameᵗ wk↪ᵗ) (nonstar-from-≢★ B′≢★))
    (↑ᶜ (close-instᶜ c′))


record ΛPostPrefixPackageAt
    {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    (rel : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p)
    (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    (B′≢★ : B′ ≢ ★) : Set₁ where
  field
    prefix-p₂ :
      A CTI2.⊑ᵂ⟨
        CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
      ⟩ ΛResidualSource₂ B
    prefix-relation :
      CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
        CTI2.∣ ECR.mapCtxᴿ
          (right-bind-right-bind-world-extendᴿ
            {W = W} {B = ★} {C = ＇ Fin.zero})
          γ
        ⊢² M ⊑ Λ⊑Λ²PostTerm V′ B ∶ prefix-p₂
    prefix-value : Value (Λ⊑Λ²PostTerm V′ B)
    prefix-reduction :
      (Λ V′) ⟨ (inst c′) B′≢★ ⟩
        —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ [] ]
      Λ⊑Λ²PostTerm V′ B ⟨
        applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
          (↑ᶜ (close-instᶜ c′)) ⟩


mapCtxᴿ-sameCtx : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δᵖ Δ₂ Δᵖ₂}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δᵖ}
    {W₂ : CTI2.World Δᴸ Δᴿ′ Δ₂}
    {Wᵖ₂ : CTI2.World Δᴸ Δᴿ′ Δᵖ₂}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
  → (ext₂ : ECR.WorldExtendᴿ χs W W₂)
  → (extᵖ₂ : ECR.WorldExtendᴿ χs Wᵖ Wᵖ₂)
  → CTI2.SameCtx γ γᵖ
  → CTI2.SameCtx (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᵖ₂ γᵖ)
mapCtxᴿ-sameCtx ext₂ extᵖ₂ CTI2.same-[] = CTI2.same-[]
mapCtxᴿ-sameCtx ext₂ extᵖ₂ (CTI2.same-∷ sc) =
  CTI2.same-∷ (mapCtxᴿ-sameCtx ext₂ extᵖ₂ sc)


rightOnlyImpEnvMono : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.ImpEnvMono (CTI2.rightOnlyWorld W B)
      (CTI2.rightOnlyWorld Wᵖ B)
rightOnlyImpEnvMono mono Fin.zero eq = refl
rightOnlyImpEnvMono mono (Fin.suc Z) eq = mono Z eq


post-source-conceal-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)} {Xᴿ?}
    {c : Conv↓ Δᴸ A A′}
  → CTI2.SourceConcealPartnerOK
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      M c Xᴿ? (Λ⊑Λ²PostTerm V′ B)
post-source-conceal-partner-ok {c = seal X R} =
  CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↑)
post-source-conceal-partner-ok {c = c ↦↓ d} =
  CTI2.fun-conceal-target
post-source-conceal-partner-ok {c = `∀↓ c} =
  CTI2.all-conceal-target
post-source-conceal-partner-ok {c = id↓ A} =
  CTI2.id-conceal-target


Λ-post-prefix→package-at : ∀ {fuel Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → inst-alloc-decreaseᵀ
  → (rel : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p)
  → (vM : CT.Value M)
  → (vΛV′ : CT.Value (Λ V′))
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : A CTI2.⊑ᵂ⟨ W ⟩ B′)
  → ΛPostPrefixPackageAt rel c′ B′≢★
  → InstPostCatalogPackageAt fuel rel vM vΛV′ c′ B′≢★
      c<fuel q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (right-bind-right-bind-world-extendᴿ
        {W = W} {B = ★} {C = ＇ Fin.zero})
Λ-post-prefix→package-at {fuel = fuel} {Δᴿ = Δᴿ} {W = W}
    {V′ = V′} {B = B} {B′ = B′}
    inst-decrease rel vM vΛV′ c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ c<fuel q prefix =
  record
    { at-B₂ = ΛResidualSource₂ B
    ; at-post = Λ⊑Λ²PostTerm V′ B
    ; at-p₂ = ΛPostPrefixPackageAt.prefix-p₂ prefix
    ; at-post-relation = ΛPostPrefixPackageAt.prefix-relation prefix
    ; at-post-value = ΛPostPrefixPackageAt.prefix-value prefix
    ; at-ν₂ = _
    ; at-residual-target = ΛResidualTarget₂ B′
    ; at-residual-q =
        subst≡ (λ C → _ CTI2.⊑ᵂ⟨
            CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
          ⟩ C)
          (residual-target₂-eq B′)
          (ECR.transport⊑ᵂ
            (right-bind-right-bind-world-extendᴿ
              {W = W} {B = ★} {C = ＇ Fin.zero})
            q)
    ; at-residual-target-eq = sym (residual-target₂-eq B′)
    ; at-residual-cast =
        applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
          (↑ᶜ (close-instᶜ c′))
    ; at-residual-provenance =
        catchup⁻-nonstar
          (renameNonStar Fin.suc
            (renameNonStar (toRenameᵗ wk↪ᵗ)
              (inst-residual-source-nonstar Bnv zero∈B)))
          (renameNonStar Fin.suc
            (renameNonStar (toRenameᵗ wk↪ᵗ)
              (nonstar-from-≢★ B′≢★)))
          (applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
            (↑ᶜ (close-instᶜ c′)))
    ; at-residual-fuel =
        subst≡ (λ n → suc n < fuel)
          (sym (castSize-applyConsistency
            (bind {Δ = suc Δᴿ} (＇ Fin.zero))
            (↑ᶜ (close-instᶜ c′))))
          (≤-trans (s≤s (inst-decrease B′≢★)) c<fuel)
    ; at-prefix-reduction =
        ΛPostPrefixPackageAt.prefix-reduction prefix
    ; at-spine-descent =
        spine-descent-zero
          (ΛPostPrefixPackageAt.prefix-value prefix)
          (ΛPostPrefixPackageAt.prefix-relation prefix)
    }


Λ⊑Λ²-base-prefix-at : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → ΛPostPrefixPackageAt rel c′ B′≢★
Λ⊑Λ²-base-prefix-at {Δᴿ = Δᴿ} {W = W} {V′ = V′}
    {A = A} {B = B} rel vV vV′ c′ B′≢★ liftγ Anv zero∈A
    bodyRel
    with Λ⊑Λ²-post-body-transport
      right-bind-right-bind-world-extendᴿ Anv zero∈A
      liftγ vV vV′ bodyRel
Λ⊑Λ²-base-prefix-at {Δᴿ = Δᴿ} {W = W} {V′ = V′}
    {A = A} {B = B} rel vV vV′ c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ liftγ Anv zero∈A bodyRel
  | γ₂ᴸ , body-p₂ , top-p₂ ,
    liftγ₂ , vPost , post⊢ , bodyRel₂ =
  record
    { prefix-p₂ =
        subst≡ (λ C → `∀ A CTI2.⊑ᵂ⟨
            CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
          ⟩ C)
          (residual-source₂-eq B) top-p₂
    ; prefix-relation =
        rel-target-transportᴿ (residual-source₂-eq B) top-p₂
          (CTI2.Λ⊑² Anv zero∈A liftγ₂ vV post⊢ bodyRel₂ top-p₂)
    ; prefix-value = vPost
    ; prefix-reduction =
        Λ⊑Λ²-prefix-reduction vV′ B′≢★
    }


Λ⊑²-smart-recursive-prefix-at : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vV : CT.Value V)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (liftγ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (bodyRel : CTI2.liftWorldLeft I.X⊑★ W CTI2.∣ γᴸ
      ⊢² V ⊑ Λ V′ ∶ body-p)
  → ΛPostPrefixPackageAt bodyRel c′ B′≢★
  → ΛPostPrefixPackageAt rel c′ B′≢★
Λ⊑²-smart-recursive-prefix-at {W = W}
    rel vV c′ B′≢★ liftγ Anv zero∈A bodyRel bodyPrefix =
  record
    { prefix-p₂ =
        Λ⊑²-smart-fresh-top {W = W} Anv zero∈A
          (ΛPostPrefixPackageAt.prefix-p₂ bodyPrefix)
    ; prefix-relation =
        Λ⊑²-smart-fresh-at-rewrap Anv zero∈A liftγ vV
          (ΛPostPrefixPackageAt.prefix-relation bodyPrefix)
    ; prefix-value =
        ΛPostPrefixPackageAt.prefix-value bodyPrefix
    ; prefix-reduction =
        ΛPostPrefixPackageAt.prefix-reduction bodyPrefix
    }
