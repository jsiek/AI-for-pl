module proof.DGG.Catchup.InstInversionProof where

-- File Charter:
--   * Proves support lemmas for the M5 target-instantiation inversion
--     packages.
--   * Starts with residual `CatchupCast⁻` provenance for the Λ package.
--   * Imports only the live Def surface plus core/proof-only consistency
--     support; it does not consume other catch-up Proof modules.

open import Data.Empty using (⊥-elim)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Data.List using ([]; _∷_)
import Data.List as List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; s≤s)
open import Data.Nat.Properties using (n<1+n; ≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_)
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
   wk↪ᵗ)
open import Conversion using
  (Conv↑; Conv↓; replaceTy; makeConceal; 〖_,_↑_〗; rename↑)
import Imprecision as I
open import Imprecision using (_⊢_⊑_)
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
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; nonstar-from-≢★; rename-⊑;
   source-nonvar-target; source-occurs-target; subst-zero-occurs-exts;
   toRenameᵗ-injective)
import proof.ImprecisionConsistency as PIC
open import proof.TypeInTermSubst using
  (renameᵗᵐ-preserves-Value; rename-occurs; StoreTransport-lift-bind;
   StoreRename-suc-bind; toRename-keep-eq; toRename-wk-eq)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CastTermImprecision2Typing as CTI2T
import proof.DGG.CenterRename as CR
import proof.DGG.TargetBindLift as TBL
import proof.DGG.TargetExtend as TE
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; _++χ_; FuelStepSurface; Catchup⁻Embedᵀ;
   inst-alloc-decreaseᵀ;
   catchup⁻-inert; catchup⁻-id; catchup⁻-inst;
   catchup⁻-bot-elim; catchup⁻-bot-intro)
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


swap01 : ∀ {Δ} → Fin.Fin (suc (suc Δ)) → Fin.Fin (suc (suc Δ))
swap01 Fin.zero = Fin.suc Fin.zero
swap01 (Fin.suc Fin.zero) = Fin.zero
swap01 (Fin.suc (Fin.suc X)) = Fin.suc (Fin.suc X)


swap01-injective : ∀ {Δ} {X Y : Fin.Fin (suc (suc Δ))}
  → swap01 X ≡ swap01 Y
  → X ≡ Y
swap01-injective {X = Fin.zero} {Y = Fin.zero} eq = refl
swap01-injective {X = Fin.zero} {Y = Fin.suc Fin.zero} ()
swap01-injective {X = Fin.zero} {Y = Fin.suc (Fin.suc Y)} ()
swap01-injective {X = Fin.suc Fin.zero} {Y = Fin.zero} ()
swap01-injective {X = Fin.suc Fin.zero} {Y = Fin.suc Fin.zero} eq =
  refl
swap01-injective {X = Fin.suc Fin.zero} {Y = Fin.suc (Fin.suc Y)} ()
swap01-injective {X = Fin.suc (Fin.suc X)} {Y = Fin.zero} ()
swap01-injective {X = Fin.suc (Fin.suc X)} {Y = Fin.suc Fin.zero} ()
swap01-injective {X = Fin.suc (Fin.suc X)}
    {Y = Fin.suc (Fin.suc Y)} eq =
  cong (λ Z → Fin.suc (Fin.suc Z)) (fin-suc-injective
    (fin-suc-injective eq))


swap01-involutive : ∀ {Δ} (X : Fin.Fin (suc (suc Δ)))
  → swap01 (swap01 X) ≡ X
swap01-involutive Fin.zero = refl
swap01-involutive (Fin.suc Fin.zero) = refl
swap01-involutive (Fin.suc (Fin.suc X)) = refl


swap12 : ∀ {Δ} → Fin.Fin (suc (suc (suc Δ)))
  → Fin.Fin (suc (suc (suc Δ)))
swap12 = extᵗ swap01


swap12-injective : ∀ {Δ}
    {X Y : Fin.Fin (suc (suc (suc Δ)))}
  → swap12 X ≡ swap12 Y
  → X ≡ Y
swap12-injective = ext-injective swap01-injective


swap12-involutive : ∀ {Δ} (X : Fin.Fin (suc (suc (suc Δ))))
  → swap12 (swap12 X) ≡ X
swap12-involutive Fin.zero = refl
swap12-involutive (Fin.suc X) = cong Fin.suc (swap01-involutive X)


data Swap01OPE : ∀ {Δ₀ Δ}
    → Δ₀ ↪ᵗ suc (suc Δ) → Δ₀ ↪ᵗ suc (suc Δ) → Set where
  swap01-empty : ∀ {Δ} → Swap01OPE {Δ = Δ} empty empty
  swap01-skip-empty : ∀ {Δ}
    → Swap01OPE {Δ = Δ} (skip empty) empty
  swap01-keep-empty : ∀ {Δ}
    → Swap01OPE {Δ = Δ} (keep empty) (skip (keep empty))
  swap01-skip-skip : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → Swap01OPE (skip (skip η)) (skip (skip η))
  swap01-skip-keep : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → Swap01OPE (skip (keep η)) (keep (skip η))
  swap01-keep-skip : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → Swap01OPE (keep (skip η)) (skip (keep η))


data NoKeepKeep01 : ∀ {Δ₀ Δ}
    → Δ₀ ↪ᵗ suc (suc Δ) → Set where
  no-keep-keep-empty : ∀ {Δ}
    → NoKeepKeep01 {Δ = Δ} empty
  no-keep-keep-skip-empty : ∀ {Δ}
    → NoKeepKeep01 {Δ = Δ} (skip empty)
  no-keep-keep-keep-empty : ∀ {Δ}
    → NoKeepKeep01 {Δ = Δ} (keep empty)
  no-keep-keep-skip-skip : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → NoKeepKeep01 (skip (skip η))
  no-keep-keep-skip-keep : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → NoKeepKeep01 (skip (keep η))
  no-keep-keep-keep-skip : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
    → NoKeepKeep01 (keep (skip η))


swap01-reify-ope : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ suc (suc Δ)}
  → NoKeepKeep01 η
  → Σ[ ηˣ ∈ Δ₀ ↪ᵗ suc (suc Δ) ] Swap01OPE η ηˣ
swap01-reify-ope no-keep-keep-empty =
  empty , swap01-empty
swap01-reify-ope no-keep-keep-skip-empty =
  empty , swap01-skip-empty
swap01-reify-ope no-keep-keep-keep-empty =
  skip (keep empty) , swap01-keep-empty
swap01-reify-ope (no-keep-keep-skip-skip {η = η}) =
  skip (skip η) , swap01-skip-skip
swap01-reify-ope (no-keep-keep-skip-keep {η = η}) =
  keep (skip η) , swap01-skip-keep
swap01-reify-ope (no-keep-keep-keep-skip {η = η}) =
  skip (keep η) , swap01-keep-skip


top-target-frozen-no-keep-keep : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ Δ}
    {η′ : suc Δ₀ ↪ᵗ suc (suc Δ)}
  → (∀ Y → toRenameᵗ η′ Y ≡ toRenameᵗ (keep (skip η)) Y)
  → NoKeepKeep01 η′
top-target-frozen-no-keep-keep {η′ = skip (skip η′)} frozen =
  no-keep-keep-skip-skip
top-target-frozen-no-keep-keep {η′ = skip (keep η′)} frozen =
  no-keep-keep-skip-keep
top-target-frozen-no-keep-keep {η′ = keep empty} frozen =
  no-keep-keep-keep-empty
top-target-frozen-no-keep-keep {η′ = keep (skip η′)} frozen =
  no-keep-keep-keep-skip
top-target-frozen-no-keep-keep {η′ = keep (keep η′)} frozen
    with frozen (Fin.suc Fin.zero)
top-target-frozen-no-keep-keep {η′ = keep (keep η′)} frozen | ()


top-source-off-no-keep-keep : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ Δ}
    {η′ : suc Δ₀ ↪ᵗ suc (suc Δ)}
    {X : Fin.Fin (suc Δ₀)}
  → (∀ {Y} → Y ≢ X
      → toRenameᵗ η′ Y ≡ toRenameᵗ (skip (keep η)) Y)
  → NoKeepKeep01 η′
top-source-off-no-keep-keep {η′ = skip (skip η′)} off =
  no-keep-keep-skip-skip
top-source-off-no-keep-keep {η′ = skip (keep η′)} off =
  no-keep-keep-skip-keep
top-source-off-no-keep-keep {η′ = keep empty} off =
  no-keep-keep-keep-empty
top-source-off-no-keep-keep {η′ = keep (skip η′)} off =
  no-keep-keep-keep-skip
top-source-off-no-keep-keep {η′ = keep (keep η′)} {X = Fin.zero} off
    with off {Y = Fin.suc Fin.zero} (λ ())
top-source-off-no-keep-keep {η′ = keep (keep η′)} {X = Fin.zero} off
    | ()
top-source-off-no-keep-keep {η′ = keep (keep η′)} {X = Fin.suc X} off
    with off {Y = Fin.zero} (λ ())
top-source-off-no-keep-keep {η′ = keep (keep η′)} {X = Fin.suc X} off
    | ()


top-skip-skip-frozen-no-keep-keep : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ Δ}
    {η′ : Δ₀ ↪ᵗ suc (suc Δ)}
  → (∀ Y → toRenameᵗ η′ Y ≡ toRenameᵗ (skip (skip η)) Y)
  → NoKeepKeep01 η′
top-skip-skip-frozen-no-keep-keep {η′ = empty} frozen =
  no-keep-keep-empty
top-skip-skip-frozen-no-keep-keep {η′ = skip empty} frozen =
  no-keep-keep-skip-empty
top-skip-skip-frozen-no-keep-keep {η′ = skip (skip η′)} frozen =
  no-keep-keep-skip-skip
top-skip-skip-frozen-no-keep-keep {η′ = skip (keep η′)} frozen
    with frozen Fin.zero
top-skip-skip-frozen-no-keep-keep {η′ = skip (keep η′)} frozen | ()
top-skip-skip-frozen-no-keep-keep {η′ = keep empty} frozen
    with frozen Fin.zero
top-skip-skip-frozen-no-keep-keep {η′ = keep empty} frozen | ()
top-skip-skip-frozen-no-keep-keep {η′ = keep (skip η′)} frozen
    with frozen Fin.zero
top-skip-skip-frozen-no-keep-keep {η′ = keep (skip η′)} frozen | ()
top-skip-skip-frozen-no-keep-keep {η′ = keep (keep η′)} frozen
    with frozen Fin.zero
top-skip-skip-frozen-no-keep-keep {η′ = keep (keep η′)} frozen | ()


data AdjacentSwapOPE : ∀ {Δ₀ Δ}
    (ρ : TyVar Δ → TyVar Δ)
    → Δ₀ ↪ᵗ Δ → Δ₀ ↪ᵗ Δ → Set where
  adj-swap01 : ∀ {Δ₀ Δ}
      {η ηˣ : Δ₀ ↪ᵗ suc (suc Δ)}
    → Swap01OPE η ηˣ
    → AdjacentSwapOPE swap01 η ηˣ

  adj-under-skip : ∀ {Δ₀ Δ} {ρ : TyVar Δ → TyVar Δ}
      {η ηˣ : Δ₀ ↪ᵗ Δ}
    → AdjacentSwapOPE ρ η ηˣ
    → AdjacentSwapOPE (extᵗ ρ) (skip η) (skip ηˣ)

  adj-under-keep : ∀ {Δ₀ Δ} {ρ : TyVar Δ → TyVar Δ}
      {η ηˣ : Δ₀ ↪ᵗ Δ}
    → AdjacentSwapOPE ρ η ηˣ
    → AdjacentSwapOPE (extᵗ ρ) (keep η) (keep ηˣ)


under-right-target-reify-ope : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ Δ}
    {η′ : suc (suc Δ₀) ↪ᵗ suc (suc (suc Δ))}
  → (∀ Y → toRenameᵗ η′ Y ≡ toRenameᵗ (keep (keep (skip η))) Y)
  → Σ[ ηˣ ∈ suc (suc Δ₀) ↪ᵗ suc (suc (suc Δ)) ]
      AdjacentSwapOPE swap12 η′ ηˣ
under-right-target-reify-ope {η′ = skip η′} frozen
    with frozen Fin.zero
under-right-target-reify-ope {η′ = skip η′} frozen | ()
under-right-target-reify-ope {η = η} {η′ = keep η′} frozen
    with swap01-reify-ope
      (top-target-frozen-no-keep-keep
        {η = η} {η′ = η′} tail-frozen)
  where
  tail-frozen : ∀ Y
    → toRenameᵗ η′ Y ≡ toRenameᵗ (keep (skip η)) Y
  tail-frozen Y = fin-suc-injective (frozen (Fin.suc Y))
under-right-target-reify-ope {η = η} {η′ = keep η′} frozen
    | ηˣ , ope =
  keep ηˣ , adj-under-keep (adj-swap01 ope)


under-right-source-reify-ope : ∀ {Δ₀ Δ}
    {η : Δ₀ ↪ᵗ Δ}
    {η′ : suc Δ₀ ↪ᵗ suc (suc (suc Δ))}
    {X : Fin.Fin (suc Δ₀)}
  → (∀ {Y} → Y ≢ X
      → toRenameᵗ η′ Y ≡ toRenameᵗ (skip (skip (keep η))) Y)
  → Σ[ ηˣ ∈ suc Δ₀ ↪ᵗ suc (suc (suc Δ)) ]
      AdjacentSwapOPE swap12 η′ ηˣ
under-right-source-reify-ope {η = η} {η′ = skip η′} {X = X} off
    with swap01-reify-ope
      (top-source-off-no-keep-keep
        {η = η} {η′ = η′} {X = X} tail-off)
  where
  tail-off : ∀ {Y}
    → Y ≢ X
    → toRenameᵗ η′ Y ≡ toRenameᵗ (skip (keep η)) Y
  tail-off Y≢ = fin-suc-injective (off Y≢)
under-right-source-reify-ope {η′ = skip η′} off | ηˣ , ope =
  skip ηˣ , adj-under-skip (adj-swap01 ope)
under-right-source-reify-ope {η = η} {η′ = keep η′} {X = Fin.zero} off
    with swap01-reify-ope
      (top-skip-skip-frozen-no-keep-keep
        {η = η} {η′ = η′} tail-frozen)
  where
  tail-frozen : ∀ Y
    → toRenameᵗ η′ Y ≡ toRenameᵗ (skip (skip η)) Y
  tail-frozen Y =
    fin-suc-injective (off {Y = Fin.suc Y} (λ ()))
under-right-source-reify-ope {η′ = keep η′} {X = Fin.zero} off
    | ηˣ , ope =
  keep ηˣ , adj-under-keep (adj-swap01 ope)
under-right-source-reify-ope {η′ = keep η′} {X = Fin.suc X} off
    with off {Y = Fin.zero} (λ ())
under-right-source-reify-ope {η′ = keep η′} {X = Fin.suc X} off | ()


swap01-ope-rename : ∀ {Δ₀ Δ}
    {η ηˣ : Δ₀ ↪ᵗ suc (suc Δ)}
  → Swap01OPE η ηˣ
  → ∀ X
  → toRenameᵗ ηˣ X ≡ swap01 (toRenameᵗ η X)
swap01-ope-rename swap01-empty ()
swap01-ope-rename swap01-skip-empty ()
swap01-ope-rename swap01-keep-empty Fin.zero = refl
swap01-ope-rename swap01-skip-skip X = refl
swap01-ope-rename swap01-skip-keep Fin.zero = refl
swap01-ope-rename swap01-skip-keep (Fin.suc X) = refl
swap01-ope-rename swap01-keep-skip Fin.zero = refl
swap01-ope-rename swap01-keep-skip (Fin.suc X) = refl


adjacent-swap-ope-rename : ∀ {Δ₀ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {η ηˣ : Δ₀ ↪ᵗ Δ}
  → AdjacentSwapOPE ρ η ηˣ
  → ∀ X
  → toRenameᵗ ηˣ X ≡ ρ (toRenameᵗ η X)
adjacent-swap-ope-rename (adj-swap01 ope) X =
  swap01-ope-rename ope X
adjacent-swap-ope-rename (adj-under-skip ope) X =
  cong Fin.suc (adjacent-swap-ope-rename ope X)
adjacent-swap-ope-rename (adj-under-keep ope) Fin.zero = refl
adjacent-swap-ope-rename (adj-under-keep ope) (Fin.suc X) =
  cong Fin.suc (adjacent-swap-ope-rename ope X)


top-source-swap-ope : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
  → AdjacentSwapOPE swap01 (skip (keep η)) (keep (skip η))
top-source-swap-ope = adj-swap01 swap01-skip-keep


top-target-swap-ope : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
  → AdjacentSwapOPE swap01 (keep (skip η)) (skip (keep η))
top-target-swap-ope = adj-swap01 swap01-keep-skip


under-right-source-swap-ope : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
  → AdjacentSwapOPE swap12
      (skip (skip (keep η))) (skip (keep (skip η)))
under-right-source-swap-ope =
  adj-under-skip top-source-swap-ope


under-right-target-swap-ope : ∀ {Δ₀ Δ} {η : Δ₀ ↪ᵗ Δ}
  → AdjacentSwapOPE swap12
      (keep (keep (skip η))) (keep (skip (keep η)))
under-right-target-swap-ope =
  adj-under-keep top-target-swap-ope


record CenterMapWorld {Δᴸ Δᴿ Δ}
    (ρ : TyVar Δ → TyVar Δ)
    (W Wˣ : CTI2.World Δᴸ Δᴿ Δ) : Set₁ where
  field
    map-injective : ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y
    map-involutive : ∀ X → ρ (ρ X) ≡ X

    source-center-map : ∀ Xᴸ
      → ρ (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
          ≡ toRenameᵗ (CTI2.ηᴸʷ Wˣ) Xᴸ

    target-center-map : ∀ Xᴿ
      → ρ (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
          ≡ toRenameᵗ (CTI2.ηᴿʷ Wˣ) Xᴿ

    impEnv-map : ∀ Z
      → CTI2.impEnvʷ W Z ≡ I.X⊑★
      → CTI2.impEnvʷ Wˣ (ρ Z) ≡ I.X⊑★

    impEnv-unmap : ∀ Z
      → CTI2.impEnvʷ Wˣ (ρ Z) ≡ I.X⊑★
      → CTI2.impEnvʷ W Z ≡ I.X⊑★

    sourceStore-map :
      CTI2.sourceStoreʷ Wˣ ≡ CTI2.sourceStoreʷ W

    targetStore-map :
      CTI2.targetStoreʷ Wˣ ≡ CTI2.targetStoreʷ W


open CenterMapWorld


center-map-source : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
  → CenterMapWorld ρ W Wˣ
  → ∀ A
  → renameᵗ ρ (CTI2.embedᴸ W A) ≡ CTI2.embedᴸ Wˣ A
center-map-source {ρ = ρ} {W = W} mp A =
  trans (renameᵗ-comp (toRenameᵗ (CTI2.ηᴸʷ W)) ρ A)
    (renameᵗ-cong A (source-center-map mp))


center-map-target : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
  → CenterMapWorld ρ W Wˣ
  → ∀ B
  → renameᵗ ρ (CTI2.embedᴿ W B) ≡ CTI2.embedᴿ Wˣ B
center-map-target {ρ = ρ} {W = W} mp B =
  trans (renameᵗ-comp (toRenameᵗ (CTI2.ηᴿʷ W)) ρ B)
    (renameᵗ-cong B (target-center-map mp))


center-map-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → A CTI2.⊑ᵂ⟨ W ⟩ B
  → A CTI2.⊑ᵂ⟨ Wˣ ⟩ B
center-map-⊑ᵂ {ρ = ρ} {W = W} {Wˣ = Wˣ} {A = A} {B = B} mp p =
  subst≡
    (λ L → CTI2.impEnvʷ Wˣ ⊢ L ⊑ CTI2.embedᴿ Wˣ B)
    (center-map-source mp A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wˣ ⊢ renameᵗ ρ (CTI2.embedᴸ W A) ⊑ R)
      (center-map-target mp B)
      (rename-⊑ ρ (map-injective mp) (impEnv-map mp) p))


swapWorld : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {ηᴸˣ : Δᴸ ↪ᵗ Δ} {ηᴿˣ : Δᴿ ↪ᵗ Δ}
  → (W : CTI2.World Δᴸ Δᴿ Δ)
  → AdjacentSwapOPE ρ (CTI2.ηᴸʷ W) ηᴸˣ
  → AdjacentSwapOPE ρ (CTI2.ηᴿʷ W) ηᴿˣ
  → CTI2.World Δᴸ Δᴿ Δ
swapWorld {ρ = ρ} {ηᴸˣ = ηᴸˣ} {ηᴿˣ = ηᴿˣ} W src tgt =
  CTI2.world ηᴸˣ ηᴿˣ (λ Z → CTI2.impEnvʷ W (ρ Z))
    (CTI2.sourceStoreʷ W) (CTI2.targetStoreʷ W)


swapWorld-map : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {ηᴸˣ : Δᴸ ↪ᵗ Δ} {ηᴿˣ : Δᴿ ↪ᵗ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (ρ-inj : ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y)
  → (ρ-inv : ∀ X → ρ (ρ X) ≡ X)
  → (src : AdjacentSwapOPE ρ (CTI2.ηᴸʷ W) ηᴸˣ)
  → (tgt : AdjacentSwapOPE ρ (CTI2.ηᴿʷ W) ηᴿˣ)
  → CenterMapWorld ρ W (swapWorld W src tgt)
swapWorld-map {ρ = ρ} {W = W} ρ-inj ρ-inv src tgt = record
  { map-injective = ρ-inj
  ; map-involutive = ρ-inv
  ; source-center-map = λ X →
      sym (adjacent-swap-ope-rename src X)
  ; target-center-map = λ X →
      sym (adjacent-swap-ope-rename tgt X)
  ; impEnv-map = λ Z star →
      subst≡ (λ Y → CTI2.impEnvʷ W Y ≡ I.X⊑★)
        (sym (ρ-inv Z)) star
  ; impEnv-unmap = λ Z star →
      subst≡ (λ Y → CTI2.impEnvʷ W Y ≡ I.X⊑★)
        (ρ-inv Z) star
  ; sourceStore-map = refl
  ; targetStore-map = refl
  }


center-map-ctx : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
  → CenterMapWorld ρ W Wˣ
  → CTI2.CtxImp W
  → CTI2.CtxImp Wˣ
center-map-ctx mp [] = []
center-map-ctx mp (CTI2.ctx-imp A B p ∷ γ) =
  CTI2.ctx-imp A B (center-map-⊑ᵂ mp p) ∷ center-map-ctx mp γ


center-map-∋ʷ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {x A B}
    {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → γ CTI2.∋ʷ x ⦂ CTI2.ctx-imp A B p
  → center-map-ctx mp γ CTI2.∋ʷ x ⦂
      CTI2.ctx-imp A B (center-map-⊑ᵂ mp p)
center-map-∋ʷ mp CTI2.Zʷ = CTI2.Zʷ
center-map-∋ʷ mp (CTI2.Sʷ x∈) = CTI2.Sʷ (center-map-∋ʷ mp x∈)


center-map-same-ctx : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W W′ Wˣ W′ˣ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {γ′ : CTI2.CtxImp W′}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (mp′ : CenterMapWorld ρ W′ W′ˣ)
  → CTI2.SameCtx γ γ′
  → CTI2.SameCtx (center-map-ctx mp γ) (center-map-ctx mp′ γ′)
center-map-same-ctx mp mp′ CTI2.same-[] = CTI2.same-[]
center-map-same-ctx mp mp′ (CTI2.same-∷ sc) =
  CTI2.same-∷ (center-map-same-ctx mp mp′ sc)


center-map-ctx-tgt : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (γ : CTI2.CtxImp W)
  → CTI2.tgtCtxʷ (center-map-ctx mp γ) ≡ CTI2.tgtCtxʷ γ
center-map-ctx-tgt mp [] = refl
center-map-ctx-tgt mp (CTI2.ctx-imp A B p ∷ γ) =
  cong (B ∷_) (center-map-ctx-tgt mp γ)


center-map-aligned : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.CenterAligned W Xᴸ Xᴿ
  → CTI2.CenterAligned Wˣ Xᴸ Xᴿ
center-map-aligned {ρ = ρ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} mp aligned =
  trans (sym (source-center-map mp Xᴸ))
    (trans (cong ρ aligned) (target-center-map mp Xᴿ))


center-map-same-runtime : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W W′ Wˣ W′ˣ : CTI2.World Δᴸ Δᴿ Δ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (mp′ : CenterMapWorld ρ W′ W′ˣ)
  → CTI2.SameRuntime W W′
  → CTI2.SameRuntime Wˣ W′ˣ
center-map-same-runtime mp mp′
    (CTI2.same-runtime source-eq target-eq) =
  CTI2.same-runtime
    (trans (sourceStore-map mp′)
      (trans source-eq (sym (sourceStore-map mp))))
    (trans (targetStore-map mp′)
      (trans target-eq (sym (targetStore-map mp))))


center-map-imp-mono : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W W′ Wˣ W′ˣ : CTI2.World Δᴸ Δᴿ Δ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (mp′ : CenterMapWorld ρ W′ W′ˣ)
  → CTI2.ImpEnvMono W W′
  → CTI2.ImpEnvMono Wˣ W′ˣ
center-map-imp-mono {ρ = ρ} {Wˣ = Wˣ} {W′ˣ = W′ˣ}
    mp mp′ mono Z star =
  subst≡ (λ Y → CTI2.impEnvʷ W′ˣ Y ≡ I.X⊑★)
    (map-involutive mp Z)
    (impEnv-map mp′ (ρ Z) (mono (ρ Z) old-star))
  where
  star-at-ρρ =
    subst≡ (λ Y → CTI2.impEnvʷ Wˣ Y ≡ I.X⊑★)
      (sym (map-involutive mp Z)) star

  old-star = impEnv-unmap mp (ρ Z) star-at-ρρ


center-map-lift-both : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {v : I.VarImp}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CenterMapWorld (extᵗ ρ)
      (CTI2.liftWorldBoth v W)
      (CTI2.liftWorldBoth v Wˣ)
center-map-lift-both mp = record
  { map-injective = ext-injective (map-injective mp)
  ; map-involutive = λ
      { Fin.zero → refl
      ; (Fin.suc X) → cong Fin.suc (map-involutive mp X)
      }
  ; source-center-map = λ
      { Fin.zero → refl
      ; (Fin.suc X) → cong Fin.suc (source-center-map mp X)
      }
  ; target-center-map = λ
      { Fin.zero → refl
      ; (Fin.suc X) → cong Fin.suc (target-center-map mp X)
      }
  ; impEnv-map = λ
      { Fin.zero eq → eq
      ; (Fin.suc Z) eq → impEnv-map mp Z eq
      }
  ; impEnv-unmap = λ
      { Fin.zero eq → eq
      ; (Fin.suc Z) eq → impEnv-unmap mp Z eq
      }
  ; sourceStore-map = cong store-lift (sourceStore-map mp)
  ; targetStore-map = cong store-lift (targetStore-map mp)
  }


center-map-lift-left : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {v : I.VarImp}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CenterMapWorld (extᵗ ρ)
      (CTI2.liftWorldLeft v W)
      (CTI2.liftWorldLeft v Wˣ)
center-map-lift-left mp = record
  { map-injective = ext-injective (map-injective mp)
  ; map-involutive = λ
      { Fin.zero → refl
      ; (Fin.suc X) → cong Fin.suc (map-involutive mp X)
      }
  ; source-center-map = λ
      { Fin.zero → refl
      ; (Fin.suc X) → cong Fin.suc (source-center-map mp X)
      }
  ; target-center-map = λ X →
      cong Fin.suc (target-center-map mp X)
  ; impEnv-map = λ
      { Fin.zero eq → eq
      ; (Fin.suc Z) eq → impEnv-map mp Z eq
      }
  ; impEnv-unmap = λ
      { Fin.zero eq → eq
      ; (Fin.suc Z) eq → impEnv-unmap mp Z eq
      }
  ; sourceStore-map = cong store-lift (sourceStore-map mp)
  ; targetStore-map = targetStore-map mp
  }


center-map-lift-ctx : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.LiftCtx I.X⊑X (center-map-ctx mp γ)
      (center-map-ctx (center-map-lift-both mp) γᴮ)
center-map-lift-ctx mp CTI2.lift-[] = CTI2.lift-[]
center-map-lift-ctx mp (CTI2.lift-∷ liftγ) =
  CTI2.lift-∷ (center-map-lift-ctx mp liftγ)


center-map-lift-ctxᴸ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
  → CTI2.LiftCtxᴸ I.X⊑★ (center-map-ctx mp γ)
      (center-map-ctx (center-map-lift-left mp) γᴸ)
center-map-lift-ctxᴸ mp CTI2.liftᴸ-[] = CTI2.liftᴸ-[]
center-map-lift-ctxᴸ mp (CTI2.liftᴸ-∷ liftγ) =
  CTI2.liftᴸ-∷ (center-map-lift-ctxᴸ mp liftγ)


center-map-store-rep : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.StoreRepImp W Xᴸ Xᴿ
  → CTI2.StoreRepImp Wˣ Xᴸ Xᴿ
center-map-store-rep {W = W} {Wˣ = Wˣ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ}
    mp (CTI2.store-rep-imp represented) =
  CTI2.store-rep-imp
    (subst≡
      (λ A → A CTI2.⊑ᵂ⟨ Wˣ ⟩
        CTI2.resolveVar (CTI2.targetStoreʷ Wˣ) Xᴿ)
      (sym source-eq)
      (subst≡
        (λ B → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ
          CTI2.⊑ᵂ⟨ Wˣ ⟩ B)
        (sym target-eq)
        (center-map-⊑ᵂ mp represented)))
  where
  source-eq =
    cong (λ Σ → CTI2.resolveVar Σ Xᴸ) (sourceStore-map mp)

  target-eq =
    cong (λ Σ → CTI2.resolveVar Σ Xᴿ) (targetStore-map mp)


center-map-rebase-at : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W W′ Wˣ W′ˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (mp′ : CenterMapWorld ρ W′ W′ˣ)
  → CTI2.RebaseAt W W′ Xᴸ Xᴿ
  → CTI2.RebaseAt Wˣ W′ˣ Xᴸ Xᴿ
center-map-rebase-at {ρ = ρ} {Xᴸ = Xᴸ} {Xᴿ = Xᴿ} mp mp′
    (CTI2.rebase-at runtime offL frozenR aligned reps) =
  CTI2.rebase-at
    (center-map-same-runtime mp mp′ runtime)
    (λ Y≢ → trans (sym (source-center-map mp′ _))
      (trans (cong ρ (offL Y≢)) (source-center-map mp _)))
    (λ Y → trans (sym (target-center-map mp′ Y))
      (trans (cong ρ (frozenR Y)) (target-center-map mp Y)))
    (center-map-aligned mp′ aligned)
    (center-map-store-rep mp′ reps)


center-map-mark-starᴸ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) ≡ I.X⊑★
  → CTI2.impEnvʷ Wˣ (toRenameᵗ (CTI2.ηᴸʷ Wˣ) Xᴸ) ≡ I.X⊑★
center-map-mark-starᴸ {W = W} {Wˣ = Wˣ} {Xᴸ = Xᴸ} mp to-star =
  subst≡ (λ Z → CTI2.impEnvʷ Wˣ Z ≡ I.X⊑★)
    (source-center-map mp Xᴸ)
    (impEnv-map mp (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ) to-star)


center-map-disalignedᴸ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → (∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
  → ∀ Xᴿ → toRenameᵗ (CTI2.ηᴿʷ Wˣ) Xᴿ
      ≢ toRenameᵗ (CTI2.ηᴸʷ Wˣ) Xᴸ
center-map-disalignedᴸ {ρ = ρ} {Xᴸ = Xᴸ} mp disaligned Xᴿ eq =
  disaligned Xᴿ
    (map-injective mp
      (trans (target-center-map mp Xᴿ)
        (trans eq (sym (source-center-map mp Xᴸ)))))


center-map-represented★ᴸ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ : TyVar Δᴸ}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.resolveVar (CTI2.sourceStoreʷ W) Xᴸ CTI2.⊑ᵂ⟨ W ⟩ ★
  → CTI2.resolveVar (CTI2.sourceStoreʷ Wˣ) Xᴸ
      CTI2.⊑ᵂ⟨ Wˣ ⟩ ★
center-map-represented★ᴸ {W = W} {Wˣ = Wˣ} {Xᴸ = Xᴸ} mp represented =
  subst≡ (λ A → A CTI2.⊑ᵂ⟨ Wˣ ⟩ ★)
    (sym source-eq)
    (center-map-⊑ᵂ mp represented)
  where
  source-eq =
    cong (λ Σ → CTI2.resolveVar Σ Xᴸ) (sourceStore-map mp)


center-map-rep★-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.Rep★PartnerOK W X P Xᴿ? M′
  → CTI2.Rep★PartnerOK Wˣ X P Xᴿ? M′
center-map-rep★-partner-ok mp (CTI2.rep★-untagged nt) =
  CTI2.rep★-untagged nt
center-map-rep★-partner-ok mp (CTI2.rep★-nonvar-tag Gnv) =
  CTI2.rep★-nonvar-tag Gnv
center-map-rep★-partner-ok mp (CTI2.rep★-var-tag aligned) =
  CTI2.rep★-var-tag (center-map-aligned mp aligned)
center-map-rep★-partner-ok mp
    (CTI2.rep★-matched-inner-tags X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags X₂≢X
    (center-map-aligned mp aligned)
center-map-rep★-partner-ok mp (CTI2.rep★-round-trip ok) =
  CTI2.rep★-round-trip (center-map-rep★-partner-ok mp ok)


center-map-seal-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.SealPartnerOK W X P R Xᴿ? M′
  → CTI2.SealPartnerOK Wˣ X P R Xᴿ? M′
center-map-seal-partner-ok mp (CTI2.star-rep-target ok) =
  CTI2.star-rep-target (center-map-rep★-partner-ok mp ok)
center-map-seal-partner-ok mp (CTI2.plain-target nt) =
  CTI2.plain-target nt
center-map-seal-partner-ok mp CTI2.name-protected-target =
  CTI2.name-protected-target


center-map-source-conceal-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {M : CT.Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.SourceConcealPartnerOK W M c Xᴿ? M′
  → CTI2.SourceConcealPartnerOK Wˣ M c Xᴿ? M′
center-map-source-conceal-partner-ok mp
    (CTI2.seal-partner-ok ok) =
  CTI2.seal-partner-ok (center-map-seal-partner-ok mp ok)
center-map-source-conceal-partner-ok mp
    CTI2.fun-conceal-target =
  CTI2.fun-conceal-target
center-map-source-conceal-partner-ok mp
    CTI2.all-conceal-target =
  CTI2.all-conceal-target
center-map-source-conceal-partner-ok mp
    CTI2.id-conceal-target =
  CTI2.id-conceal-target


center-map-matched-conceal-partner-ok : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {M : CT.Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Y M′}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.MatchedConcealPartnerOK W M c Y M′
  → CTI2.MatchedConcealPartnerOK Wˣ M c Y M′
center-map-matched-conceal-partner-ok mp
    (CTI2.matched-seal-star-partner ok) =
  CTI2.matched-seal-star-partner
    (center-map-rep★-partner-ok mp ok)
center-map-matched-conceal-partner-ok mp
    (CTI2.matched-seal-nonstar Rns) =
  CTI2.matched-seal-nonstar Rns
center-map-matched-conceal-partner-ok mp
    CTI2.matched-fun-conceal-target =
  CTI2.matched-fun-conceal-target
center-map-matched-conceal-partner-ok mp
    CTI2.matched-all-conceal-target =
  CTI2.matched-all-conceal-target
center-map-matched-conceal-partner-ok mp
    CTI2.matched-id-conceal-target =
  CTI2.matched-id-conceal-target


center-map-target-⊢↑ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴿ? A B} {c : Conv↑ Δᴿ A B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.targetStoreʷ W CTI2.⊢↑[ Xᴿ? ] c
  → CTI2.targetStoreʷ Wˣ CTI2.⊢↑[ Xᴿ? ] c
center-map-target-⊢↑ mp c⊢ =
  subst≡ (λ Σ → Σ CTI2.⊢↑[ _ ] _) (sym (targetStore-map mp)) c⊢


center-map-target-⊢↓ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴿ? A B} {c : Conv↓ Δᴿ A B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.targetStoreʷ W CTI2.⊢↓[ Xᴿ? ] c
  → CTI2.targetStoreʷ Wˣ CTI2.⊢↓[ Xᴿ? ] c
center-map-target-⊢↓ mp c⊢ =
  subst≡ (λ Σ → Σ CTI2.⊢↓[ _ ] _) (sym (targetStore-map mp)) c⊢


center-map-source-⊢↑ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? A B} {c : Conv↑ Δᴸ A B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c
  → CTI2.sourceStoreʷ Wˣ CTI2.⊢↑[ Xᴸ? ] c
center-map-source-⊢↑ mp c⊢ =
  subst≡ (λ Σ → Σ CTI2.⊢↑[ _ ] _) (sym (sourceStore-map mp)) c⊢


center-map-source-⊢↓ : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {Xᴸ? A B} {c : Conv↓ Δᴸ A B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
  → CTI2.sourceStoreʷ Wˣ CTI2.⊢↓[ Xᴸ? ] c
center-map-source-⊢↓ mp c⊢ =
  subst≡ (λ Σ → Σ CTI2.⊢↓[ _ ] _) (sym (sourceStore-map mp)) c⊢


record CenterMapSupport {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    (mp : CenterMapWorld ρ W Wˣ) : Set₁ where
  coinductive
  field
    liftBothSupport :
      CenterMapSupport (center-map-lift-both {v = I.X⊑X} mp)

    liftLeftSupport :
      CenterMapSupport (center-map-lift-left {v = I.X⊑★} mp)

    rebaseAtForward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → CTI2.RebaseAt W Wᵖ Xᴸ Xᴿ
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.RebaseAt Wˣ Wᵖˣ Xᴸ Xᴿ

    rebaseAtBackward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
      → CTI2.RebaseAt Wᵖ W Xᴸ Xᴿ
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.RebaseAt Wᵖˣ Wˣ Xᴸ Xᴿ

    rebaseAtᴿForward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴿ? : Maybe (TyVar Δᴿ)}
      → CTI2.RebaseAtᴿ W Wᵖ Xᴿ?
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.RebaseAtᴿ Wˣ Wᵖˣ Xᴿ?

    rebaseAtᴿBackward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴿ? : Maybe (TyVar Δᴿ)}
      → CTI2.RebaseAtᴿ Wᵖ W Xᴿ?
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.RebaseAtᴿ Wᵖˣ Wˣ Xᴿ?

    rebaseAtᴸForward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴸ? : Maybe (TyVar Δᴸ)}
      → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.RebaseAtᴸ Wˣ Wᵖˣ Xᴸ?

    tagRebaseAtᴸBackward : ∀ {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
        {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
      → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
      → Σ[ Wᵖˣ ∈ CTI2.World Δᴸ Δᴿ Δ ]
        Σ[ mpᵖ ∈ CenterMapWorld ρ Wᵖ Wᵖˣ ]
          CenterMapSupport mpᵖ
          × CTI2.TagRebaseAtᴸ Wᵖˣ Wˣ Xᴸ? Xᴿ?


open CenterMapSupport


⊢²-center-map : ∀ {Δᴸ Δᴿ Δ}
    {ρ : TyVar Δ → TyVar Δ}
    {W Wˣ : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W} {M : CT.Term Δᴸ} {N : CT.Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ B}
  → (mp : CenterMapWorld ρ W Wˣ)
  → CenterMapSupport mp
  → W CTI2.∣ γ ⊢² M ⊑ N ∶ p
  → (p′ : A CTI2.⊑ᵂ⟨ Wˣ ⟩ B)
  → Wˣ CTI2.∣ center-map-ctx mp γ ⊢² M ⊑ N ∶ p′
⊢²-center-map mp sup (CTI2.x⊑x² x∈) p′ =
  TBL.⊢²-retarget (CTI2.x⊑x² (center-map-∋ʷ mp x∈))
⊢²-center-map mp sup
    (CTI2.ƛ⊑ƛ² {pA = pA} {pB = pB} M⊑N) p′ =
  TBL.⊢²-retarget (CTI2.ƛ⊑ƛ²
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp pB)))
⊢²-center-map mp sup
    (CTI2.·⊑·² {pA = pA} {pB = pB} L⊑L′ M⊑M′) p′ =
  TBL.⊢²-retarget (CTI2.·⊑·²
    (⊢²-center-map mp sup L⊑L′
      (I.⇒⊑⇒ (center-map-⊑ᵂ mp pA) (center-map-⊑ᵂ mp pB)))
    (⊢²-center-map mp sup M⊑M′ (center-map-⊑ᵂ mp pA)))
⊢²-center-map mp sup
    (CTI2.Λ⊑Λ² {p = p} liftγ vV vV′ V⊑V′ q) p′ =
  CTI2.Λ⊑Λ² (center-map-lift-ctx mp liftγ) vV vV′
    (⊢²-center-map (center-map-lift-both {v = I.X⊑X} mp)
      (liftBothSupport sup) V⊑V′
      (center-map-⊑ᵂ (center-map-lift-both {v = I.X⊑X} mp) p))
    p′
⊢²-center-map {γ = γ} mp sup
    (CTI2.Λ⊑² {p = p} Anv zero∈A liftγ vV N⊢ V⊑N q) p′ =
  CTI2.Λ⊑² Anv zero∈A (center-map-lift-ctxᴸ mp liftγ) vV
    (subst≡ (λ Σ → ⟨ _ , Σ , CTI2.tgtCtxʷ (center-map-ctx mp γ) ⟩
        ⊢ _ ⦂ _)
      (sym (targetStore-map mp))
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (sym (center-map-ctx-tgt mp γ)) N⊢))
    (⊢²-center-map (center-map-lift-left {v = I.X⊑★} mp)
      (liftLeftSupport sup) V⊑N
      (center-map-⊑ᵂ (center-map-lift-left {v = I.X⊑★} mp) p))
    p′
⊢²-center-map mp sup (CTI2.•⊑•² p∀ M⊑N q r) p′ =
  CTI2.•⊑•² (center-map-⊑ᵂ mp p∀)
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp p∀))
    (center-map-⊑ᵂ mp q) p′
⊢²-center-map mp sup (CTI2.•⊑² p∀ M⊑N q r) p′ =
  CTI2.•⊑² (center-map-⊑ᵂ mp p∀)
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp p∀))
    (center-map-⊑ᵂ mp q) p′
⊢²-center-map mp sup (CTI2.κ⊑κ² κ p) p′ =
  CTI2.κ⊑κ² κ p′
⊢²-center-map mp sup
    (CTI2.cast⊑cast² {p = p} c c′ M⊑N q) p′ =
  CTI2.cast⊑cast² c c′
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp p)) p′
⊢²-center-map mp sup
    (CTI2.⊑cast² {p = p} c′ M⊑N q) p′ =
  CTI2.⊑cast² c′
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp p)) p′
⊢²-center-map mp sup
    (CTI2.cast⊑² {p = p} c M⊑N q) p′ =
  CTI2.cast⊑² c
    (⊢²-center-map mp sup M⊑N (center-map-⊑ᵂ mp p)) p′
⊢²-center-map mp sup
    (CTI2.⊑reveal² {W′ = W′} {p = p} mono rb sc c′⊢ M⊑N q)
    p′
    with rebaseAtᴿForward sup rb
... | W′ˣ , mp′ , sup′ , rb′ =
  CTI2.⊑reveal² (center-map-imp-mono mp mp′ mono) rb′
    (center-map-same-ctx mp mp′ sc) (center-map-target-⊢↑ mp c′⊢)
    (⊢²-center-map mp′ sup′ M⊑N (center-map-⊑ᵂ mp′ p))
    p′
⊢²-center-map mp sup
    (CTI2.⊑conceal² {W′ = W′} {p = p} mono rb sc c′⊢ M⊑N q)
    p′
    with rebaseAtᴿBackward sup rb
... | W′ˣ , mp′ , sup′ , rb′ =
  CTI2.⊑conceal² (center-map-imp-mono mp mp′ mono) rb′
    (center-map-same-ctx mp mp′ sc) (center-map-target-⊢↓ mp c′⊢)
    (⊢²-center-map mp′ sup′ M⊑N (center-map-⊑ᵂ mp′ p))
    p′
⊢²-center-map mp sup
    (CTI2.reveal⊑² {W′ = W′} {p = p} mono rb sc c⊢ M⊑N q)
    p′
    with rebaseAtᴸForward sup rb
... | W′ˣ , mp′ , sup′ , rb′ =
  CTI2.reveal⊑² (center-map-imp-mono mp mp′ mono) rb′
    (center-map-same-ctx mp mp′ sc) (center-map-source-⊢↑ mp c⊢)
    (⊢²-center-map mp′ sup′ M⊑N (center-map-⊑ᵂ mp′ p))
    p′
⊢²-center-map mp sup
    (CTI2.conceal⊑² {W′ = W′} {p = p} ok mono rb sc c⊢ M⊑N q)
    p′
    with tagRebaseAtᴸBackward sup rb
... | W′ˣ , mp′ , sup′ , rb′ =
  CTI2.conceal⊑²
    (center-map-source-conceal-partner-ok mp′ ok)
    (center-map-imp-mono mp mp′ mono) rb′
    (center-map-same-ctx mp mp′ sc) (center-map-source-⊢↓ mp c⊢)
    (⊢²-center-map mp′ sup′ M⊑N (center-map-⊑ᵂ mp′ p))
    p′
⊢²-center-map mp sup
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} {p = p}
      mono rb sc c⊢ c′⊢ M⊑N q)
    p′
    with rebaseAtForward sup rb
... | Wᵖˣ , mpᵖ , supᵖ , rbᵖ =
  CTI2.reveal⊑reveal²
    (center-map-imp-mono mp mpᵖ mono) rbᵖ
    (center-map-same-ctx mp mpᵖ sc)
    (center-map-source-⊢↑ mp c⊢) (center-map-target-⊢↑ mp c′⊢)
    (⊢²-center-map mpᵖ supᵖ M⊑N (center-map-⊑ᵂ mpᵖ p))
    p′
⊢²-center-map mp sup
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} {p = p}
      ok mono rb sc c⊢ c′⊢ M⊑N q)
    p′
    with rebaseAtBackward sup rb
... | Wᵖˣ , mpᵖ , supᵖ , rbᵖ =
  CTI2.conceal⊑conceal²
    (center-map-matched-conceal-partner-ok mpᵖ ok)
    (center-map-imp-mono mp mpᵖ mono) rbᵖ
    (center-map-same-ctx mp mpᵖ sc)
    (center-map-source-⊢↓ mp c⊢) (center-map-target-⊢↓ mp c′⊢)
    (⊢²-center-map mpᵖ supᵖ M⊑N (center-map-⊑ᵂ mpᵖ p))
    p′
⊢²-center-map mp sup
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} {p★ = p★}
      {qᵖ = qᵖ} ok mono rb sc c⊢ c′⊢ M⊑N sourcePrem q)
    p′
    with rebaseAtBackward sup rb
... | Wᵖˣ , mpᵖ , supᵖ , rbᵖ =
  CTI2.packaged-seal-star²
    (center-map-matched-conceal-partner-ok mpᵖ ok)
    (center-map-imp-mono mp mpᵖ mono) rbᵖ
    (center-map-same-ctx mp mpᵖ sc)
    (center-map-source-⊢↓ mp c⊢) (center-map-target-⊢↓ mp c′⊢)
    (⊢²-center-map mpᵖ supᵖ M⊑N (center-map-⊑ᵂ mpᵖ p★))
    (⊢²-center-map mpᵖ supᵖ sourcePrem (center-map-⊑ᵂ mpᵖ qᵖ))
    p′
⊢²-center-map {γ = γ} mp sup (CTI2.blame⊑² M′⊢ p) p′ =
  CTI2.blame⊑²
    (subst≡ (λ Σ → ⟨ _ , Σ , CTI2.tgtCtxʷ (center-map-ctx mp γ) ⟩
        ⊢ _ ⦂ _)
      (sym (targetStore-map mp))
      (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
        (sym (center-map-ctx-tgt mp γ)) M′⊢))
    p′
⊢²-center-map mp sup
    (CTI2.⊕⊑⊕² op {p = p} {q = q} L⊑L′ M⊑M′ r) p′ =
  CTI2.⊕⊑⊕² op
    (⊢²-center-map mp sup L⊑L′ (center-map-⊑ᵂ mp p))
    (⊢²-center-map mp sup M⊑M′ (center-map-⊑ᵂ mp q)) p′


swap01-left-right-source : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (A : Ty (suc Δ₀))
  → renameᵗ swap01 (renameᵗ (toRenameᵗ (skip (keep η))) A)
    ≡ renameᵗ (toRenameᵗ (keep (skip η))) A
swap01-left-right-source η A =
  trans (renameᵗ-comp (toRenameᵗ (skip (keep η))) swap01 A)
    (renameᵗ-cong A eq)
  where
  eq : ∀ X
    → swap01 (toRenameᵗ (skip (keep η)) X)
      ≡ toRenameᵗ (keep (skip η)) X
  eq Fin.zero = refl
  eq (Fin.suc X) = refl


swap01-left-right-target : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (B : Ty (suc Δ₀))
  → renameᵗ swap01 (renameᵗ (toRenameᵗ (keep (skip η))) B)
    ≡ renameᵗ (toRenameᵗ (skip (keep η))) B
swap01-left-right-target η B =
  trans (renameᵗ-comp (toRenameᵗ (keep (skip η))) swap01 B)
    (renameᵗ-cong B eq)
  where
  eq : ∀ X
    → swap01 (toRenameᵗ (keep (skip η)) X)
      ≡ toRenameᵗ (skip (keep η)) X
  eq Fin.zero = refl
  eq (Fin.suc X) = refl


left-right-swap-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.instᵐ (I.extendᵐ I.X⊑★ μ) X ≡ I.X⊑★
  → I.extendᵐ I.X⊑★ (I.instᵐ μ) (swap01 X) ≡ I.X⊑★
left-right-swap-star-map Fin.zero eq = refl
left-right-swap-star-map (Fin.suc Fin.zero) eq = refl
left-right-swap-star-map (Fin.suc (Fin.suc X)) eq = eq


left-right-swap-star-unmap : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.extendᵐ I.X⊑★ (I.instᵐ μ) (swap01 X) ≡ I.X⊑★
  → I.instᵐ (I.extendᵐ I.X⊑★ μ) X ≡ I.X⊑★
left-right-swap-star-unmap Fin.zero eq = refl
left-right-swap-star-unmap (Fin.suc Fin.zero) eq = refl
left-right-swap-star-unmap (Fin.suc (Fin.suc X)) eq = eq


right-left-center-map : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
  → CenterMapWorld swap01
      (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B′)
      (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′))
right-left-center-map {W = W} = record
  { map-injective = swap01-injective
  ; map-involutive = swap01-involutive
  ; source-center-map = λ X →
      sym (adjacent-swap-ope-rename
        (top-source-swap-ope {η = CTI2.ηᴸʷ W}) X)
  ; target-center-map = λ X →
      sym (adjacent-swap-ope-rename
        (top-target-swap-ope {η = CTI2.ηᴿʷ W}) X)
  ; impEnv-map = left-right-swap-star-map
  ; impEnv-unmap = left-right-swap-star-unmap
  ; sourceStore-map = refl
  ; targetStore-map = refl
  }


right-left-rebase-atᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {Wᵖ : CTI2.World (suc Δᴸ) (suc Δᴿ) (suc (suc Δ))}
    {Xᴿ? : Maybe (TyVar (suc Δᴿ))}
  → CTI2.RebaseAtᴿ
      (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B′)
      Wᵖ Xᴿ?
  → Σ[ Wᵖˣ ∈ CTI2.World (suc Δᴸ) (suc Δᴿ) (suc (suc Δ)) ]
      CenterMapWorld swap01 Wᵖ Wᵖˣ
      × CTI2.RebaseAtᴿ
          (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′))
          Wᵖˣ Xᴿ?
right-left-rebase-atᴿ {W = W} {B′ = B′} CTI2.rebase-idᴿ =
  CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′) ,
  right-left-center-map {W = W} {B′ = B′} ,
  CTI2.rebase-idᴿ
right-left-rebase-atᴿ {W = W} {B′ = B′} {Wᵖ = Wᵖ}
    (CTI2.rebase-varᴿ rb@(CTI2.rebase-at runtime offL frozenR
      aligned reps))
    with swap01-reify-ope
      (top-source-off-no-keep-keep
        {η = CTI2.ηᴸʷ W} {η′ = CTI2.ηᴸʷ Wᵖ} offL)
... | ηᴸˣ , src-ope
    with swap01-reify-ope
      (top-target-frozen-no-keep-keep
        {η = CTI2.ηᴿʷ W} {η′ = CTI2.ηᴿʷ Wᵖ} frozenR)
... | ηᴿˣ , tgt-ope =
  Wᵖˣ , mpᵖ ,
  CTI2.rebase-varᴿ
    (center-map-rebase-at
      (right-left-center-map {W = W} {B′ = B′}) mpᵖ rb)
  where
  src-adj = adj-swap01 src-ope

  tgt-adj = adj-swap01 tgt-ope

  Wᵖˣ = swapWorld Wᵖ src-adj tgt-adj

  mpᵖ = swapWorld-map swap01-injective swap01-involutive
    src-adj tgt-adj


right-left-exchange-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B′ : Ty Δᴿ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B′
    ⟩ B
  → A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′)
    ⟩ B
right-left-exchange-⊑ᵂ {W = W} {B′ = B′} {A = A} {B = B} p =
  subst≡
    (λ L → CTI2.impEnvʷ Wout ⊢ L ⊑ CTI2.embedᴿ Wout B)
    (swap01-left-right-source (CTI2.ηᴸʷ W) A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wout ⊢
        renameᵗ swap01 (CTI2.embedᴸ Win A) ⊑ R)
      (swap01-left-right-target (CTI2.ηᴿʷ W) B)
      (rename-⊑ swap01 swap01-injective
        left-right-swap-star-map p))
  where
  Win =
    CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B′

  Wout =
    CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B′)


swap12-left-right-source : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (A : Ty (suc Δ₀))
  → renameᵗ swap12
      (renameᵗ (toRenameᵗ (skip (skip (keep η)))) A)
    ≡ renameᵗ (toRenameᵗ (skip (keep (skip η)))) A
swap12-left-right-source η A =
  trans (renameᵗ-comp (toRenameᵗ (skip (skip (keep η)))) swap12 A)
    (renameᵗ-cong A eq)
  where
  eq : ∀ X
    → swap12 (toRenameᵗ (skip (skip (keep η))) X)
      ≡ toRenameᵗ (skip (keep (skip η))) X
  eq Fin.zero = refl
  eq (Fin.suc X) = refl


swap12-left-right-target : ∀ {Δ₀ Δ} (η : Δ₀ ↪ᵗ Δ)
    (B : Ty (suc (suc Δ₀)))
  → renameᵗ swap12
      (renameᵗ (toRenameᵗ (keep (keep (skip η)))) B)
    ≡ renameᵗ (toRenameᵗ (keep (skip (keep η)))) B
swap12-left-right-target η B =
  trans (renameᵗ-comp (toRenameᵗ (keep (keep (skip η)))) swap12 B)
    (renameᵗ-cong B eq)
  where
  eq : ∀ X
    → swap12 (toRenameᵗ (keep (keep (skip η))) X)
      ≡ toRenameᵗ (keep (skip (keep η))) X
  eq Fin.zero = refl
  eq (Fin.suc Fin.zero) = refl
  eq (Fin.suc (Fin.suc X)) = refl


left-right-swap12-star-map : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.instᵐ (I.instᵐ (I.extendᵐ I.X⊑★ μ)) X ≡ I.X⊑★
  → I.instᵐ (I.extendᵐ I.X⊑★ (I.instᵐ μ)) (swap12 X) ≡ I.X⊑★
left-right-swap12-star-map Fin.zero eq = refl
left-right-swap12-star-map (Fin.suc Fin.zero) eq = refl
left-right-swap12-star-map (Fin.suc (Fin.suc Fin.zero)) eq = refl
left-right-swap12-star-map (Fin.suc (Fin.suc (Fin.suc X))) eq = eq


left-right-swap12-star-unmap : ∀ {Δ} {μ : I.ImpEnv Δ}
  → ∀ X
  → I.instᵐ (I.extendᵐ I.X⊑★ (I.instᵐ μ)) (swap12 X) ≡ I.X⊑★
  → I.instᵐ (I.instᵐ (I.extendᵐ I.X⊑★ μ)) X ≡ I.X⊑★
left-right-swap12-star-unmap Fin.zero eq = refl
left-right-swap12-star-unmap (Fin.suc Fin.zero) eq = refl
left-right-swap12-star-unmap (Fin.suc (Fin.suc Fin.zero)) eq = refl
left-right-swap12-star-unmap (Fin.suc (Fin.suc (Fin.suc X))) eq = eq


right-left-under-right-center-map : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B₁ : Ty Δᴿ} {B₂ : Ty (suc Δᴿ)}
  → CenterMapWorld swap12
      (CTI2.rightOnlyWorld
        (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B₁)
        B₂)
      (CTI2.rightOnlyWorld
        (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B₁))
        B₂)
right-left-under-right-center-map {W = W} = record
  { map-injective = swap12-injective
  ; map-involutive = swap12-involutive
  ; source-center-map = λ X →
      sym (adjacent-swap-ope-rename
        (under-right-source-swap-ope {η = CTI2.ηᴸʷ W}) X)
  ; target-center-map = λ X →
      sym (adjacent-swap-ope-rename
        (under-right-target-swap-ope {η = CTI2.ηᴿʷ W}) X)
  ; impEnv-map = left-right-swap12-star-map
  ; impEnv-unmap = left-right-swap12-star-unmap
  ; sourceStore-map = refl
  ; targetStore-map = refl
  }


right-left-under-right-rebase-atᴿ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {B₁ : Ty Δᴿ} {B₂ : Ty (suc Δᴿ)}
    {Wᵖ : CTI2.World
      (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))}
    {Xᴿ? : Maybe (TyVar (suc (suc Δᴿ)))}
  → CTI2.RebaseAtᴿ
      (CTI2.rightOnlyWorld
        (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B₁)
        B₂)
      Wᵖ Xᴿ?
  → Σ[ Wᵖˣ ∈ CTI2.World
        (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ))) ]
      CenterMapWorld swap12 Wᵖ Wᵖˣ
      × CTI2.RebaseAtᴿ
          (CTI2.rightOnlyWorld
            (CTI2.liftWorldLeft I.X⊑★
              (CTI2.rightOnlyWorld W B₁))
            B₂)
          Wᵖˣ Xᴿ?
right-left-under-right-rebase-atᴿ {W = W} {B₁ = B₁} {B₂ = B₂}
    CTI2.rebase-idᴿ =
  CTI2.rightOnlyWorld
    (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B₁))
    B₂ ,
  right-left-under-right-center-map {W = W} {B₁ = B₁} {B₂ = B₂} ,
  CTI2.rebase-idᴿ
right-left-under-right-rebase-atᴿ
    {W = W} {B₁ = B₁} {B₂ = B₂} {Wᵖ = Wᵖ}
    (CTI2.rebase-varᴿ rb@(CTI2.rebase-at runtime offL frozenR
      aligned reps))
    with under-right-source-reify-ope
      {η = CTI2.ηᴸʷ W} {η′ = CTI2.ηᴸʷ Wᵖ} offL
... | ηᴸˣ , src-adj
    with under-right-target-reify-ope
      {η = CTI2.ηᴿʷ W} {η′ = CTI2.ηᴿʷ Wᵖ} frozenR
... | ηᴿˣ , tgt-adj =
  Wᵖˣ , mpᵖ ,
  CTI2.rebase-varᴿ
    (center-map-rebase-at
      (right-left-under-right-center-map
        {W = W} {B₁ = B₁} {B₂ = B₂})
      mpᵖ rb)
  where
  Wᵖˣ = swapWorld Wᵖ src-adj tgt-adj

  mpᵖ = swapWorld-map swap12-injective swap12-involutive
    src-adj tgt-adj


right-left-under-right-exchange-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ} {B₁ : Ty Δᴿ}
    {B₂ : Ty (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
  → A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld
        (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B₁)
        B₂
    ⟩ B
  → A CTI2.⊑ᵂ⟨
      CTI2.rightOnlyWorld
        (CTI2.liftWorldLeft I.X⊑★
          (CTI2.rightOnlyWorld W B₁))
        B₂
    ⟩ B
right-left-under-right-exchange-⊑ᵂ
    {W = W} {B₁ = B₁} {B₂ = B₂} {A = A} {B = B} p =
  subst≡
    (λ L → CTI2.impEnvʷ Wout ⊢ L ⊑ CTI2.embedᴿ Wout B)
    (swap12-left-right-source (CTI2.ηᴸʷ W) A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wout ⊢
        renameᵗ swap12 (CTI2.embedᴸ Win A) ⊑ R)
      (swap12-left-right-target (CTI2.ηᴿʷ W) B)
      (rename-⊑ swap12 swap12-injective
        left-right-swap12-star-map p))
  where
  Win =
    CTI2.rightOnlyWorld
      (CTI2.rightOnlyWorld (CTI2.liftWorldLeft I.X⊑★ W) B₁)
      B₂

  Wout =
    CTI2.rightOnlyWorld
      (CTI2.liftWorldLeft I.X⊑★ (CTI2.rightOnlyWorld W B₁))
      B₂


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
