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
   applyStores; applyTys; applyBody; applyVar; applyConsistency;
   applyConsistencies)
import TermCtx as T
import CastTerms as CT
open import CastTerms using
  (⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _⦂∀_[_]; _↑_; Λ_; ⇑ᵗᵐ;
   Value; RevealValue; _《_》; _↓_)
open import FunExt using (funext)
open import proof.Consistency using
  (gen-safe; castSize-subst-left-∼; castSize-subst-right-∼)
open import proof.Reduction using (cast-↠)
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (ext-injective; fin-suc-injective; nonstar-from-≢★; rename-⊑;
   source-nonvar-from-target; source-nonvar-target; source-occurs-target;
   subst-⊑; subst-zero-occurs-exts; target-occurs-source;
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


∀⊑ᵂ-from-left-lift : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ B
  → `∀ A CTI2.⊑ᵂ⟨ W ⟩ B
∀⊑ᵂ-from-left-lift {W = W} {A = A} {B = B} Anv zero∈A body-p =
  subst≡
    (λ L → CTI2.impEnvʷ W ⊢ `∀ L ⊑ CTI2.embedᴿ W B)
    (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ W)))
    (I.∀⊑
      (renameNonVar
        (toRenameᵗ (keep (CTI2.ηᴸʷ W))) Anv)
      (rename-occurs
        (toRenameᵗ (keep (CTI2.ηᴸʷ W))) zero∈A)
      (subst≡
        (λ R → I.instᵐ (CTI2.impEnvʷ W)
          ⊢ renameᵗ (toRenameᵗ (keep (CTI2.ηᴸʷ W))) A
            ⊑ R)
        (target-left-lift-eq (CTI2.ηᴿʷ W) B)
        body-p))


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


route1Innerρ : ∀ {Δ Δ₁ Δ₂}
  → suc Δ ↪ᵗ Δ₁
  → suc Δ₁ ↪ᵗ Δ₂
  → TyVar (suc Δ)
  → TyVar (suc Δ₂)
route1Innerρ κ₁ κ₂ X =
  Fin.suc (toRenameᵗ κ₂ (Fin.suc (toRenameᵗ κ₁ X)))


route1Innerρ-injective : ∀ {Δ Δ₁ Δ₂}
    (κ₁ : suc Δ ↪ᵗ Δ₁) (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
    {X Y : TyVar (suc Δ)}
  → route1Innerρ κ₁ κ₂ X ≡ route1Innerρ κ₁ κ₂ Y
  → X ≡ Y
route1Innerρ-injective κ₁ κ₂ eq =
  toRenameᵗ-injective κ₁
    (fin-suc-injective
      (toRenameᵗ-injective κ₂ (fin-suc-injective eq)))


route1OldCenter : ∀ {Δ Δ₁ Δ₂}
  → suc Δ ↪ᵗ Δ₁
  → suc Δ₁ ↪ᵗ Δ₂
  → TyVar Δ
  → TyVar (suc Δ₂)
route1OldCenter κ₁ κ₂ Z = route1Innerρ κ₁ κ₂ (Fin.suc Z)


route1SplitSource : ∀ {Δ Δ₁ Δ₂}
  → suc Δ ↪ᵗ Δ₁
  → suc Δ₁ ↪ᵗ Δ₂
  → TyVar (suc Δ)
  → Ty (suc Δ₂)
route1SplitSource κ₁ κ₂ Fin.zero = ＇ Fin.zero
route1SplitSource κ₁ κ₂ (Fin.suc Z) =
  ＇ route1OldCenter κ₁ κ₂ Z


route1SplitTarget★ : ∀ {Δ Δ₁ Δ₂}
  → suc Δ ↪ᵗ Δ₁
  → suc Δ₁ ↪ᵗ Δ₂
  → TyVar (suc Δ)
  → Ty (suc Δ₂)
route1SplitTarget★ κ₁ κ₂ Fin.zero = ★
route1SplitTarget★ κ₁ κ₂ (Fin.suc Z) =
  ＇ route1OldCenter κ₁ κ₂ Z


ΛRouteOneFreshWorldAt : ∀ {Δᴸ Δᴿ Δ₁ Δ₂}
  → (W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁)
  → (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
  → TyStore (suc (suc Δᴿ))
  → CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc Δ₂)
ΛRouteOneFreshWorldAt W₁ κ₂ Σ₂ =
  TBL.targetStoreAs
    (CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁))
    Σ₂


ΛRouteOneFreshWorldAtᴸ : ∀ {Δᴸ Δᴿ Δ₁ Δ₂}
  → (W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁)
  → (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
  → TyStore (suc (suc Δᴿ))
  → CTI2.World (suc (suc Δᴸ)) (suc (suc Δᴿ))
      (suc (suc Δ₂))
ΛRouteOneFreshWorldAtᴸ W₁ κ₂ Σ₂ =
  TBL.targetStoreAs
    (CR.renameWorld (skip (keep κ₂))
      (CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ W₁)))
    Σ₂


ΛRouteOneMidWorldAt : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
  → (W : CTI2.World Δᴸ Δᴿ Δ)
  → (W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂)
  → (κ₁ : suc Δ ↪ᵗ Δ₁)
  → (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
  → CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc Δ₂)
ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ =
  CTI2.world
    (skip (κ₂ CR.∘↪ skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))))
    (skip (CTI2.ηᴿʷ W₂))
    (CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W₂))
    (CTI2.sourceStoreʷ (CTI2.liftWorldLeft I.X⊑★ W₂))
    (CTI2.targetStoreʷ W₂)


record ΛRouteOneWindowFacts {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    (κ₁ : suc Δ ↪ᵗ Δ₁)
    (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
    (ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁)
    (ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂) : Set where
  field
    targetWindow₁ : TE.TargetWindowInsert ins₁ κ₁
    targetWindow₂ : TE.TargetWindowInsert ins₂ κ₂
    pivotMark :
      CTI2.impEnvʷ
        (CR.renameWorld (skip κ₂)
          (CTI2.liftWorldBoth I.X⊑★ W₁))
        (toRenameᵗ
          (CTI2.ηᴿʷ
            (CR.renameWorld (skip κ₂)
              (CTI2.liftWorldBoth I.X⊑★ W₁)))
          Fin.zero)
        ≡ I.X⊑★
    targetStoreTransport :
      StoreTransport (store-lift (CTI2.targetStoreʷ W₁))
        (CTI2.targetStoreʷ W₂)
    firstTargetZeroResolves :
      CTI2.resolveVar (CTI2.targetStoreʷ W₁) Fin.zero ≡ ★
    targetZeroResolves :
      CTI2.resolveVar (CTI2.targetStoreʷ W₂) Fin.zero ≡ ★
    targetOtherResolves : ∀ Z
      → Z ≢ Fin.zero
      → CTI2.resolveVar (CTI2.targetStoreʷ W₂) Z
          ≡ CTI2.resolveVar (store-lift (CTI2.targetStoreʷ W₁)) Z
    midSourcePivotMark :
      CTI2.impEnvʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
        (toRenameᵗ
          (CTI2.ηᴸʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂))
          Fin.zero)
        ≡ I.X⊑★

open ΛRouteOneWindowFacts public


route1-source₁ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → toRenameᵗ (CTI2.ηᴸʷ W₁) X
    ≡ toRenameᵗ κ₁
        (Fin.suc (toRenameᵗ (CTI2.ηᴸʷ W) X))
route1-source₁ {W = W} {κ₁ = κ₁} {ins₁ = ins₁} facts X =
  trans (TE.source-insert ins₁ X)
    (TE.window-old (ΛRouteOneWindowFacts.targetWindow₁ facts)
      (toRenameᵗ (CTI2.ηᴸʷ W) X))


route1-source₂ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → toRenameᵗ (CTI2.ηᴸʷ W₂) X
    ≡ toRenameᵗ κ₂
        (Fin.suc (toRenameᵗ κ₁
          (Fin.suc (toRenameᵗ (CTI2.ηᴸʷ W) X))))
route1-source₂ {W = W} {W₁ = W₁} {π₂ = π₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {ins₂ = ins₂} facts X =
  trans (TE.source-insert ins₂ X)
    (trans (cong (toRenameᵗ π₂) (route1-source₁ facts X))
      (TE.window-old (ΛRouteOneWindowFacts.targetWindow₂ facts)
        (toRenameᵗ κ₁
          (Fin.suc (toRenameᵗ (CTI2.ηᴸʷ W) X)))))


route1-target₁ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ Y
  → toRenameᵗ (CTI2.ηᴿʷ W₁) (Fin.suc Y)
    ≡ toRenameᵗ κ₁
        (Fin.suc (toRenameᵗ (CTI2.ηᴿʷ W) Y))
route1-target₁ {W = W} {W₁ = W₁} {κ₁ = κ₁}
    {ins₁ = ins₁} facts Y =
  subst≡
    (λ Y′ → toRenameᵗ (CTI2.ηᴿʷ W₁) Y′
      ≡ toRenameᵗ κ₁
          (Fin.suc (toRenameᵗ (CTI2.ηᴿʷ W) Y)))
    (toRename-wk-eq Y)
    (trans (TE.target-insert ins₁ Y)
      (TE.window-old (ΛRouteOneWindowFacts.targetWindow₁ facts)
        (toRenameᵗ (CTI2.ηᴿʷ W) Y)))


route1-target-zero₂ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → toRenameᵗ (CTI2.ηᴿʷ W₂) (Fin.suc Fin.zero)
    ≡ toRenameᵗ κ₂ (Fin.suc (toRenameᵗ κ₁ Fin.zero))
route1-target-zero₂ {W₁ = W₁} {W₂ = W₂} {π₂ = π₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {ins₂ = ins₂} facts =
  subst≡
    (λ Y′ → toRenameᵗ (CTI2.ηᴿʷ W₂) Y′
      ≡ toRenameᵗ κ₂ (Fin.suc (toRenameᵗ κ₁ Fin.zero)))
    (toRename-wk-eq Fin.zero)
    (trans (TE.target-insert ins₂ Fin.zero)
      (trans (cong (toRenameᵗ π₂)
        (TE.window-zero (ΛRouteOneWindowFacts.targetWindow₁ facts)))
        (TE.window-old (ΛRouteOneWindowFacts.targetWindow₂ facts)
          (toRenameᵗ κ₁ Fin.zero))))


route1-target₂ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ Y
  → toRenameᵗ (CTI2.ηᴿʷ W₂) (Fin.suc (Fin.suc Y))
    ≡ toRenameᵗ κ₂
        (Fin.suc (toRenameᵗ κ₁
          (Fin.suc (toRenameᵗ (CTI2.ηᴿʷ W) Y))))
route1-target₂ {W = W} {W₁ = W₁} {W₂ = W₂} {π₂ = π₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {ins₂ = ins₂} facts Y =
  subst≡
    (λ Y′ → toRenameᵗ (CTI2.ηᴿʷ W₂) Y′
      ≡ toRenameᵗ κ₂
          (Fin.suc (toRenameᵗ κ₁
            (Fin.suc (toRenameᵗ (CTI2.ηᴿʷ W) Y)))))
    (toRename-wk-eq (Fin.suc Y))
    (trans (TE.target-insert ins₂ (Fin.suc Y))
      (trans (cong (toRenameᵗ π₂) (route1-target₁ facts Y))
        (TE.window-old (ΛRouteOneWindowFacts.targetWindow₂ facts)
          (toRenameᵗ κ₁
            (Fin.suc (toRenameᵗ (CTI2.ηᴿʷ W) Y))))))


route1-old-mark-out : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ Z
  → CTI2.impEnvʷ W Z ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
      (route1OldCenter κ₁ κ₂ Z) ≡ I.X⊑★
route1-old-mark-out {W₁ = W₁} {W₂ = W₂}
    {κ₁ = κ₁} {ins₁ = ins₁} {ins₂ = ins₂} facts Z old-star =
  subst≡
    (λ C → CTI2.impEnvʷ W₂ C ≡ I.X⊑★)
    (TE.window-old (targetWindow₂ facts)
      (toRenameᵗ κ₁ (Fin.suc Z)))
    (trans (TE.impEnv-insert ins₂
        (toRenameᵗ κ₁ (Fin.suc Z)))
      old-star₁)
  where
  old-star₁ :
      CTI2.impEnvʷ W₁ (toRenameᵗ κ₁ (Fin.suc Z)) ≡ I.X⊑★
  old-star₁ =
    subst≡ (λ C → CTI2.impEnvʷ W₁ C ≡ I.X⊑★)
      (TE.window-old (targetWindow₁ facts) Z)
      (trans (TE.impEnv-insert ins₁ Z) old-star)


window-zero-off : ∀ {Δ Δ′}
    {π : Δ ↪ᵗ Δ′} {κ : suc Δ ↪ᵗ Δ′}
  → CR.EmbeddingWindow π κ
  → CR.preimage? π (toRenameᵗ κ Fin.zero) ≡ nothing
window-zero-off CR.window-here = refl
window-zero-off (CR.window-skip win) = window-zero-off win


route1-mid-source-pivot-from-windows : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁} {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁} {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → TE.TargetWindowInsert ins₁ κ₁
  → TE.TargetWindowInsert ins₂ κ₂
  → CTI2.impEnvʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (toRenameᵗ (CTI2.ηᴸʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂))
        Fin.zero) ≡ I.X⊑★
route1-mid-source-pivot-from-windows {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {ins₁ = ins₁} {ins₂ = ins₂}
    win₁ win₂ =
  subst≡ (λ C → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W₂) C
      ≡ I.X⊑★)
    (sym point-eq) star₂
  where
  star₁ = TE.impEnv-off-insert ins₁
    (window-zero-off (TE.windowEmbedding win₁))
  star₂ = subst≡ (λ C → CTI2.impEnvʷ W₂ C ≡ I.X⊑★)
    (TE.window-old win₂ (toRenameᵗ κ₁ Fin.zero))
    (trans (TE.impEnv-insert ins₂ (toRenameᵗ κ₁ Fin.zero)) star₁)
  point-eq = cong Fin.suc
    (trans
      (CR.toRenameᵗ-∘ κ₂ (skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W)))
        Fin.zero)
      (cong (toRenameᵗ κ₂) (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₁ (keep (CTI2.ηᴸʷ W)) Fin.zero))))


route1-split★-same : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
      ⊢ route1SplitSource κ₁ κ₂ X ⊑ route1SplitTarget★ κ₁ κ₂ X
route1-split★-same facts Fin.zero = I.X⊑★ refl
route1-split★-same facts (Fin.suc X) = I.X⊑X


route1-split★-star : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑X W) X ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
      ⊢ route1SplitSource κ₁ κ₂ X ⊑ ★
route1-split★-star facts Fin.zero ()
route1-split★-star facts (Fin.suc X) eq =
  I.X⊑★ (route1-old-mark-out facts X eq)


route1-inner-star-map : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑X W) X ≡ I.X⊑★
  → CTI2.impEnvʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (route1Innerρ κ₁ κ₂ X) ≡ I.X⊑★
route1-inner-star-map facts Fin.zero ()
route1-inner-star-map facts (Fin.suc X) eq =
  route1-old-mark-out facts X eq


route1-source-split-eq : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → (A : Ty (suc Δᴸ))
  → substᵗ (route1SplitSource κ₁ κ₂)
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
    ≡ CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W₂) A
route1-source-split-eq {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} facts A =
  trans (substᵗ-rename (route1SplitSource κ₁ κ₂)
      (toRenameᵗ (keep (CTI2.ηᴸʷ W))) A)
    (trans (substᵗ-cong A var-eq)
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W₂))) A))
  where
  var-eq : ∀ X
    → route1SplitSource κ₁ κ₂
        (toRenameᵗ (keep (CTI2.ηᴸʷ W)) X)
      ≡ ＇ toRenameᵗ
          (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W₂)) X
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) =
    cong ＇_ (cong Fin.suc (sym (route1-source₂ facts X)))


route1-target-split★-eq : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → (B : Ty (suc Δᴿ))
  → substᵗ (route1SplitTarget★ κ₁ κ₂)
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
    ≡ CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ W₂)
      (substᵗ Λ⊑Λ²TargetSplit₂ B)
route1-target-split★-eq {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} facts B =
  trans (substᵗ-rename (route1SplitTarget★ κ₁ κ₂)
      (toRenameᵗ (keep (CTI2.ηᴿʷ W))) B)
    (trans (substᵗ-cong B var-eq)
      (sym (renameᵗ-subst
        (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W₂)))
        Λ⊑Λ²TargetSplit₂ B)))
  where
  var-eq : ∀ X
    → route1SplitTarget★ κ₁ κ₂
        (toRenameᵗ (keep (CTI2.ηᴿʷ W)) X)
      ≡ renameᵗ
          (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W₂)))
          (Λ⊑Λ²TargetSplit₂ X)
  var-eq Fin.zero = refl
  var-eq (Fin.suc X) =
    cong ＇_ (cong Fin.suc (sym (route1-target₂ facts X)))


Λ-route1-final-body-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W₂ ⟩
      substᵗ Λ⊑Λ²TargetSplit₂ B
Λ-route1-final-body-⊑ᵂ {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {A = A} {B = B} facts body-p =
  subst≡
    (λ L → CTI2.impEnvʷ Wout ⊢ L ⊑
      CTI2.embedᴿ Wout (substᵗ Λ⊑Λ²TargetSplit₂ B))
    (route1-source-split-eq facts A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wout ⊢
        substᵗ (route1SplitSource κ₁ κ₂)
          (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
        ⊑ R)
      (route1-target-split★-eq facts B)
      (subst₂-⊑ (route1-split★-same facts)
        (route1-split★-star facts) body-p))
  where
  Wout = CTI2.liftWorldLeft I.X⊑★ W₂


route1-source-inner-point : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    (κ₁ : suc Δ ↪ᵗ Δ₁) (κ₂ : suc Δ₁ ↪ᵗ Δ₂)
  → ∀ X
  → route1Innerρ κ₁ κ₂
      (toRenameᵗ (keep (CTI2.ηᴸʷ W)) X)
    ≡ toRenameᵗ
        (CTI2.ηᴸʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)) X
route1-source-inner-point {W = W} κ₁ κ₂ X =
  sym
    (trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂
          (skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))) X))
      (cong (λ C → Fin.suc (toRenameᵗ κ₂ (Fin.suc C)))
        (CR.toRenameᵗ-∘ κ₁ (keep (CTI2.ηᴸʷ W)) X)))


route1-source-inner-eq : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → (A : Ty (suc Δᴸ))
  → renameᵗ (route1Innerρ κ₁ κ₂)
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
    ≡ CTI2.embedᴸ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂) A
route1-source-inner-eq {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} facts A =
  trans
    (renameᵗ-comp (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
      (route1Innerρ κ₁ κ₂) A)
    (renameᵗ-cong A
      (route1-source-inner-point {W = W} {W₂ = W₂} κ₁ κ₂))


route1-target-inner-point : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → ∀ X
  → route1Innerρ κ₁ κ₂
      (toRenameᵗ (keep (CTI2.ηᴿʷ W)) X)
    ≡ toRenameᵗ
        (CTI2.ηᴿʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂))
        (Fin.suc X)
route1-target-inner-point facts Fin.zero =
  cong Fin.suc (sym (route1-target-zero₂ facts))
route1-target-inner-point facts (Fin.suc X) =
  cong Fin.suc (sym (route1-target₂ facts X))


route1-target-inner-eq : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → (B : Ty (suc Δᴿ))
  → renameᵗ (route1Innerρ κ₁ κ₂)
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
    ≡ CTI2.embedᴿ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
        (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
          (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B))
route1-target-inner-eq {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} facts B =
  trans
    (renameᵗ-comp (toRenameᵗ (keep (CTI2.ηᴿʷ W)))
      (route1Innerρ κ₁ κ₂) B)
    (trans (renameᵗ-cong B (route1-target-inner-point facts))
      (trans
        (sym (renameᵗ-comp Fin.suc
          (toRenameᵗ
            (CTI2.ηᴿʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂))) B))
        (sym (cong
          (CTI2.embedᴿ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂))
          (inner-reveal-target-eq B)))))


Λ-route1-inner-body-⊑ᵂ : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
        (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)
Λ-route1-inner-body-⊑ᵂ {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {A = A} {B = B} facts body-p =
  subst≡
    (λ L → CTI2.impEnvʷ Wmid ⊢ L ⊑
      CTI2.embedᴿ Wmid
        (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
          (renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B)))
    (route1-source-inner-eq facts A)
    (subst≡
      (λ R → CTI2.impEnvʷ Wmid ⊢
        renameᵗ (route1Innerρ κ₁ κ₂)
          (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
        ⊑ R)
      (route1-target-inner-eq facts B)
      (rename-⊑ (route1Innerρ κ₁ κ₂)
        (route1Innerρ-injective κ₁ κ₂)
        (route1-inner-star-map facts) body-p))
  where
  Wmid = ΛRouteOneMidWorldAt W W₂ κ₁ κ₂


Λ-route1-inner-body-⊑ᵂ-applyBody : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  → A CTI2.⊑ᵂ⟨ ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩
      replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) (applyBody (bind ★) B)
Λ-route1-inner-body-⊑ᵂ-applyBody {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {A = A} {B = B} facts body-p =
  subst≡
    (λ C → A CTI2.⊑ᵂ⟨ ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩ C)
    (sym (cong (replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)))
      (applyBody-bind★-eq B)))
    (Λ-route1-inner-body-⊑ᵂ facts body-p)


Λ-route1-context-target-suc-eq : ∀ {Δ} (B : Ty Δ)
  → applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
    ≡ renameᵗ Fin.suc (⇑ᵗ B)
Λ-route1-context-target-suc-eq B = refl


Λ-route1-context-target-double-eq : ∀ {Δ} (B : Ty Δ)
  → applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
    ≡ renameᵗ (λ X → Fin.suc (Fin.suc X)) B
Λ-route1-context-target-double-eq B =
  renameᵗ-comp Fin.suc Fin.suc B


Λ-route1-context-inner-target-eq : ∀ {Δ} (B : Ty Δ)
  → replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero))
      (applyBody (bind ★) (⇑ᵗ B))
    ≡ applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
Λ-route1-context-inner-target-eq B =
  trans (inner-reveal-target-eq-applyBody (⇑ᵗ B))
    (sym (Λ-route1-context-target-suc-eq B))


Λ-route1-context-final-target-eq : ∀ {Δ} (B : Ty Δ)
  → substᵗ Λ⊑Λ²TargetSplit₂ (⇑ᵗ B)
    ≡ applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
Λ-route1-context-final-target-eq B =
  trans (substᵗ-rename Λ⊑Λ²TargetSplit₂ Fin.suc B)
    (trans (substᵗ-cong B (λ X → refl))
      (trans (rename-as-subst (λ X → Fin.suc (Fin.suc X)) B)
        (sym (Λ-route1-context-target-double-eq B))))


Λ-route1-fresh-entry-raw-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ (⇑ᵗ B)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
Λ-route1-fresh-entry-raw-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₁ = π₁} {κ₂ = κ₂} {ins₁ = ins₁} {A = A} {B = B}
    facts p =
  pᵇ
  where
  ins₁ᴮ : TE.TargetInsert (keep wk↪ᵗ) (keep π₁)
      (CTI2.liftWorldBoth I.X⊑X W)
      (CTI2.liftWorldBoth I.X⊑X W₁)
  ins₁ᴮ = TE.liftBothTargetInsert {v = I.X⊑X} ins₁

  p₁ : (⇑ᵗ A) CTI2.⊑ᵂ⟨
        CTI2.liftWorldBoth I.X⊑X W₁
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
  p₁ = TE.transport⊑ᵂ ins₁ᴮ p

  pᵈ : (⇑ᵗ A) CTI2.⊑ᵂ⟨
        CTI2.liftWorldBoth I.X⊑★ W₁
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
  pᵈ =
    WD.decay⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑X W₁}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★ W₁}
      TD.liftBothBinderDecay p₁

  pʳ : (⇑ᵗ A) CTI2.⊑ᵂ⟨
        CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★ W₁}
      (skip κ₂) pᵈ

  mv : TBL.TargetBindLiftMove
      (CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁))
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
      Fin.zero
  mv =
    TBL.freshLiftToBindTargetMoveAtκ (skip κ₂)
      (ΛRouteOneWindowFacts.pivotMark facts)
      (ΛRouteOneWindowFacts.targetStoreTransport facts)
      (ΛRouteOneWindowFacts.targetZeroResolves facts)
      (ΛRouteOneWindowFacts.targetOtherResolves facts)

  pᵇ : (⇑ᵗ A) CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) (⇑ᵗ B)
  pᵇ = TBL.move⊑ᵂ (TBL.baseMove mv) pʳ


Λ-route1-fresh-entry-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ (⇑ᵗ B)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
Λ-route1-fresh-entry-at {W₁ = W₁} {W₂ = W₂}
    {κ₂ = κ₂} {A = A} {B = B} facts p =
  subst≡
    (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
      ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
    ⟩ C)
    (sym (Λ-route1-context-target-eq B))
    (Λ-route1-fresh-entry-raw-at facts p)


Λ-route1-fresh-ctx-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
Λ-route1-fresh-ctx-at facts CTI2.lift-[] = List.[]
Λ-route1-fresh-ctx-at facts
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (Λ-route1-fresh-entry-at facts p′) List.∷
  Λ-route1-fresh-ctx-at facts liftγ


Λ-route1-mid-entry-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ (⇑ᵗ B)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨
        ΛRouteOneMidWorldAt W W₂ κ₁ κ₂
      ⟩ applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
Λ-route1-mid-entry-at {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {A = A} {B = B} facts p =
  subst≡
    (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
      ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩ C)
    (Λ-route1-context-inner-target-eq B)
    (Λ-route1-inner-body-⊑ᵂ-applyBody facts p)


Λ-route1-out-entry-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ (⇑ᵗ B)
  → (⇑ᵗ A) CTI2.⊑ᵂ⟨
        CTI2.liftWorldLeft I.X⊑★ W₂
      ⟩ applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B
Λ-route1-out-entry-at {W₂ = W₂} {A = A} {B = B} facts p =
  subst≡
    (λ C → (⇑ᵗ A) CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W₂ ⟩ C)
    (Λ-route1-context-final-target-eq B)
    (Λ-route1-final-body-⊑ᵂ facts p)


Λ-route1-mid-ctx-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
Λ-route1-mid-ctx-at facts CTI2.lift-[] = List.[]
Λ-route1-mid-ctx-at facts
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (Λ-route1-mid-entry-at facts p′) List.∷
  Λ-route1-mid-ctx-at facts liftγ


Λ-route1-out-ctx-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W₂)
Λ-route1-out-ctx-at facts CTI2.lift-[] = List.[]
Λ-route1-out-ctx-at facts
    (CTI2.lift-∷ {A = A} {B = B} {p′ = p′} liftγ) =
  CTI2.ctx-imp (⇑ᵗ A)
    (applyTys (bind ★ ∷ bind (＇ Fin.zero) ∷ []) B)
    (Λ-route1-out-entry-at facts p′) List.∷
  Λ-route1-out-ctx-at facts liftγ


Λ-route1-mid-fresh-same-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.SameCtx (Λ-route1-mid-ctx-at facts liftγ)
      (Λ-route1-fresh-ctx-at facts liftγ)
Λ-route1-mid-fresh-same-at facts CTI2.lift-[] = CTI2.same-[]
Λ-route1-mid-fresh-same-at facts (CTI2.lift-∷ liftγ) =
  CTI2.same-∷ (Λ-route1-mid-fresh-same-at facts liftγ)


Λ-route1-out-mid-same-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.SameCtx (Λ-route1-out-ctx-at facts liftγ)
      (Λ-route1-mid-ctx-at facts liftγ)
Λ-route1-out-mid-same-at facts CTI2.lift-[] = CTI2.same-[]
Λ-route1-out-mid-same-at facts (CTI2.lift-∷ liftγ) =
  CTI2.same-∷ (Λ-route1-out-mid-same-at facts liftγ)


Λ-route1-out-liftCtxᴸ-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
      (Λ-route1-out-ctx-at facts liftγ)
Λ-route1-out-liftCtxᴸ-at facts CTI2.lift-[] = CTI2.liftᴸ-[]
Λ-route1-out-liftCtxᴸ-at facts (CTI2.lift-∷ liftγ) =
  CTI2.liftᴸ-∷ (Λ-route1-out-liftCtxᴸ-at facts liftγ)


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


record ΛPostWindowGeometry {Δᴸ Δᴿ Δ Δ₂}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂)
    (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂) : Set₁ where
  field
    freshWorld : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc Δ₂)
    midWorld : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) (suc Δ₂)

    route1Prefix : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
        {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
      → CTI2.LiftCtx I.X⊑X γ γᴮ
      → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
          ⊢² V ⊑ V′ ∶ body-p
      → Σ[ γᶠ ∈ CTI2.CtxImp freshWorld ]
        Σ[ pᶠ ∈ A CTI2.⊑ᵂ⟨ freshWorld ⟩ applyBody (bind ★) B ]
          freshWorld CTI2.∣ γᶠ
            ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ

    midCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → CTI2.LiftCtx I.X⊑X γ γᴮ
      → CTI2.CtxImp midWorld

    outCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → CTI2.LiftCtx I.X⊑X γ γᴮ
      → CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W₂)

    midFreshMono :
      CTI2.ImpEnvMono midWorld freshWorld

    innerRebaseᴿ :
      CTI2.RebaseAtᴿ midWorld freshWorld (just Fin.zero)

    midFreshSame : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
        {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → (bodyRel : CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
          ⊢² V ⊑ V′ ∶ body-p)
      → CTI2.SameCtx (midCtx liftγ)
          (proj₁ (route1Prefix liftγ bodyRel))

    outMidMono :
      CTI2.ImpEnvMono (CTI2.liftWorldLeft I.X⊑★ W₂) midWorld

    outerRebaseᴿ :
      CTI2.RebaseAtᴿ (CTI2.liftWorldLeft I.X⊑★ W₂) midWorld
        (just (Fin.suc Fin.zero))

    outMidSame : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.SameCtx (outCtx liftγ) (midCtx liftγ)

    outLiftCtxᴸ : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
          (outCtx liftγ)

    innerReveal⊢ : ∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ applyBody (bind ★) B
      → CTI2.targetStoreʷ midWorld CTI2.⊢↑[ just Fin.zero ]
          〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑ applyBody (bind ★) B 〗

    outerReveal⊢ : ∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ B
      → CTI2.targetStoreʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
          CTI2.⊢↑[ just (Fin.suc Fin.zero) ]
          rename↑ Fin.suc (〖 Fin.zero , ★ ↑ B 〗)

    innerBody⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
      → A CTI2.⊑ᵂ⟨ midWorld ⟩
          replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) (applyBody (bind ★) B)

    finalBody⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W₂ ⟩
          substᵗ Λ⊑Λ²TargetSplit₂ B

    outTargetCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.tgtCtxʷ (outCtx liftγ) ≡
          CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ)


Λ-route1-prefix-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γᶠ ∈ CTI2.CtxImp
        (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)) ]
    Σ[ pᶠ ∈ A CTI2.⊑ᵂ⟨
          ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
        ⟩ applyBody (bind ★) B ]
      ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γᶠ
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
Λ-route1-prefix-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₁ = π₁} {κ₂ = κ₂} {ins₁ = ins₁} {γᴮ = γᴮ} {V = V}
    {V′ = V′} {A = A} {B = B} {body-p = body-p} facts rel =
  γfresh , pᶠ , relFresh
  where
  ins₁ᴮ : TE.TargetInsert (keep wk↪ᵗ) (keep π₁)
      (CTI2.liftWorldBoth I.X⊑X W)
      (CTI2.liftWorldBoth I.X⊑X W₁)
  ins₁ᴮ = TE.liftBothTargetInsert {v = I.X⊑X} ins₁

  p₁ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W₁ ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  p₁ = TE.transport⊑ᵂ ins₁ᴮ body-p

  rel₁ : CTI2.liftWorldBoth I.X⊑X W₁
      CTI2.∣ TE.mapCtxᵀ ins₁ᴮ γᴮ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p₁
  rel₁ = TE.⊢²-target-insert ins₁ᴮ rel

  pᵈ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑★ W₁ ⟩
      renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵈ =
    WD.decay⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑X W₁}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★ W₁}
      TD.liftBothBinderDecay p₁

  relᵈ : CTI2.liftWorldBoth I.X⊑★ W₁
      CTI2.∣ WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ ins₁ᴮ γᴮ)
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵈ
  relᵈ =
    TD.⊢²-decay
      {W = CTI2.liftWorldBoth I.X⊑X W₁}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★ W₁}
      TD.liftBothBinderDecay rel₁

  pʳ : A CTI2.⊑ᵂ⟨
        CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★ W₁}
      (skip κ₂) pᵈ

  relʳ : CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁)
      CTI2.∣ CR.renameCtx (skip κ₂)
        (WD.decayCtx TD.liftBothBinderDecay
          (TE.mapCtxᵀ ins₁ᴮ γᴮ))
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pʳ
  relʳ = CR.⊢²-rename-center (skip κ₂) relᵈ pʳ

  mv : TBL.TargetBindLiftMove
      (CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁))
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
      Fin.zero
  mv =
    TBL.freshLiftToBindTargetMoveAtκ (skip κ₂)
      (ΛRouteOneWindowFacts.pivotMark facts)
      (ΛRouteOneWindowFacts.targetStoreTransport facts)
      (ΛRouteOneWindowFacts.targetZeroResolves facts)
      (ΛRouteOneWindowFacts.targetOtherResolves facts)

  γfresh : CTI2.CtxImp
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
  γfresh =
    TBL.moveCtx (TBL.baseMove mv)
      (CR.renameCtx (skip κ₂)
        (WD.decayCtx TD.liftBothBinderDecay
          (TE.mapCtxᵀ ins₁ᴮ γᴮ)))

  pᵇ : A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵇ = TBL.move⊑ᵂ (TBL.baseMove mv) pʳ

  relᵇ :
      ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γfresh
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
  relᵇ = TBL.⊢²-target-bind-lift-move mv relʳ

  pᶠ : A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ applyBody (bind ★) B
  pᶠ =
    subst≡
      (λ C → A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ C)
      (sym (applyBody-bind★-eq B))
      pᵇ

  relFresh :
      ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γfresh
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
  relFresh =
    rel-target-transportᴿ (sym (applyBody-bind★-eq B)) pᵇ relᵇ


Λ-route1ᴸ-prefix-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X
      (CTI2.liftWorldLeft I.X⊑★ W) ⟩ B}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γᶠ ∈ CTI2.CtxImp
        (ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)) ]
    Σ[ pᶠ ∈ A CTI2.⊑ᵂ⟨
          ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
        ⟩ applyBody (bind ★) B ]
      ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γᶠ
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
Λ-route1ᴸ-prefix-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₁ = π₁} {κ₂ = κ₂} {ins₁ = ins₁} {γᴮ = γᴮ}
    {V = V} {V′ = V′} {A = A} {B = B} {body-p = body-p}
    facts rel =
  γfresh , pᶠ , relFresh
  where
  ins₁ᴮ : TE.TargetInsert (keep wk↪ᵗ) (keep (keep π₁))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W))
      (CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W₁))
  ins₁ᴮ =
    TE.liftBothTargetInsert {v = I.X⊑X}
      (TE.liftLeftTargetInsert {v = I.X⊑★} ins₁)

  p₁ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X
          (CTI2.liftWorldLeft I.X⊑★ W₁)
        ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  p₁ = TE.transport⊑ᵂ ins₁ᴮ body-p

  rel₁ : CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W₁)
      CTI2.∣ TE.mapCtxᵀ ins₁ᴮ γᴮ
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ p₁
  rel₁ = TE.⊢²-target-insert ins₁ᴮ rel

  pᵈ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ W₁)
        ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵈ =
    WD.decay⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W₁)}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ W₁)}
      TD.liftBothBinderDecay p₁

  relᵈ : CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ W₁)
      CTI2.∣ WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ ins₁ᴮ γᴮ)
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵈ
  relᵈ =
    TD.⊢²-decay
      {W = CTI2.liftWorldBoth I.X⊑X
        (CTI2.liftWorldLeft I.X⊑★ W₁)}
      {Wᵈ = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ W₁)}
      TD.liftBothBinderDecay rel₁

  pʳ : A CTI2.⊑ᵂ⟨
        CR.renameWorld (skip (keep κ₂))
          (CTI2.liftWorldBoth I.X⊑★
            (CTI2.liftWorldLeft I.X⊑★ W₁))
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pʳ =
    CR.rename-⊑ᵂ
      {W = CTI2.liftWorldBoth I.X⊑★
        (CTI2.liftWorldLeft I.X⊑★ W₁)}
      (skip (keep κ₂)) pᵈ

  relʳ : CR.renameWorld (skip (keep κ₂))
        (CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ W₁))
      CTI2.∣ CR.renameCtx (skip (keep κ₂))
        (WD.decayCtx TD.liftBothBinderDecay
          (TE.mapCtxᵀ ins₁ᴮ γᴮ))
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pʳ
  relʳ = CR.⊢²-rename-center (skip (keep κ₂)) relᵈ pʳ

  mv : TBL.TargetBindLiftMove
      (CR.renameWorld (skip (keep κ₂))
        (CTI2.liftWorldBoth I.X⊑★
          (CTI2.liftWorldLeft I.X⊑★ W₁)))
      (ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂))
      Fin.zero
  mv =
    TBL.freshLiftToBindTargetMoveAtκᴸ (skip (keep κ₂))
      refl
      (ΛRouteOneWindowFacts.targetStoreTransport facts)
      (ΛRouteOneWindowFacts.targetZeroResolves facts)
      (ΛRouteOneWindowFacts.targetOtherResolves facts)

  γfresh : CTI2.CtxImp
      (ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂))
  γfresh =
    TBL.moveCtx (TBL.baseMove mv)
      (CR.renameCtx (skip (keep κ₂))
        (WD.decayCtx TD.liftBothBinderDecay
          (TE.mapCtxᵀ ins₁ᴮ γᴮ)))

  pᵇ : A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B
  pᵇ = TBL.move⊑ᵂ (TBL.baseMove mv) pʳ

  relᵇ :
      ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γfresh
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
  relᵇ = TBL.⊢²-target-bind-lift-move mv relʳ

  pᶠ : A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ applyBody (bind ★) B
  pᶠ =
    subst≡
      (λ C → A CTI2.⊑ᵂ⟨
        ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
      ⟩ C)
      (sym (applyBody-bind★-eq B))
      pᵇ

  relFresh :
      ΛRouteOneFreshWorldAtᴸ W₁ κ₂ (CTI2.targetStoreʷ W₂)
        CTI2.∣ γfresh
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
  relFresh =
    rel-target-transportᴿ (sym (applyBody-bind★-eq B)) pᵇ relᵇ


Λ-route1-prefix-map-ctx-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
  → CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)
  → CTI2.CtxImp
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
Λ-route1-prefix-map-ctx-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₁ = π₁} {κ₂ = κ₂} {ins₁ = ins₁} facts γᴮ =
  TBL.moveCtx (TBL.baseMove mv)
    (CR.renameCtx (skip κ₂)
      (WD.decayCtx TD.liftBothBinderDecay
        (TE.mapCtxᵀ ins₁ᴮ γᴮ)))
  where
  ins₁ᴮ : TE.TargetInsert (keep wk↪ᵗ) (keep π₁)
      (CTI2.liftWorldBoth I.X⊑X W)
      (CTI2.liftWorldBoth I.X⊑X W₁)
  ins₁ᴮ = TE.liftBothTargetInsert {v = I.X⊑X} ins₁

  mv : TBL.TargetBindLiftMove
      (CR.renameWorld (skip κ₂) (CTI2.liftWorldBoth I.X⊑★ W₁))
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
      Fin.zero
  mv =
    TBL.freshLiftToBindTargetMoveAtκ (skip κ₂)
      (ΛRouteOneWindowFacts.pivotMark facts)
      (ΛRouteOneWindowFacts.targetStoreTransport facts)
      (ΛRouteOneWindowFacts.targetZeroResolves facts)
      (ΛRouteOneWindowFacts.targetOtherResolves facts)


Λ-route1-prefix-map-ctx-at-eq : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → Λ-route1-prefix-map-ctx-at facts γᴮ
      ≡ Λ-route1-fresh-ctx-at facts liftγ
Λ-route1-prefix-map-ctx-at-eq facts CTI2.lift-[] = refl
Λ-route1-prefix-map-ctx-at-eq facts
    (CTI2.lift-∷ {B = B} {p′ = p′} liftγ) =
  cong₂ List._∷_
    (ctx-imp-transportᴿ
      (sym (Λ-route1-context-target-eq B))
      (Λ-route1-fresh-entry-raw-at facts p′))
    (Λ-route1-prefix-map-ctx-at-eq facts liftγ)


Λ-route1-prefix-at-ctx : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → (bodyRel : CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p)
  → proj₁ (Λ-route1-prefix-at facts bodyRel)
      ≡ Λ-route1-fresh-ctx-at facts liftγ
Λ-route1-prefix-at-ctx facts liftγ bodyRel =
  Λ-route1-prefix-map-ctx-at-eq facts liftγ


Λ-route1-inner-rebase-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.RebaseAtᴿ
      (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
      (just Fin.zero)
Λ-route1-inner-rebase-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₂ = π₂} {κ₁ = κ₁} {κ₂ = κ₂} {ins₁ = ins₁}
    {ins₂ = ins₂} facts =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at runtime source-off target-frozen
      fresh-zero-aligned store-rep)
  where
  win₁ = ΛRouteOneWindowFacts.targetWindow₁ facts
  win₂ = ΛRouteOneWindowFacts.targetWindow₂ facts

  Wfresh =
    ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)

  Wmid =
    ΛRouteOneMidWorldAt W W₂ κ₁ κ₂

  runtime : CTI2.SameRuntime Wmid Wfresh
  runtime =
    CTI2.same-runtime
      (sym (cong store-lift (TE.sourceStore-kept ins₂)))
      refl

  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ Wfresh) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ Wmid) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc X} neq =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂ (keep (CTI2.ηᴸʷ W₁)) (Fin.suc X)))
      (trans
        (cong (λ C → Fin.suc (toRenameᵗ κ₂ (Fin.suc C)))
          source₁)
        (cong Fin.suc
          (sym (CR.toRenameᵗ-∘ κ₂
            (skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))) (Fin.suc X)))))
    where
    source₁ :
        toRenameᵗ (CTI2.ηᴸʷ W₁) X
          ≡ toRenameᵗ (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W)) (Fin.suc X)
    source₁ =
      trans (TE.source-insert ins₁ X)
        (trans (TE.window-old win₁ (toRenameᵗ (CTI2.ηᴸʷ W) X))
          (sym (CR.toRenameᵗ-∘ κ₁ (keep (CTI2.ηᴸʷ W))
            (Fin.suc X))))

  target-zero :
      toRenameᵗ (CTI2.ηᴿʷ Wfresh) Fin.zero
        ≡ toRenameᵗ (CTI2.ηᴿʷ Wmid) Fin.zero
  target-zero =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂ (keep (CTI2.ηᴿʷ W₁)) Fin.zero))
      (cong Fin.suc (sym (TE.window-zero win₂)))

  target-suc : ∀ X
    → toRenameᵗ (CTI2.ηᴿʷ Wfresh) (Fin.suc X)
      ≡ toRenameᵗ (CTI2.ηᴿʷ Wmid) (Fin.suc X)
  target-suc X =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂ (keep (CTI2.ηᴿʷ W₁)) (Fin.suc X)))
      (cong Fin.suc
        (trans (sym (TE.window-old win₂
          (toRenameᵗ (CTI2.ηᴿʷ W₁) X)))
          (sym target-insert-suc)))
    where
    target-insert-suc :
        toRenameᵗ (CTI2.ηᴿʷ W₂) (Fin.suc X)
          ≡ toRenameᵗ π₂ (toRenameᵗ (CTI2.ηᴿʷ W₁) X)
    target-insert-suc =
      subst≡
        (λ Y → toRenameᵗ (CTI2.ηᴿʷ W₂) Y
          ≡ toRenameᵗ π₂ (toRenameᵗ (CTI2.ηᴿʷ W₁) X))
        (toRename-wk-eq X)
        (TE.target-insert ins₂ X)

  target-frozen : ∀ Y
    → toRenameᵗ (CTI2.ηᴿʷ Wfresh) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ Wmid) Y
  target-frozen Fin.zero = target-zero
  target-frozen (Fin.suc X) = target-suc X

  fresh-zero-aligned :
      toRenameᵗ (CTI2.ηᴸʷ Wfresh) Fin.zero
        ≡ toRenameᵗ (CTI2.ηᴿʷ Wfresh) Fin.zero
  fresh-zero-aligned =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂ (keep (CTI2.ηᴸʷ W₁)) Fin.zero))
      (sym (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂ (keep (CTI2.ηᴿʷ W₁)) Fin.zero)))

  sourcePivotMark :
      CTI2.impEnvʷ Wfresh
        (toRenameᵗ (CTI2.ηᴸʷ Wfresh) Fin.zero) ≡ I.X⊑★
  sourcePivotMark =
    subst≡ (λ C → CTI2.impEnvʷ Wfresh C ≡ I.X⊑★)
      (sym fresh-zero-aligned)
      (ΛRouteOneWindowFacts.pivotMark facts)

  store-rep : CTI2.StoreRepImp Wfresh Fin.zero Fin.zero
  store-rep =
    CTI2.store-rep-imp
      (subst≡
        (λ R → CTI2.resolveVar (CTI2.sourceStoreʷ Wfresh) Fin.zero
          CTI2.⊑ᵂ⟨ Wfresh ⟩ R)
        (sym (ΛRouteOneWindowFacts.targetZeroResolves facts))
        (I.X⊑★ sourcePivotMark))


Λ-route1-outer-rebase-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.RebaseAtᴿ
      (CTI2.liftWorldLeft I.X⊑★ W₂)
      (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (just (Fin.suc Fin.zero))
Λ-route1-outer-rebase-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {π₂ = π₂} {κ₁ = κ₁} {κ₂ = κ₂} {ins₁ = ins₁}
    {ins₂ = ins₂} facts =
  CTI2.rebase-varᴿ
    (CTI2.rebase-at runtime source-off target-frozen
      pivot-aligned store-rep)
  where
  win₁ = ΛRouteOneWindowFacts.targetWindow₁ facts
  win₂ = ΛRouteOneWindowFacts.targetWindow₂ facts

  Wmid =
    ΛRouteOneMidWorldAt W W₂ κ₁ κ₂

  Wout =
    CTI2.liftWorldLeft I.X⊑★ W₂

  runtime : CTI2.SameRuntime Wout Wmid
  runtime = CTI2.same-runtime refl refl

  source₁ : ∀ X
    → toRenameᵗ (CTI2.ηᴸʷ W₁) X
      ≡ toRenameᵗ (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W)) (Fin.suc X)
  source₁ X =
    trans (TE.source-insert ins₁ X)
      (trans (TE.window-old win₁ (toRenameᵗ (CTI2.ηᴸʷ W) X))
        (sym (CR.toRenameᵗ-∘ κ₁ (keep (CTI2.ηᴸʷ W))
          (Fin.suc X))))

  source₂ : ∀ X
    → toRenameᵗ (CTI2.ηᴸʷ W₂) X
      ≡ toRenameᵗ κ₂
          (Fin.suc
            (toRenameᵗ (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))
              (Fin.suc X)))
  source₂ X =
    trans (TE.source-insert ins₂ X)
      (trans (cong (toRenameᵗ π₂) (source₁ X))
        (TE.window-old win₂
          (toRenameᵗ (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))
            (Fin.suc X))))

  source-off : ∀ {Y}
    → Y ≢ Fin.zero
    → toRenameᵗ (CTI2.ηᴸʷ Wmid) Y
      ≡ toRenameᵗ (CTI2.ηᴸʷ Wout) Y
  source-off {Fin.zero} neq = ⊥-elim (neq refl)
  source-off {Fin.suc X} neq =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂
          (skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))) (Fin.suc X)))
      (cong Fin.suc (sym (source₂ X)))

  target-frozen : ∀ Y
    → toRenameᵗ (CTI2.ηᴿʷ Wmid) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ Wout) Y
  target-frozen Y = refl

  target-insert-suc-zero :
      toRenameᵗ (CTI2.ηᴿʷ W₂) (Fin.suc Fin.zero)
        ≡ toRenameᵗ π₂
          (toRenameᵗ (CTI2.ηᴿʷ W₁) Fin.zero)
  target-insert-suc-zero =
    subst≡
      (λ Y → toRenameᵗ (CTI2.ηᴿʷ W₂) Y
        ≡ toRenameᵗ π₂
          (toRenameᵗ (CTI2.ηᴿʷ W₁) Fin.zero))
      (toRename-wk-eq Fin.zero)
      (TE.target-insert ins₂ Fin.zero)

  target₁ :
      toRenameᵗ (CTI2.ηᴿʷ W₂) (Fin.suc Fin.zero)
        ≡ toRenameᵗ κ₂ (Fin.suc (toRenameᵗ κ₁ Fin.zero))
  target₁ =
    trans target-insert-suc-zero
      (trans (cong (toRenameᵗ π₂) (TE.window-zero win₁))
        (TE.window-old win₂ (toRenameᵗ κ₁ Fin.zero)))

  source-zero₁ :
      toRenameᵗ (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W)) Fin.zero
        ≡ toRenameᵗ κ₁ Fin.zero
  source-zero₁ =
    CR.toRenameᵗ-∘ κ₁ (keep (CTI2.ηᴸʷ W)) Fin.zero

  pivot-aligned :
      toRenameᵗ (CTI2.ηᴸʷ Wmid) Fin.zero
        ≡ toRenameᵗ (CTI2.ηᴿʷ Wmid) (Fin.suc Fin.zero)
  pivot-aligned =
    trans
      (cong Fin.suc
        (CR.toRenameᵗ-∘ κ₂
          (skip (κ₁ CR.∘↪ keep (CTI2.ηᴸʷ W))) Fin.zero))
      (trans
        (cong (λ C → Fin.suc (toRenameᵗ κ₂ (Fin.suc C)))
          source-zero₁)
        (cong Fin.suc (sym target₁)))

  target-suc-zero-resolves :
      CTI2.resolveVar (CTI2.targetStoreʷ W₂) (Fin.suc Fin.zero)
        ≡ ★
  target-suc-zero-resolves =
    trans
      (ΛRouteOneWindowFacts.targetOtherResolves facts
        (Fin.suc Fin.zero) (λ ()))
      (cong ⇑ᵗ (ΛRouteOneWindowFacts.firstTargetZeroResolves facts))

  store-rep : CTI2.StoreRepImp Wmid Fin.zero (Fin.suc Fin.zero)
  store-rep =
    CTI2.store-rep-imp
      (subst≡
        (λ R → CTI2.resolveVar (CTI2.sourceStoreʷ Wmid) Fin.zero
          CTI2.⊑ᵂ⟨ Wmid ⟩ R)
        (sym target-suc-zero-resolves)
        (I.X⊑★ (ΛRouteOneWindowFacts.midSourcePivotMark facts)))


record ΛRouteOnePostWindowSupport {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂) : Set₁ where
  field
    midCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → CTI2.LiftCtx I.X⊑X γ γᴮ
      → CTI2.CtxImp (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)

    outCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → CTI2.LiftCtx I.X⊑X γ γᴮ
      → CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W₂)

    midFreshMono :
      CTI2.ImpEnvMono
        (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
        (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))

    midFreshSame : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
        {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → (bodyRel : CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
          ⊢² V ⊑ V′ ∶ body-p)
      → CTI2.SameCtx (midCtx liftγ)
          (proj₁ (Λ-route1-prefix-at facts bodyRel))

    outMidMono :
      CTI2.ImpEnvMono (CTI2.liftWorldLeft I.X⊑★ W₂)
        (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)

    outMidSame : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.SameCtx (outCtx liftγ) (midCtx liftγ)

    outLiftCtxᴸ : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
          (outCtx liftγ)

    innerReveal⊢ : ∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ applyBody (bind ★) B
      → CTI2.targetStoreʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
          CTI2.⊢↑[ just Fin.zero ]
          〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑ applyBody (bind ★) B 〗

    outerReveal⊢ : ∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ B
      → CTI2.targetStoreʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
          CTI2.⊢↑[ just (Fin.suc Fin.zero) ]
          rename↑ Fin.suc (〖 Fin.zero , ★ ↑ B 〗)

    innerBody⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
      → A CTI2.⊑ᵂ⟨ ΛRouteOneMidWorldAt W W₂ κ₁ κ₂ ⟩
          replaceTy Fin.zero (⇑ᵗ (＇ Fin.zero)) (applyBody (bind ★) B)

    finalBody⊑ᵂ : ∀ {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
      → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W₂ ⟩
          substᵗ Λ⊑Λ²TargetSplit₂ B

    outTargetCtx : ∀ {γ : CTI2.CtxImp W}
        {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
      → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
      → CTI2.tgtCtxʷ (outCtx liftγ) ≡
          CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ)

open ΛRouteOnePostWindowSupport public


Λ-route1-out-mid-mono-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
  → CTI2.ImpEnvMono (CTI2.liftWorldLeft I.X⊑★ W₂)
      (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
Λ-route1-out-mid-mono-at Z eq = eq


Λ-route1-mid-fresh-mono-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.ImpEnvMono
      (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
Λ-route1-mid-fresh-mono-at {W₁ = W₁} {W₂ = W₂}
    {κ₂ = κ₂} facts Fin.zero eq = refl
Λ-route1-mid-fresh-mono-at {W₁ = W₁} {W₂ = W₂}
    {κ₂ = κ₂} {ins₂ = ins₂} facts (Fin.suc Z′) eq
    with CR.preimage? κ₂ Z′ in pre
Λ-route1-mid-fresh-mono-at {W₁ = W₁} {W₂ = W₂}
    {κ₂ = κ₂} {ins₂ = ins₂} facts (Fin.suc Z′) eq
    | nothing =
  CR.renameEnv-off κ₂
    (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ W₁))
    pre
Λ-route1-mid-fresh-mono-at {W₁ = W₁} {W₂ = W₂}
    {κ₂ = κ₂} {ins₂ = ins₂} facts (Fin.suc Z′) eq
    | just Fin.zero =
  subst≡
    (λ C → CR.renameEnv κ₂
      (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ W₁)) C
      ≡ I.X⊑★)
    (sym image-eq)
    (CR.renameEnv-image κ₂
      (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ W₁))
      Fin.zero)
  where
  image-eq : Z′ ≡ toRenameᵗ κ₂ Fin.zero
  image-eq = CR.preimage?-sound κ₂ pre
Λ-route1-mid-fresh-mono-at {W₁ = W₁} {W₂ = W₂}
    {π₂ = π₂} {κ₂ = κ₂} {ins₂ = ins₂} facts (Fin.suc Z′) eq
    | just (Fin.suc Z) =
  subst≡
    (λ C → CR.renameEnv κ₂
      (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ W₁)) C
      ≡ I.X⊑★)
    (sym image-eq)
    (trans
      (CR.renameEnv-image κ₂
        (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ W₁))
        (Fin.suc Z))
      old-star)
  where
  image-eq : Z′ ≡ toRenameᵗ κ₂ (Fin.suc Z)
  image-eq = CR.preimage?-sound κ₂ pre

  final-star : CTI2.impEnvʷ W₂ (toRenameᵗ π₂ Z) ≡ I.X⊑★
  final-star =
    subst≡ (λ C → CTI2.impEnvʷ W₂ C ≡ I.X⊑★)
      (sym
        (trans (TE.TargetWindowInsert.window-old
          (ΛRouteOneWindowFacts.targetWindow₂ facts) Z)
          (sym image-eq)))
      eq

  old-star : CTI2.impEnvʷ W₁ Z ≡ I.X⊑★
  old-star = trans (sym (TE.impEnv-insert ins₂ Z)) final-star


Λ-route1-post-window-support-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → CTI2.ImpEnvMono
      (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
      (ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂))
  → (∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ applyBody (bind ★) B
      → CTI2.targetStoreʷ (ΛRouteOneMidWorldAt W W₂ κ₁ κ₂)
          CTI2.⊢↑[ just Fin.zero ]
          〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑ applyBody (bind ★) B 〗)
  → (∀ {B : Ty (suc Δᴿ)}
      → Fin.zero ∈ᵗ B
      → CTI2.targetStoreʷ (CTI2.liftWorldLeft I.X⊑★ W₂)
          CTI2.⊢↑[ just (Fin.suc Fin.zero) ]
          rename↑ Fin.suc (〖 Fin.zero , ★ ↑ B 〗))
  → ΛRouteOnePostWindowSupport {ext₂ = ext₂} facts
Λ-route1-post-window-support-at {W = W} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} {ext₂ = ext₂}
    facts midFreshMono innerReveal outerReveal =
  record
    { midCtx = Λ-route1-mid-ctx-at facts
    ; outCtx = Λ-route1-out-ctx-at facts
    ; midFreshMono = midFreshMono
    ; midFreshSame = λ liftγ bodyRel →
        subst≡
          (λ γᶠ → CTI2.SameCtx
            (Λ-route1-mid-ctx-at facts liftγ) γᶠ)
          (sym (Λ-route1-prefix-at-ctx facts liftγ bodyRel))
          (Λ-route1-mid-fresh-same-at facts liftγ)
    ; outMidMono =
        Λ-route1-out-mid-mono-at {W = W} {W₂ = W₂}
          {κ₁ = κ₁} {κ₂ = κ₂}
    ; outMidSame = Λ-route1-out-mid-same-at facts
    ; outLiftCtxᴸ = Λ-route1-out-liftCtxᴸ-at {ext₂ = ext₂} facts
    ; innerReveal⊢ = innerReveal
    ; outerReveal⊢ = outerReveal
    ; innerBody⊑ᵂ = Λ-route1-inner-body-⊑ᵂ-applyBody facts
    ; finalBody⊑ᵂ = Λ-route1-final-body-⊑ᵂ facts
    ; outTargetCtx = λ liftγ →
        liftCtxᴸ-target
          (Λ-route1-out-liftCtxᴸ-at {ext₂ = ext₂} facts liftγ)
    }


Λ-route1-post-window-at : ∀ {Δᴸ Δᴿ Δ Δ₁ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {π₁ : Δ ↪ᵗ Δ₁}
    {π₂ : Δ₁ ↪ᵗ Δ₂}
    {κ₁ : suc Δ ↪ᵗ Δ₁}
    {κ₂ : suc Δ₁ ↪ᵗ Δ₂}
    {ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁}
    {ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
  → (facts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂)
  → ΛRouteOnePostWindowSupport {ext₂ = ext₂} facts
  → ΛPostWindowGeometry W W₂ ext₂
Λ-route1-post-window-at {W = W} {W₁ = W₁} {W₂ = W₂}
    {κ₁ = κ₁} {κ₂ = κ₂} facts support =
  record
    { freshWorld =
        ΛRouteOneFreshWorldAt W₁ κ₂ (CTI2.targetStoreʷ W₂)
    ; midWorld = ΛRouteOneMidWorldAt W W₂ κ₁ κ₂
    ; route1Prefix = λ liftγ bodyRel →
        Λ-route1-prefix-at facts bodyRel
    ; midCtx = ΛRouteOnePostWindowSupport.midCtx support
    ; outCtx = ΛRouteOnePostWindowSupport.outCtx support
    ; midFreshMono =
        ΛRouteOnePostWindowSupport.midFreshMono support
    ; innerRebaseᴿ = Λ-route1-inner-rebase-at facts
    ; midFreshSame =
        ΛRouteOnePostWindowSupport.midFreshSame support
    ; outMidMono = ΛRouteOnePostWindowSupport.outMidMono support
    ; outerRebaseᴿ = Λ-route1-outer-rebase-at facts
    ; outMidSame =
        ΛRouteOnePostWindowSupport.outMidSame support
    ; outLiftCtxᴸ =
        ΛRouteOnePostWindowSupport.outLiftCtxᴸ support
    ; innerReveal⊢ =
        ΛRouteOnePostWindowSupport.innerReveal⊢ support
    ; outerReveal⊢ =
        ΛRouteOnePostWindowSupport.outerReveal⊢ support
    ; innerBody⊑ᵂ =
        ΛRouteOnePostWindowSupport.innerBody⊑ᵂ support
    ; finalBody⊑ᵂ =
        ΛRouteOnePostWindowSupport.finalBody⊑ᵂ support
    ; outTargetCtx =
        ΛRouteOnePostWindowSupport.outTargetCtx support
    }


Λ-concrete-route1-prefix : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γᶠ ∈ CTI2.CtxImp (TBL.ΛLiftToBindFreshWorld I.X⊑★ W) ]
    Σ[ pᶠ ∈ A CTI2.⊑ᵂ⟨
          TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ applyBody (bind ★) B ]
      TBL.ΛLiftToBindFreshWorld I.X⊑★ W CTI2.∣ γᶠ
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
Λ-concrete-route1-prefix {W = W} {V = V} {V′ = V′}
    {A = A} {B = B} liftγ bodyRel
    with Λ⊑Λ²-route1-prefix bodyRel
... | pᵇ , relFreshRoute =
  γfresh , pᶠ , relFresh
  where
  γfresh = Λ-route1-fresh-ctx liftγ

  relFreshRouteCtx : TBL.ΛLiftToBindFreshWorld I.X⊑★ W
      CTI2.∣ γfresh
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ
  relFreshRouteCtx =
    subst≡
      (λ γᶠ → TBL.ΛLiftToBindFreshWorld I.X⊑★ W
        CTI2.∣ γᶠ
        ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᵇ)
      (Λ-route1-ctx-fresh-eq liftγ)
      relFreshRoute

  pᶠ : A CTI2.⊑ᵂ⟨ TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩
      applyBody (bind ★) B
  pᶠ =
    subst≡
      (λ C → A CTI2.⊑ᵂ⟨
        TBL.ΛLiftToBindFreshWorld I.X⊑★ W ⟩ C)
      (sym (applyBody-bind★-eq B))
      pᵇ

  relFresh : TBL.ΛLiftToBindFreshWorld I.X⊑★ W
      CTI2.∣ γfresh
      ⊢² V ⊑ CT.renameᵗᵐ (keep wk↪ᵗ) V′ ∶ pᶠ
  relFresh =
    rel-target-transportᴿ (sym (applyBody-bind★-eq B))
      pᵇ relFreshRouteCtx


Λ-concrete-route1-prefix-ctx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → (bodyRel : CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p)
  → proj₁ (Λ-concrete-route1-prefix liftγ bodyRel)
      ≡ Λ-route1-fresh-ctx liftγ
Λ-concrete-route1-prefix-ctx liftγ bodyRel
    with Λ⊑Λ²-route1-prefix bodyRel
... | pᵇ , relFreshRoute = refl


Λ-concrete-post-window : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))}
  → ΛPostWindowGeometry W
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      ext₂
Λ-concrete-post-window {W = W} {ext₂ = ext₂} = record
  { freshWorld = TBL.ΛLiftToBindFreshWorld I.X⊑★ W
  ; midWorld = ΛPostMidWorld W
  ; route1Prefix = Λ-concrete-route1-prefix
  ; midCtx = Λ-route1-mid-ctx
  ; outCtx = Λ-route1-out-ctx
  ; midFreshMono = Λ-mid-fresh-mono W
  ; innerRebaseᴿ = Λ-inner-rebaseᴿ W
  ; midFreshSame = λ liftγ bodyRel →
      subst≡ (λ γ → CTI2.SameCtx (Λ-route1-mid-ctx liftγ) γ)
        (sym (Λ-concrete-route1-prefix-ctx liftγ bodyRel))
        (Λ-route1-mid-fresh-same liftγ)
  ; outMidMono = Λ-out-mid-mono W
  ; outerRebaseᴿ = Λ-outer-rebaseᴿ W
  ; outMidSame = Λ-route1-out-mid-same
  ; outLiftCtxᴸ = Λ-route1-out-liftCtxᴸ ext₂
  ; innerReveal⊢ = λ Bpre-zero∈ →
      generated-reveal-⊢↑-present Bpre-zero∈ (Z∋ refl)
  ; outerReveal⊢ = λ zero∈B →
      TE.reveal-renameˣ StoreRename-suc-bind
        (generated-reveal-⊢↑-present zero∈B (Z∋ refl))
  ; innerBody⊑ᵂ = λ {A} {B} body-p →
      Λ-inner-body-⊑ᵂ-applyBody {W = W} {A = A} {B = B} body-p
  ; finalBody⊑ᵂ = λ {A} {B} body-p →
      Λ-final-body-⊑ᵂ {W = W} {A = A} {B = B} body-p
  ; outTargetCtx = λ liftγ →
      liftCtxᴸ-target (Λ-route1-out-liftCtxᴸ ext₂ liftγ)
  }


Λ-route1-right-bind-facts : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ΛRouteOneWindowFacts id↪ᵗ id↪ᵗ
      (TE.rightBindTargetInsert {W = W} {B = ★})
      (TE.rightBindTargetInsert
        {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
Λ-route1-right-bind-facts {W = W} = record
  { targetWindow₁ = TE.rightBindTargetWindowInsert
  ; targetWindow₂ = TE.rightBindTargetWindowInsert
  ; pivotMark = refl
  ; targetStoreTransport = StoreTransport-lift-bind
  ; firstTargetZeroResolves = refl
  ; targetZeroResolves = refl
  ; targetOtherResolves = target-other
  ; midSourcePivotMark = refl
  }
  where
  target-other : ∀ Z
    → Z ≢ Fin.zero
    → CTI2.resolveVar
        (CTI2.targetStoreʷ
          (CTI2.rightOnlyWorld
            (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))) Z
      ≡ CTI2.resolveVar
          (store-lift
            (CTI2.targetStoreʷ (CTI2.rightOnlyWorld W ★))) Z
  target-other Fin.zero neq = ⊥-elim (neq refl)
  target-other (Fin.suc Z) neq = refl


record ΛTwoInsertPostPlan {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ) : Set₁ where
  field
    Δ₁ : TyCtx
    Δ₂ : TyCtx
    W₁ : CTI2.World Δᴸ (suc Δᴿ) Δ₁
    W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂
    π₁ : Δ ↪ᵗ Δ₁
    π₂ : Δ₁ ↪ᵗ Δ₂
    κ₁ : suc Δ ↪ᵗ Δ₁
    κ₂ : suc Δ₁ ↪ᵗ Δ₂
    ins₁ : TE.TargetInsert wk↪ᵗ π₁ W W₁
    ins₂ : TE.TargetInsert wk↪ᵗ π₂ W₁ W₂
    targetFollows₁ : CTI2.targetStoreʷ W₁
      ≡ applyStores (bind ★ ∷ []) (CTI2.targetStoreʷ W)
    targetFollows₂ : CTI2.targetStoreʷ W₂
      ≡ applyStores (bind (＇ Fin.zero) ∷ []) (CTI2.targetStoreʷ W₁)
    windowFacts : ΛRouteOneWindowFacts κ₁ κ₂ ins₁ ins₂
    postExtend : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂
    postGeometry : ΛPostWindowGeometry W W₂ postExtend

open ΛTwoInsertPostPlan public


record ΛSmartChildPostPlan {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    (plan : ΛTwoInsertPostPlan W) : Set₁ where
  field
    childPlan : ΛTwoInsertPostPlan Wᵐ
    postLift : CTI2.SmartCommaLiftᴸ
      (ΛTwoInsertPostPlan.W₂ plan)
      (ΛTwoInsertPostPlan.W₂ childPlan)
    postLiftCtx : ∀ {γ γᵐ}
      → CTI2.SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
      → CTI2.SmartLiftCtxᴸ
          (ECR.mapCtxᴿ (ΛTwoInsertPostPlan.postExtend plan) γ)
          (ECR.mapCtxᴿ
            (ΛTwoInsertPostPlan.postExtend childPlan) γᵐ)


Λ-concrete-two-insert-post-plan : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ΛTwoInsertPostPlan W
Λ-concrete-two-insert-post-plan {W = W} = record
  { Δ₁ = _
  ; Δ₂ = _
  ; W₁ = CTI2.rightOnlyWorld W ★
  ; W₂ = CTI2.rightOnlyWorld
      (CTI2.rightOnlyWorld W ★) (＇ Fin.zero)
  ; π₁ = wk↪ᵗ
  ; π₂ = wk↪ᵗ
  ; κ₁ = id↪ᵗ
  ; κ₂ = id↪ᵗ
  ; ins₁ = TE.rightBindTargetInsert
  ; ins₂ = TE.rightBindTargetInsert
  ; targetFollows₁ = refl
  ; targetFollows₂ = refl
  ; windowFacts = Λ-route1-right-bind-facts
  ; postExtend = right-bind-right-bind-world-extendᴿ
  ; postGeometry = Λ-concrete-post-window
  }


Λ⊑Λ²-post-body-transport-at : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W}
    {γᴮ : CTI2.CtxImp (CTI2.liftWorldBoth I.X⊑X W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B}
  → {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
  → ΛPostWindowGeometry W W₂ ext₂
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CTI2.LiftCtx I.X⊑X γ γᴮ
  → CT.Value V
  → CT.Value V′
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γ₂ᴸ ∈ CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W₂) ]
    Σ[ body-p₂ ∈ A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
    Σ[ top-p₂ ∈ `∀ A CTI2.⊑ᵂ⟨ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
      CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ) γ₂ᴸ
      × Value (Λ⊑Λ²PostTerm V′ B)
      × ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ ,
          CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
          ⊢ Λ⊑Λ²PostTerm V′ B ⦂
          substᵗ Λ⊑Λ²TargetSplit₂ B
      × CTI2.liftWorldLeft I.X⊑★ W₂ CTI2.∣ γ₂ᴸ
          ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂
Λ⊑Λ²-post-body-transport-at {Δᴿ = Δᴿ} {W = W} {W₂ = W₂}
    {γ = γ} {γᴮ = γᴮ}
    {V = V} {V′ = V′} {A = A} {B = B} {body-p = body-p}
    {ext₂ = ext₂} geom Anv zero∈A liftγ vV vV′ bodyRel
  =
  γout , body-p₂ , top-p₂ , liftOut , postVal , post⊢ , relOut
  where
  route = ΛPostWindowGeometry.route1Prefix geom liftγ bodyRel

  γfresh = proj₁ route

  pFresh = proj₁ (proj₂ route)

  relFresh = proj₂ (proj₂ route)

  Wfresh =
    ΛPostWindowGeometry.freshWorld geom

  Wmid =
    ΛPostWindowGeometry.midWorld geom

  Wout =
    CTI2.liftWorldLeft I.X⊑★ W₂

  γmid = ΛPostWindowGeometry.midCtx geom liftγ
  γout = ΛPostWindowGeometry.outCtx geom liftγ

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
    ΛPostWindowGeometry.innerReveal⊢ geom Bpre-zero∈

  cOuter⊢ :
      CTI2.targetStoreʷ Wout
        CTI2.⊢↑[ just (Fin.suc Fin.zero) ] cOuter
  cOuter⊢ =
    ΛPostWindowGeometry.outerReveal⊢ geom zero∈B

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
  qInner = ΛPostWindowGeometry.innerBody⊑ᵂ geom body-p

  relMid : Wmid CTI2.∣ γmid ⊢² V ⊑ post₁ ∶ qInner
  relMid =
    CTI2.⊑reveal²
      (ΛPostWindowGeometry.midFreshMono geom)
      (ΛPostWindowGeometry.innerRebaseᴿ geom)
      (ΛPostWindowGeometry.midFreshSame geom liftγ bodyRel)
      cInner⊢ relFresh qInner

  relMidOuterPrem : Wmid CTI2.∣ γmid
      ⊢² V ⊑ post₁ ∶
        subst≡ (λ C → A CTI2.⊑ᵂ⟨ Wmid ⟩ C)
          (inner-reveal-target-eq-applyBody B) qInner
  relMidOuterPrem =
    rel-target-transportᴿ (inner-reveal-target-eq-applyBody B) qInner relMid

  body-p₂ : A CTI2.⊑ᵂ⟨ Wout ⟩ B₂
  body-p₂ = ΛPostWindowGeometry.finalBody⊑ᵂ geom body-p

  qOuter : A CTI2.⊑ᵂ⟨ Wout ⟩ BouterOut
  qOuter =
    subst≡ (λ C → A CTI2.⊑ᵂ⟨ Wout ⟩ C)
      (sym (outer-reveal-target-eq B))
      body-p₂

  relOutConv : Wout CTI2.∣ γout ⊢² V ⊑ post ∶ qOuter
  relOutConv =
    CTI2.⊑reveal²
      (ΛPostWindowGeometry.outMidMono geom)
      (ΛPostWindowGeometry.outerRebaseᴿ geom)
      (ΛPostWindowGeometry.outMidSame geom liftγ)
      cOuter⊢ relMidOuterPrem qOuter

  relOut : Wout CTI2.∣ γout ⊢² V ⊑ post ∶ body-p₂
  relOut =
    TBL.⊢²-retarget {q = body-p₂}
      (rel-target-transportᴿ
        {W = Wout} {γ = γout} {M = V} {N = post}
        {A = A} {B = BouterOut} {B′ = B₂}
        (outer-reveal-target-eq B)
        qOuter relOutConv)

  top-p₂ : `∀ A CTI2.⊑ᵂ⟨ W₂ ⟩ B₂
  top-p₂ =
    ∀⊑ᵂ-from-left-lift
      {W = W₂} {A = A} {B = B₂} Anv zero∈A body-p₂

  liftOut : CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ) γout
  liftOut = ΛPostWindowGeometry.outLiftCtxᴸ geom liftγ

  post⊢ :
      ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
      ⊢ post ⦂ B₂
  post⊢ =
    subst≡
      (λ Γ → ⟨ _ , CTI2.targetStoreʷ W₂ , Γ ⟩
        ⊢ post ⦂ B₂)
      (ΛPostWindowGeometry.outTargetCtx geom liftγ)
      (CTI2T.target-typing² relOut)


Λ⊑Λ²-post-body-transport : Λ⊑Λ²PostBodyTransportᵀ
Λ⊑Λ²-post-body-transport {W = W} {body-p = body-p} ext₂ =
  Λ⊑Λ²-post-body-transport-at
    (Λ-concrete-post-window {W = W} {ext₂ = ext₂})


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


Λ-route1-smart-alias-facts : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ΛRouteOneWindowFacts id↪ᵗ id↪ᵗ
      (TE.smartAliasTargetInsert
        (TE.rightBindTargetInsert {W = W} {B = ★}) guard)
      (TE.smartAliasTargetInsert
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartAliasGuardInsert
          (TE.rightBindTargetInsert {W = W} {B = ★}) guard))
Λ-route1-smart-alias-facts {W = W} {Wᵐ = Wᵐ} guard =
  record
    { targetWindow₁ =
        TE.smartAliasTargetWindowInsert
          (TE.rightBindTargetInsert {W = W} {B = ★})
          guard TE.rightBindTargetWindowInsert
    ; targetWindow₂ =
        TE.smartAliasTargetWindowInsert
          (TE.rightBindTargetInsert
            {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
          guard₁ TE.rightBindTargetWindowInsert
    ; pivotMark = refl
    ; targetStoreTransport = StoreTransport-lift-bind
    ; firstTargetZeroResolves = refl
    ; targetZeroResolves = refl
    ; targetOtherResolves = target-other
    ; midSourcePivotMark = refl
    }
  where
  guard₁ =
    TE.smartAliasGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard

  target-other : ∀ Z
    → Z ≢ Fin.zero
    → CTI2.resolveVar
        (CTI2.targetStoreʷ
          (TE.smartAliasInsertWorld
            (TE.rightBindTargetInsert
              {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
            (TE.smartAliasInsertWorld
              (TE.rightBindTargetInsert {W = W} {B = ★}) Wᵐ)))
        Z
      ≡ CTI2.resolveVar
          (store-lift
            (CTI2.targetStoreʷ
              (TE.smartAliasInsertWorld
                (TE.rightBindTargetInsert {W = W} {B = ★}) Wᵐ)))
          Z
  target-other Fin.zero neq = ⊥-elim (neq refl)
  target-other (Fin.suc Z) neq = refl


Λ-route1-smart-alias-ext₂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ []) Wᵐ
      (TE.smartAliasInsertWorld
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartAliasInsertWorld
          (TE.rightBindTargetInsert {W = W} {B = ★}) Wᵐ))
Λ-route1-smart-alias-ext₂ {W = W} guard =
  composeWorldExtendᴿ
    (smart-alias-bind-world-extendᴿ {W = W} {B = ★} guard)
    (smart-alias-bind-world-extendᴿ
      {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero} guard₁)
  where
  guard₁ =
    TE.smartAliasGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard


Λ-route1-smart-alias-post-window : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ΛPostWindowGeometry Wᵐ
      (TE.smartAliasInsertWorld
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartAliasInsertWorld
          (TE.rightBindTargetInsert {W = W} {B = ★}) Wᵐ))
      (Λ-route1-smart-alias-ext₂ guard)
Λ-route1-smart-alias-post-window guard =
  Λ-route1-post-window-at facts
    (Λ-route1-post-window-support-at facts
      (Λ-route1-mid-fresh-mono-at facts)
      (λ Bpre-zero∈ →
        generated-reveal-⊢↑-present Bpre-zero∈ (Z∋ refl))
      (λ zero∈B →
        TE.reveal-renameˣ StoreRename-suc-bind
          (generated-reveal-⊢↑-present zero∈B (Z∋ refl))))
  where
  facts = Λ-route1-smart-alias-facts guard


Λ-route1-smart-fresh-facts : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ΛRouteOneWindowFacts
      (TE.rightPushoutWindow
        (CTI2.SmartFreshBehindGuard.oldCenters guard))
      (TE.rightPushoutWindow
        (CTI2.SmartFreshBehindGuard.oldCenters
          (TE.smartFreshGuardInsert
            (TE.rightBindTargetInsert {W = W} {B = ★}) guard)))
      (TE.smartFreshTargetInsert
        (TE.rightBindTargetInsert {W = W} {B = ★}) guard)
      (TE.smartFreshTargetInsert
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartFreshGuardInsert
          (TE.rightBindTargetInsert {W = W} {B = ★}) guard))
Λ-route1-smart-fresh-facts {W = W} {Wᵐ = Wᵐ} guard =
  record
    { targetWindow₁ =
        TE.smartFreshRightBindTargetWindowInsert guard
    ; targetWindow₂ =
        TE.smartFreshRightBindTargetWindowInsert guard₁
    ; pivotMark = refl
    ; targetStoreTransport = StoreTransport-lift-bind
    ; firstTargetZeroResolves = refl
    ; targetZeroResolves = refl
    ; targetOtherResolves = target-other
    ; midSourcePivotMark = refl
    }
  where
  guard₁ =
    TE.smartFreshGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard

  target-other : ∀ Z
    → Z ≢ Fin.zero
    → CTI2.resolveVar
        (CTI2.targetStoreʷ
          (TE.smartFreshInsertWorld
            (TE.rightBindTargetInsert
              {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
            guard₁))
        Z
      ≡ CTI2.resolveVar
          (store-lift
            (CTI2.targetStoreʷ
              (TE.smartFreshInsertWorld
                (TE.rightBindTargetInsert {W = W} {B = ★}) guard)))
          Z
  target-other Fin.zero neq = ⊥-elim (neq refl)
  target-other (Fin.suc Z) neq = refl


Λ-route1-smart-fresh-ext₂ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ []) Wᵐ
      (TE.smartFreshInsertWorld
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartFreshGuardInsert
          (TE.rightBindTargetInsert {W = W} {B = ★}) guard))
Λ-route1-smart-fresh-ext₂ {W = W} guard =
  composeWorldExtendᴿ
    (smart-fresh-bind-world-extendᴿ {W = W} {B = ★} guard)
    (smart-fresh-bind-world-extendᴿ
      {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero} guard₁)
  where
  guard₁ =
    TE.smartFreshGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard


Λ-route1-smart-fresh-post-window : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ΛPostWindowGeometry Wᵐ
      (TE.smartFreshInsertWorld
        (TE.rightBindTargetInsert
          {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
        (TE.smartFreshGuardInsert
          (TE.rightBindTargetInsert {W = W} {B = ★}) guard))
      (Λ-route1-smart-fresh-ext₂ guard)
Λ-route1-smart-fresh-post-window guard =
  Λ-route1-post-window-at facts
    (Λ-route1-post-window-support-at facts
      (Λ-route1-mid-fresh-mono-at facts)
      (λ Bpre-zero∈ →
        generated-reveal-⊢↑-present Bpre-zero∈ (Z∋ refl))
      (λ zero∈B →
        TE.reveal-renameˣ StoreRename-suc-bind
          (generated-reveal-⊢↑-present zero∈B (Z∋ refl))))
  where
  facts = Λ-route1-smart-fresh-facts guard


Λ-two-insert-smart-child : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (plan : ΛTwoInsertPostPlan W)
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → ΛSmartChildPostPlan plan
Λ-two-insert-smart-child {Wᵐ = Wᵐ} plan
    (CTI2.smart-merge-alias guard) =
  record
    { childPlan = record
        { Δ₁ = _ ; Δ₂ = _ ; W₁ = Wᵐ₁ ; W₂ = Wᵐ₂
        ; π₁ = π₁ plan ; π₂ = π₂ plan
        ; κ₁ = κ₁ plan ; κ₂ = κ₂ plan
        ; ins₁ = insᵐ₁ ; ins₂ = insᵐ₂
        ; targetFollows₁ = follows₁ ; targetFollows₂ = follows₂
        ; windowFacts = facts ; postExtend = extᵐ
        ; postGeometry = Λ-route1-post-window-at facts support }
    ; postLift = CTI2.smart-merge-alias guard₂
    ; postLiftCtx = mapCtxᴿ-smart-liftᴸ
    }
  where
  Wᵐ₁ = TE.smartAliasInsertWorld (ins₁ plan) Wᵐ
  insᵐ₁ = TE.smartAliasTargetInsert (ins₁ plan) guard
  guard₁ = TE.smartAliasGuardInsert (ins₁ plan) guard
  Wᵐ₂ = TE.smartAliasInsertWorld (ins₂ plan) Wᵐ₁
  insᵐ₂ = TE.smartAliasTargetInsert (ins₂ plan) guard₁
  guard₂ = TE.smartAliasGuardInsert (ins₂ plan) guard₁
  follows₁ = trans (targetFollows₁ plan)
    (cong (applyStores (bind ★ ∷ []))
      (sym (CTI2.SmartAliasMergeGuard.targetStore-same guard)))
  follows₂ = trans (targetFollows₂ plan)
    (cong (applyStores (bind (＇ Fin.zero) ∷ []))
      (sym (CTI2.SmartAliasMergeGuard.targetStore-same guard₁)))
  extᵐ = composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ insᵐ₁ follows₁)
    (target-insert-bind-world-extendᴿ insᵐ₂ follows₂)
  winᵐ₁ = TE.smartAliasTargetWindowInsert
    (ins₁ plan) guard (targetWindow₁ (windowFacts plan))
  winᵐ₂ = TE.smartAliasTargetWindowInsert
    (ins₂ plan) guard₁ (targetWindow₂ (windowFacts plan))
  facts = record
    { targetWindow₁ = winᵐ₁
    ; targetWindow₂ = winᵐ₂
    ; pivotMark = subst≡ (λ C → CTI2.impEnvʷ
          (CR.renameWorld (skip (κ₂ plan))
            (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) C ≡ I.X⊑★)
        (sym (CR.toRenameᵗ-∘ (skip (κ₂ plan))
          (CTI2.ηᴿʷ (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) Fin.zero))
        (CR.renameEnv-image (skip (κ₂ plan))
          (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) Fin.zero)
    ; targetStoreTransport = targetStoreTransport (windowFacts plan)
    ; firstTargetZeroResolves = firstTargetZeroResolves (windowFacts plan)
    ; targetZeroResolves = targetZeroResolves (windowFacts plan)
    ; targetOtherResolves = targetOtherResolves (windowFacts plan)
    ; midSourcePivotMark =
        route1-mid-source-pivot-from-windows winᵐ₁ winᵐ₂ }
  first-entry = subst≡
    (λ Σ → Σ ∋ Fin.zero ⦂ ⇑ᵗ ★) (sym follows₁) (Z∋ refl)
  support = Λ-route1-post-window-support-at facts
    (Λ-route1-mid-fresh-mono-at facts)
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just Fin.zero ] _)
      (sym follows₂) (generated-reveal-⊢↑-present z (Z∋ refl)))
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just (Fin.suc Fin.zero) ] _)
      (sym follows₂) (TE.reveal-renameˣ StoreRename-suc-bind
        (generated-reveal-⊢↑-present z first-entry)))
Λ-two-insert-smart-child {Wᵐ = Wᵐ} plan
    (CTI2.smart-fresh-behind guard)
    with TE.smartFreshTargetWindowInsert (ins₁ plan) guard
      (targetWindow₁ (windowFacts plan))
Λ-two-insert-smart-child {Wᵐ = Wᵐ} plan
    (CTI2.smart-fresh-behind guard) | κᵐ₁ , winᵐ₁
    with TE.smartFreshTargetWindowInsert (ins₂ plan) guard₁
      (targetWindow₂ (windowFacts plan))
  where
  guard₁ = TE.smartFreshGuardInsert (ins₁ plan) guard
Λ-two-insert-smart-child {Wᵐ = Wᵐ} plan
    (CTI2.smart-fresh-behind guard)
    | κᵐ₁ , winᵐ₁ | κᵐ₂ , winᵐ₂ =
  record
    { childPlan = record
        { Δ₁ = _ ; Δ₂ = _ ; W₁ = Wᵐ₁ ; W₂ = Wᵐ₂
        ; π₁ = πᵐ₁ ; π₂ = πᵐ₂
        ; κ₁ = κᵐ₁ ; κ₂ = κᵐ₂
        ; ins₁ = insᵐ₁ ; ins₂ = insᵐ₂
        ; targetFollows₁ = follows₁ ; targetFollows₂ = follows₂
        ; windowFacts = facts ; postExtend = extᵐ
        ; postGeometry = Λ-route1-post-window-at facts support }
    ; postLift = CTI2.smart-fresh-behind guard₂
    ; postLiftCtx = mapCtxᴿ-smart-liftᴸ
    }
  where
  πᵐ₁ = CR.EmbeddingPushout.premise (CR.embeddingPushout
    (π₁ plan) (CTI2.SmartFreshBehindGuard.oldCenters guard))
  Wᵐ₁ = TE.smartFreshInsertWorld (ins₁ plan) guard
  insᵐ₁ = TE.smartFreshTargetInsert (ins₁ plan) guard
  guard₁ = TE.smartFreshGuardInsert (ins₁ plan) guard
  πᵐ₂ = CR.EmbeddingPushout.premise (CR.embeddingPushout
    (π₂ plan) (CTI2.SmartFreshBehindGuard.oldCenters guard₁))
  Wᵐ₂ = TE.smartFreshInsertWorld (ins₂ plan) guard₁
  insᵐ₂ = TE.smartFreshTargetInsert (ins₂ plan) guard₁
  guard₂ = TE.smartFreshGuardInsert (ins₂ plan) guard₁
  follows₁ = trans (targetFollows₁ plan)
    (cong (applyStores (bind ★ ∷ []))
      (sym (CTI2.SmartFreshBehindGuard.targetStore-same guard)))
  follows₂ = trans (targetFollows₂ plan)
    (cong (applyStores (bind (＇ Fin.zero) ∷ []))
      (sym (CTI2.SmartFreshBehindGuard.targetStore-same guard₁)))
  extᵐ = composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ insᵐ₁ follows₁)
    (target-insert-bind-world-extendᴿ insᵐ₂ follows₂)
  facts = record
    { targetWindow₁ = winᵐ₁ ; targetWindow₂ = winᵐ₂
    ; pivotMark = subst≡ (λ C → CTI2.impEnvʷ
          (CR.renameWorld (skip κᵐ₂)
            (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) C ≡ I.X⊑★)
        (sym (CR.toRenameᵗ-∘ (skip κᵐ₂)
          (CTI2.ηᴿʷ (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) Fin.zero))
        (CR.renameEnv-image (skip κᵐ₂)
          (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ Wᵐ₁)) Fin.zero)
    ; targetStoreTransport = targetStoreTransport (windowFacts plan)
    ; firstTargetZeroResolves = firstTargetZeroResolves (windowFacts plan)
    ; targetZeroResolves = targetZeroResolves (windowFacts plan)
    ; targetOtherResolves = targetOtherResolves (windowFacts plan)
    ; midSourcePivotMark =
        route1-mid-source-pivot-from-windows winᵐ₁ winᵐ₂ }
  first-entry = subst≡
    (λ Σ → Σ ∋ Fin.zero ⦂ ⇑ᵗ ★) (sym follows₁) (Z∋ refl)
  support = Λ-route1-post-window-support-at facts
    (Λ-route1-mid-fresh-mono-at facts)
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just Fin.zero ] _)
      (sym follows₂) (generated-reveal-⊢↑-present z (Z∋ refl)))
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just (Fin.suc Fin.zero) ] _)
      (sym follows₂) (TE.reveal-renameˣ StoreRename-suc-bind
        (generated-reveal-⊢↑-present z first-entry)))


Λ-front-old-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Z
  → CTI2.impEnvʷ W Z ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (toRenameᵗ (skip id↪ᵗ) Z) ≡ I.X⊑★
Λ-front-old-mark-mono W Z eq =
  subst≡
    (λ Y → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (Fin.suc Y) ≡ I.X⊑★)
    (sym (toRename-id-eq Z)) eq


Λ-front-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → toRenameᵗ
      (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W)) Xᴿ
    ≡ toRenameᵗ (skip id↪ᵗ)
        (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)
Λ-front-target-frozen W Xᴿ =
  cong Fin.suc
    (sym (toRename-id-eq (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ)))


Λ-front-old-source-frozen : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴸ
  → toRenameᵗ
      (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W)) (Fin.suc Xᴸ)
    ≡ toRenameᵗ (skip id↪ᵗ)
        (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
Λ-front-old-source-frozen W Xᴸ =
  cong Fin.suc
    (sym (toRename-id-eq (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)))


Λ-front-target-mark-mono : ∀ {Δᴸ Δᴿ Δ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
  → ∀ Xᴿ
  → CTI2.impEnvʷ W (toRenameᵗ (CTI2.ηᴿʷ W) Xᴿ) ≡ I.X⊑★
  → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
      (toRenameᵗ
        (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W)) Xᴿ) ≡ I.X⊑★
Λ-front-target-mark-mono W Xᴿ eq = eq


Λ-front-smart-guard : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.SmartFreshBehindGuard W
      (CTI2.liftWorldLeft I.X⊑★ W)
Λ-front-smart-guard {W = W} =
  CTI2.smart-fresh-behind-guard (skip id↪ᵗ) refl refl
    (λ p → p) (Λ-front-old-mark-mono W) (Λ-front-target-frozen W)
    (Λ-front-old-source-frozen W) (λ _ ()) refl
    (Λ-front-target-mark-mono W)


record ExactSmartFreshGuard {Δᴸ Δᴿ Δ Δᵐ}
    (W : CTI2.World Δᴸ Δᴿ Δ)
    (Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ) : Set where
  field
    guard : CTI2.SmartFreshBehindGuard W Wᵐ
    old-mark-exact : ∀ Z
      → CTI2.impEnvʷ Wᵐ
          (toRenameᵗ
            (CTI2.SmartFreshBehindGuard.oldCenters guard) Z)
        ≡ CTI2.impEnvʷ W Z
    fresh-off-old :
      CR.preimage? (CTI2.SmartFreshBehindGuard.oldCenters guard)
        (toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero) ≡ nothing

open ExactSmartFreshGuard public


Λ-front-exact-smart-guard : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → ExactSmartFreshGuard W (CTI2.liftWorldLeft I.X⊑★ W)
Λ-front-exact-smart-guard {W = W} = record
  { guard = Λ-front-smart-guard
  ; old-mark-exact = exact
  ; fresh-off-old = refl
  }
  where
  exact : ∀ Z
    → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
        (toRenameᵗ (skip id↪ᵗ) Z)
      ≡ CTI2.impEnvʷ W Z
  exact Z =
    subst≡
      (λ Y → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
        (Fin.suc Y) ≡ CTI2.impEnvʷ W Z)
      (sym (toRename-id-eq Z)) refl


exactSmartFreshSubst : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → ExactSmartFreshGuard W Wᵐ
  → Fin.Fin Δᵐ
  → Ty (suc Δ)
exactSmartFreshSubst exact Zᵐ
    with CR.preimage?
      (CTI2.SmartFreshBehindGuard.oldCenters (guard exact)) Zᵐ
exactSmartFreshSubst exact Zᵐ | just Z = ＇ (Fin.suc Z)
exactSmartFreshSubst exact Zᵐ | nothing = ＇ Fin.zero


exactSmartFreshSubst-image : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ Z
  → exactSmartFreshSubst exact
      (toRenameᵗ
        (CTI2.SmartFreshBehindGuard.oldCenters (guard exact)) Z)
    ≡ ＇ (Fin.suc Z)
exactSmartFreshSubst-image exact Z
  rewrite CR.preimage?-image
    (CTI2.SmartFreshBehindGuard.oldCenters (guard exact)) Z = refl


exactSmartFreshSubst-fresh : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → exactSmartFreshSubst exact
      (toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero)
    ≡ ＇ Fin.zero
exactSmartFreshSubst-fresh exact
  rewrite fresh-off-old exact = refl


exactSmartFreshSubst-source : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ X
  → exactSmartFreshSubst exact (toRenameᵗ (CTI2.ηᴸʷ Wᵐ) X)
    ≡ ＇ (toRenameᵗ
        (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W)) X)
exactSmartFreshSubst-source exact Fin.zero =
  exactSmartFreshSubst-fresh exact
exactSmartFreshSubst-source {W = W} exact (Fin.suc X) =
  trans
    (cong (exactSmartFreshSubst exact)
      (CTI2.SmartFreshBehindGuard.old-source-frozen
        (guard exact) X))
    (exactSmartFreshSubst-image exact
      (toRenameᵗ (CTI2.ηᴸʷ W) X))


exactSmartFreshSubst-target : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ Y
  → exactSmartFreshSubst exact (toRenameᵗ (CTI2.ηᴿʷ Wᵐ) Y)
    ≡ ＇ (toRenameᵗ
        (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W)) Y)
exactSmartFreshSubst-target {W = W} exact Y =
  trans
    (cong (exactSmartFreshSubst exact)
      (CTI2.SmartFreshBehindGuard.target-frozen (guard exact) Y))
    (exactSmartFreshSubst-image exact
      (toRenameᵗ (CTI2.ηᴿʷ W) Y))


exactSmartFreshSubst-star : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ Zᵐ
  → CTI2.impEnvʷ Wᵐ Zᵐ ≡ I.X⊑★
  → I._⊢_⊑_ (CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W))
      (exactSmartFreshSubst exact Zᵐ) ★
exactSmartFreshSubst-star {W = W} {Wᵐ = Wᵐ} exact Zᵐ star
    with CR.preimage?
      (CTI2.SmartFreshBehindGuard.oldCenters (guard exact)) Zᵐ in pre
exactSmartFreshSubst-star {W = W} {Wᵐ = Wᵐ} exact Zᵐ star
    | nothing = I.X⊑★ refl
exactSmartFreshSubst-star {W = W} {Wᵐ = Wᵐ} exact Zᵐ star
    | just Z =
  I.X⊑★ parent-star
  where
  old = CTI2.SmartFreshBehindGuard.oldCenters (guard exact)

  image-eq : Zᵐ ≡ toRenameᵗ old Z
  image-eq = CR.preimage?-sound old pre

  child-star : CTI2.impEnvʷ Wᵐ (toRenameᵗ old Z) ≡ I.X⊑★
  child-star =
    subst≡ (λ C → CTI2.impEnvʷ Wᵐ C ≡ I.X⊑★) image-eq star

  parent-star : CTI2.impEnvʷ W Z ≡ I.X⊑★
  parent-star = trans (sym (old-mark-exact exact Z)) child-star


exactSmartFreshSubst-source-eq : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ A
  → substᵗ (exactSmartFreshSubst exact) (CTI2.embedᴸ Wᵐ A)
    ≡ CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W) A
exactSmartFreshSubst-source-eq {W = W} {Wᵐ = Wᵐ} exact A =
  trans
    (substᵗ-rename (exactSmartFreshSubst exact)
      (toRenameᵗ (CTI2.ηᴸʷ Wᵐ)) A)
    (trans (substᵗ-cong A (exactSmartFreshSubst-source exact))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴸʷ (CTI2.liftWorldLeft I.X⊑★ W))) A))


exactSmartFreshSubst-target-eq : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ∀ B
  → substᵗ (exactSmartFreshSubst exact) (CTI2.embedᴿ Wᵐ B)
    ≡ CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ W) B
exactSmartFreshSubst-target-eq {W = W} {Wᵐ = Wᵐ} exact B =
  trans
    (substᵗ-rename (exactSmartFreshSubst exact)
      (toRenameᵗ (CTI2.ηᴿʷ Wᵐ)) B)
    (trans (substᵗ-cong B (exactSmartFreshSubst-target exact))
      (rename-as-subst
        (toRenameᵗ (CTI2.ηᴿʷ (CTI2.liftWorldLeft I.X⊑★ W))) B))


exactSmartFresh-untransport : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → A CTI2.⊑ᵂ⟨ Wᵐ ⟩ B
  → A CTI2.⊑ᵂ⟨ CTI2.liftWorldLeft I.X⊑★ W ⟩ B
exactSmartFresh-untransport {W = W} {Wᵐ = Wᵐ} {A = A} {B = B}
    exact p =
  subst≡
    (λ L → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W) ⊢ L
      ⊑ CTI2.embedᴿ (CTI2.liftWorldLeft I.X⊑★ W) B)
    (exactSmartFreshSubst-source-eq exact A)
    (subst≡
      (λ R → CTI2.impEnvʷ (CTI2.liftWorldLeft I.X⊑★ W)
        ⊢ substᵗ (exactSmartFreshSubst exact) (CTI2.embedᴸ Wᵐ A)
        ⊑ R)
      (exactSmartFreshSubst-target-eq exact B)
      (subst-⊑ (exactSmartFreshSubst-star exact) p))


exactSmartFreshGuardInsert : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′ Δᵐ}
    {ρ : Δᴿ ↪ᵗ Δᴿ′} {π : Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (ins : TE.TargetInsert ρ π W W′)
  → (exact : ExactSmartFreshGuard W Wᵐ)
  → ExactSmartFreshGuard W′
      (TE.smartFreshInsertWorld ins (guard exact))
exactSmartFreshGuardInsert {π = π} {W = W} {W′ = W′}
    {Wᵐ = Wᵐ} ins exact = record
  { guard = TE.smartFreshGuardInsert ins guard₀
  ; old-mark-exact = exact′
  ; fresh-off-old = fresh-off′
  }
  where
  guard₀ = guard exact
  old = CTI2.SmartFreshBehindGuard.oldCenters guard₀
  po = CR.embeddingPushout π old
  premise = CR.EmbeddingPushout.premise po
  old′ = CR.EmbeddingPushout.old′ po
  commutes = CR.EmbeddingPushout.commutes po

  exact′ : ∀ Z′
    → CTI2.impEnvʷ (TE.smartFreshInsertWorld ins guard₀)
        (toRenameᵗ old′ Z′)
      ≡ CTI2.impEnvʷ W′ Z′
  exact′ Z′ with CR.preimage? π Z′ in pre
  exact′ Z′ | nothing =
    trans
      (CR.renameEnv-off premise (CTI2.impEnvʷ Wᵐ)
        (CR.pushout-old-off-premise π old pre))
      (sym (TE.impEnv-off-insert ins pre))
  exact′ Z′ | just Z =
    trans
      (cong (CR.renameEnv premise (CTI2.impEnvʷ Wᵐ)) old-image)
      (trans
        (CR.renameEnv-image premise (CTI2.impEnvʷ Wᵐ)
          (toRenameᵗ old Z))
        (trans (old-mark-exact exact Z) (sym target-image)))
    where
    z′-eq : Z′ ≡ toRenameᵗ π Z
    z′-eq = CR.preimage?-sound π pre

    old-image : toRenameᵗ old′ Z′
      ≡ toRenameᵗ premise (toRenameᵗ old Z)
    old-image = trans (cong (toRenameᵗ old′) z′-eq)
      (sym (commutes Z))

    target-image : CTI2.impEnvʷ W′ Z′ ≡ CTI2.impEnvʷ W Z
    target-image = trans (cong (CTI2.impEnvʷ W′) z′-eq)
      (TE.impEnv-insert ins Z)

  fresh-center =
    toRenameᵗ
      (CTI2.ηᴸʷ (TE.smartFreshInsertWorld ins guard₀)) Fin.zero

  old-fresh-center = toRenameᵗ (CTI2.ηᴸʷ Wᵐ) Fin.zero

  fresh-center-eq : fresh-center ≡ toRenameᵗ premise old-fresh-center
  fresh-center-eq = CR.toRenameᵗ-∘ premise (CTI2.ηᴸʷ Wᵐ) Fin.zero

  fresh-off′ : CR.preimage? old′ fresh-center ≡ nothing
  fresh-off′ with CR.preimage? old′ fresh-center in post-pre
  fresh-off′ | nothing = refl
  fresh-off′ | just Z′ with CR.preimage? π Z′ in root-pre
  fresh-off′ | just Z′ | nothing =
    ⊥-elim
      (CR.pushout-off-image-disjoint π old root-pre
        (trans (sym post-image) fresh-center-eq))
    where
    post-image : fresh-center ≡ toRenameᵗ old′ Z′
    post-image = CR.preimage?-sound old′ post-pre
  fresh-off′ | just Z′ | just Z =
    ⊥-elim
      (impossible (trans (sym old-preimage) (fresh-off-old exact)))
    where
    impossible : just Z ≡ nothing → ⊥
    impossible ()

    post-image : fresh-center ≡ toRenameᵗ old′ Z′
    post-image = CR.preimage?-sound old′ post-pre

    z′-eq : Z′ ≡ toRenameᵗ π Z
    z′-eq = CR.preimage?-sound π root-pre

    old-fresh-eq : toRenameᵗ old Z ≡ old-fresh-center
    old-fresh-eq = toRenameᵗ-injective premise
      (trans (commutes Z)
        (trans (cong (toRenameᵗ old′) (sym z′-eq))
          (trans (sym post-image) fresh-center-eq)))

    old-preimage : CR.preimage? old old-fresh-center ≡ just Z
    old-preimage = trans
      (cong (CR.preimage? old) (sym old-fresh-eq))
      (CR.preimage?-image old Z)


Λ-front-smart-liftCtx : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
  → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
  → CTI2.SmartLiftCtxᴸ γ γᴸ
Λ-front-smart-liftCtx CTI2.liftᴸ-[] = CTI2.smart-lift-[]
Λ-front-smart-liftCtx (CTI2.liftᴸ-∷ liftγ) =
  CTI2.smart-lift-∷ (Λ-front-smart-liftCtx liftγ)


record ΛFrontChildPostPlan {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    (plan : ΛTwoInsertPostPlan W) : Set₁ where
  field
    frontChildPlan :
      ΛTwoInsertPostPlan (CTI2.liftWorldLeft I.X⊑★ W)
    frontPostExact : ExactSmartFreshGuard
      (W₂ plan) (W₂ frontChildPlan)
    frontPostLift : CTI2.SmartCommaLiftᴸ
      (W₂ plan) (W₂ frontChildPlan)
    frontPostLiftCtx : ∀ {γ γᴸ}
      → CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ
      → CTI2.SmartLiftCtxᴸ
          (ECR.mapCtxᴿ (postExtend plan) γ)
          (ECR.mapCtxᴿ (postExtend frontChildPlan) γᴸ)

open ΛFrontChildPostPlan public


Λ-two-insert-front-child : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
  → (plan : ΛTwoInsertPostPlan W)
  → ΛFrontChildPostPlan plan
Λ-two-insert-front-child plan = record
  { frontChildPlan = ΛSmartChildPostPlan.childPlan smartChild
  ; frontPostExact = exact₂
  ; frontPostLift = ΛSmartChildPostPlan.postLift smartChild
  ; frontPostLiftCtx = λ liftγ →
      ΛSmartChildPostPlan.postLiftCtx smartChild
        (Λ-front-smart-liftCtx liftγ)
  }
  where
  smartChild = Λ-two-insert-smart-child plan
    (CTI2.smart-fresh-behind Λ-front-smart-guard)

  exact₁ = exactSmartFreshGuardInsert
    (ins₁ plan) Λ-front-exact-smart-guard

  exact₂ = exactSmartFreshGuardInsert (ins₂ plan) exact₁


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
  ∀⊑ᵂ-from-left-lift
    {W = CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★)
      (＇ Fin.zero)}
    {A = A} {B = B}
    Anv zero∈A
    (Λ⊑²-smart-fresh-untransport {W = W} p)


Λ-post-outer-obligation : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Aₒ : Ty Δᴸ} {B : Ty (suc Δᴿ)}
  → (plan : ΛTwoInsertPostPlan W)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → Aₒ CTI2.⊑ᵂ⟨ W ⟩ `∀ B
  → Aₒ CTI2.⊑ᵂ⟨ W₂ plan ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B


Λ-post-outer-obligation-∀ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → (plan : ΛTwoInsertPostPlan W)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → I._⊢_⊑_ (CTI2.impEnvʷ W)
      (`∀ (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A))
      (`∀ (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B))
  → `∀ A CTI2.⊑ᵂ⟨ W₂ plan ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B


Λ-post-outer-obligation-∀∀-case : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → (plan : ΛTwoInsertPostPlan W)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → I._⊢_⊑_ (I.extᵐ (CTI2.impEnvʷ W))
      (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A)
      (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B)
  → `∀ A CTI2.⊑ᵂ⟨ W₂ plan ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B
Λ-post-outer-obligation-∀∀-case {W = W} {A = A} {B = B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄ body-p =
  ∀⊑ᵂ-from-left-lift
    {W = W₂ plan}
    {A = A} {B = substᵗ Λ⊑Λ²TargetSplit₂ B}
    Anv zero∈A
    (ΛPostWindowGeometry.finalBody⊑ᵂ
      (postGeometry plan) body-pᵂ)
  where
  raw-source-eq :
      renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A
    ≡ CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A
  raw-source-eq = sym (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ W)))

  raw-target-eq :
      renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B
    ≡ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B
  raw-target-eq = sym (renameᵗ-cong B (toRename-keep-eq (CTI2.ηᴿʷ W)))

  body-pᵂ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  body-pᵂ =
    subst≡
      (λ L → I.extᵐ (CTI2.impEnvʷ W) ⊢ L
        ⊑ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
      raw-source-eq
      (subst≡
        (λ R → I.extᵐ (CTI2.impEnvʷ W)
          ⊢ renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A ⊑ R)
        raw-target-eq
        body-p)

  rawBnv : NonVar
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
  rawBnv =
    renameNonVar (toRenameᵗ (keep (CTI2.ηᴿʷ W))) Bnv

  rawZero∈B :
      toRenameᵗ (keep (CTI2.ηᴿʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B
  rawZero∈B =
    rename-occurs (toRenameᵗ (keep (CTI2.ηᴿʷ W))) zero∈B

  rawAnv : NonVar
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
  rawAnv = source-nonvar-from-target body-pᵂ rawBnv rawZero∈B

  rawZero∈A :
      toRenameᵗ (keep (CTI2.ηᴸʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A
  rawZero∈A = target-occurs-source body-pᵂ rawZero∈B

  Anv : NonVar A
  Anv = unrenameNonVar (toRenameᵗ (keep (CTI2.ηᴸʷ W))) rawAnv

  zero∈A : Fin.zero ∈ᵗ A
  zero∈A =
    PIC.unrename-occurs
      (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
      (toRenameᵗ-injective (keep (CTI2.ηᴸʷ W)))
      rawZero∈A
Λ-post-outer-obligation-∀⊑-case : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → (plan : ΛTwoInsertPostPlan W)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → NonVar (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A)
  → Fin.zero ∈ᵗ renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A
  → I._⊢_⊑_ (I.instᵐ (CTI2.impEnvʷ W))
      (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A)
      (⇑ᵗ (CTI2.embedᴿ W (`∀ B)))
  → `∀ A CTI2.⊑ᵂ⟨ W₂ plan ⟩ substᵗ Λ⊑Λ²TargetSplit₂ B
Λ-post-outer-obligation-∀⊑-case {W = W} {A = A} {B = B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄
    rawAnv rawZero∈A rawBody =
  ∀⊑ᵂ-from-left-lift
    {W = W₂ plan}
    {A = A} {B = substᵗ Λ⊑Λ²TargetSplit₂ B}
    Anv zero∈A
    (exactSmartFresh-untransport (frontPostExact front)
      (Λ-post-outer-obligation {Aₒ = A} {B = B}
        (frontChildPlan front)
        ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄
        (subst≡
          (λ R → I.instᵐ (CTI2.impEnvʷ W)
            ⊢ CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W) A
              ⊑ R)
          (sym (target-left-lift-eq (CTI2.ηᴿʷ W) (`∀ B)))
          body-source)))
  where
  front = Λ-two-insert-front-child plan

  raw-source-eq :
      renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A
    ≡ CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W) A
  raw-source-eq = sym (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ W)))

  body-source :
      I.instᵐ (CTI2.impEnvʷ W)
        ⊢ CTI2.embedᴸ (CTI2.liftWorldLeft I.X⊑★ W) A
        ⊑ ⇑ᵗ (CTI2.embedᴿ W (`∀ B))
  body-source =
    subst≡
      (λ L → I.instᵐ (CTI2.impEnvʷ W)
        ⊢ L ⊑ ⇑ᵗ (CTI2.embedᴿ W (`∀ B)))
      raw-source-eq
      rawBody

  Anv : NonVar A
  Anv = unrenameNonVar (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) rawAnv

  zero∈A : Fin.zero ∈ᵗ A
  zero∈A =
    PIC.unrename-occurs
      (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W)))
      (ext-injective (toRenameᵗ-injective (CTI2.ηᴸʷ W)))
      rawZero∈A
Λ-post-outer-obligation-∀ {B = ＇ X} plan ⦃ Bnv = () ⦄ q
Λ-post-outer-obligation-∀ {B = ‵ ι} plan ⦃ zero∈B = () ⦄ q
Λ-post-outer-obligation-∀ {B = ★} plan ⦃ zero∈B = () ⦄ q
Λ-post-outer-obligation-∀ {W = W} {A = A} {B = B₁ ⇒ B₂}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄ (I.∀⊑∀ body-p) =
  Λ-post-outer-obligation-∀∀-case
    {W = W} {A = A} {B = B₁ ⇒ B₂} plan
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ body-p
Λ-post-outer-obligation-∀ {W = W} {A = A} {B = B₁ ⇒ B₂}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄
    (I.∀⊑ rawAnv rawZero∈A rawBody) =
  Λ-post-outer-obligation-∀⊑-case
    {W = W} {A = A} {B = B₁ ⇒ B₂} plan
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄
    rawAnv rawZero∈A rawBody
Λ-post-outer-obligation-∀ {W = W} {A = A} {B = `∀ B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄ (I.∀⊑∀ body-p) =
  Λ-post-outer-obligation-∀∀-case
    {W = W} {A = A} {B = `∀ B} plan
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ body-p
Λ-post-outer-obligation-∀ {W = W} {A = A} {B = `∀ B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄
    (I.∀⊑ rawAnv rawZero∈A rawBody) =
  Λ-post-outer-obligation-∀⊑-case
    {W = W} {A = A} {B = `∀ B} plan
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄
    rawAnv rawZero∈A rawBody


Λ-post-outer-obligation {Aₒ = ＇ X} plan ()
Λ-post-outer-obligation {Aₒ = ‵ ι} plan ()
Λ-post-outer-obligation {Aₒ = ★} plan ()
Λ-post-outer-obligation {Aₒ = A₁ ⇒ A₂} plan ()
Λ-post-outer-obligation {W = W} {Aₒ = `∀ A} {B = B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄ q =
  Λ-post-outer-obligation-∀
    {W = W} {A = A} {B = B} plan
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ q


Λ-source-body-nonvar-occurs-∀∀ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → I._⊢_⊑_ (I.extᵐ (CTI2.impEnvʷ W))
      (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A)
      (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B)
  → NonVar A × Fin.zero ∈ᵗ A
Λ-source-body-nonvar-occurs-∀∀ {W = W} {A = A} {B = B}
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ body-p =
  Anv , zero∈A
  where
  raw-source-eq :
      renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A
    ≡ CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A
  raw-source-eq = sym (renameᵗ-cong A (toRename-keep-eq (CTI2.ηᴸʷ W)))

  raw-target-eq :
      renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B
    ≡ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B
  raw-target-eq = sym (renameᵗ-cong B (toRename-keep-eq (CTI2.ηᴿʷ W)))

  body-pᵂ : A CTI2.⊑ᵂ⟨ CTI2.liftWorldBoth I.X⊑X W ⟩ B
  body-pᵂ =
    subst≡
      (λ L → I.extᵐ (CTI2.impEnvʷ W) ⊢ L
        ⊑ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
      raw-source-eq
      (subst≡
        (λ R → I.extᵐ (CTI2.impEnvʷ W)
          ⊢ renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A ⊑ R)
        raw-target-eq
        body-p)

  rawBnv : NonVar
      (CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B)
  rawBnv =
    renameNonVar (toRenameᵗ (keep (CTI2.ηᴿʷ W))) Bnv

  rawZero∈B :
      toRenameᵗ (keep (CTI2.ηᴿʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴿ (CTI2.liftWorldBoth I.X⊑X W) B
  rawZero∈B =
    rename-occurs (toRenameᵗ (keep (CTI2.ηᴿʷ W))) zero∈B

  rawAnv : NonVar
      (CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A)
  rawAnv = source-nonvar-from-target body-pᵂ rawBnv rawZero∈B

  rawZero∈A :
      toRenameᵗ (keep (CTI2.ηᴸʷ W)) Fin.zero
        ∈ᵗ CTI2.embedᴸ (CTI2.liftWorldBoth I.X⊑X W) A
  rawZero∈A = target-occurs-source body-pᵂ rawZero∈B

  Anv : NonVar A
  Anv = unrenameNonVar (toRenameᵗ (keep (CTI2.ηᴸʷ W))) rawAnv

  zero∈A : Fin.zero ∈ᵗ A
  zero∈A =
    PIC.unrename-occurs
      (toRenameᵗ (keep (CTI2.ηᴸʷ W)))
      (toRenameᵗ-injective (keep (CTI2.ηᴸʷ W)))
      rawZero∈A


Λ-source-body-nonvar-occurs-∀⊑ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → NonVar (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A)
  → Fin.zero ∈ᵗ renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A
  → NonVar A × Fin.zero ∈ᵗ A
Λ-source-body-nonvar-occurs-∀⊑ {W = W} rawAnv rawZero∈A =
  unrenameNonVar (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) rawAnv ,
  PIC.unrename-occurs
    (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W)))
    (ext-injective (toRenameᵗ-injective (CTI2.ηᴸʷ W)))
    rawZero∈A


Λ-source-body-nonvar-occurs-∀ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → I._⊢_⊑_ (CTI2.impEnvʷ W)
      (`∀ (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴸʷ W))) A))
      (`∀ (renameᵗ (extᵗ (toRenameᵗ (CTI2.ηᴿʷ W))) B))
  → NonVar A × Fin.zero ∈ᵗ A
Λ-source-body-nonvar-occurs-∀ {B = ＇ X} ⦃ Bnv = () ⦄ q
Λ-source-body-nonvar-occurs-∀ {B = ‵ ι} ⦃ zero∈B = () ⦄ q
Λ-source-body-nonvar-occurs-∀ {B = ★} ⦃ zero∈B = () ⦄ q
Λ-source-body-nonvar-occurs-∀ {W = W} {A = A} {B = B₁ ⇒ B₂}
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ (I.∀⊑∀ body-p) =
  Λ-source-body-nonvar-occurs-∀∀
    {W = W} {A = A} {B = B₁ ⇒ B₂}
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ body-p
Λ-source-body-nonvar-occurs-∀ {W = W} {A = A} {B = B₁ ⇒ B₂}
    (I.∀⊑ rawAnv rawZero∈A rawBody) =
  Λ-source-body-nonvar-occurs-∀⊑ {W = W} {A = A}
    {B = B₁ ⇒ B₂}
    rawAnv rawZero∈A
Λ-source-body-nonvar-occurs-∀ {W = W} {A = A} {B = `∀ B}
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ (I.∀⊑∀ body-p) =
  Λ-source-body-nonvar-occurs-∀∀
    {W = W} {A = A} {B = `∀ B}
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ body-p
Λ-source-body-nonvar-occurs-∀ {W = W} {A = A} {B = `∀ B}
    (I.∀⊑ rawAnv rawZero∈A rawBody) =
  Λ-source-body-nonvar-occurs-∀⊑ {W = W} {A = A}
    {B = `∀ B}
    rawAnv rawZero∈A


Λ-source-body-nonvar-occurs : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B
  → NonVar A × Fin.zero ∈ᵗ A
Λ-source-body-nonvar-occurs {W = W} {A = A} {B = B}
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ q =
  Λ-source-body-nonvar-occurs-∀
    {W = W} {A = A} {B = B}
    ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ q


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


Λ-route1-smart-alias-left-ext₂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δ}
    {β α : Fin.Fin Δᴿ}
  → (guard : CTI2.SmartAliasMergeGuard W Wᵐ β α)
  → ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ Wᵐ)
      (CTI2.liftWorldLeft I.X⊑★
        (TE.smartAliasInsertWorld
          (TE.rightBindTargetInsert
            {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
          (TE.smartAliasInsertWorld
            (TE.rightBindTargetInsert {W = W} {B = ★}) Wᵐ)))
Λ-route1-smart-alias-left-ext₂ {W = W} guard =
  composeWorldExtendᴿ
    (smart-alias-bind-under-left-liftᴿ {W = W} {B = ★} guard)
    (smart-alias-bind-under-left-liftᴿ
      {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero} guard₁)
  where
  guard₁ =
    TE.smartAliasGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard


Λ-route1-smart-fresh-left-ext₂ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → (guard : CTI2.SmartFreshBehindGuard W Wᵐ)
  → ECR.WorldExtendᴿ (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ Wᵐ)
      (CTI2.liftWorldLeft I.X⊑★
        (TE.smartFreshInsertWorld
          (TE.rightBindTargetInsert
            {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero})
          (TE.smartFreshGuardInsert
            (TE.rightBindTargetInsert {W = W} {B = ★}) guard)))
Λ-route1-smart-fresh-left-ext₂ {W = W} guard =
  composeWorldExtendᴿ
    (smart-fresh-bind-under-left-liftᴿ {W = W} {B = ★} guard)
    (smart-fresh-bind-under-left-liftᴿ
      {W = CTI2.rightOnlyWorld W ★} {B = ＇ Fin.zero} guard₁)
  where
  guard₁ =
    TE.smartFreshGuardInsert
      (TE.rightBindTargetInsert {W = W} {B = ★}) guard


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
  → (bodyPkg : InstPostCatalogPackageAt fuel bodyRel vV vΛV′ c′
      B′≢★ c<fuel body-q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (Λ⊑²-smart-fresh-world W)
      (right-bind-right-bind-world-extendᴿ
        {W = CTI2.liftWorldLeft I.X⊑★ W}
        {B = ★} {C = ＇ Fin.zero}))
  → CT.Value (InstPostCatalogPackageAt.at-post bodyPkg)
  → InstPostCatalogPackageAt fuel rel vΛV vΛV′ c′
      B′≢★ c<fuel q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (right-bind-right-bind-world-extendᴿ
        {W = W} {B = ★} {C = ＇ Fin.zero})
Λ⊑²-smart-recursive-package-at {W = W}
    rel vΛV vΛV′ vV c′ B′≢★ c<fuel body-q q
    liftγ Anv zero∈A bodyRel bodyPkg vPost =
  record
    { at-B₂ = InstPostCatalogPackageAt.at-B₂ bodyPkg
    ; at-post = InstPostCatalogPackageAt.at-post bodyPkg
    ; at-p₂ =
        Λ⊑²-smart-fresh-top {W = W} Anv zero∈A
          (InstPostCatalogPackageAt.at-p₂ bodyPkg)
    ; at-post-relation =
        Λ⊑²-smart-fresh-at-rewrap Anv zero∈A liftγ vV
          (InstPostCatalogPackageAt.at-post-relation bodyPkg)
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
        spine-descent-zero vPost
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


record ΛPostPrefixPackageAtBase
    {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    (rel : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p)
    (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂)
    (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    (B′≢★ : B′ ≢ ★) : Set₁ where
  field
    prefix-p₂ : A CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B
    prefix-relation :
      W₂ CTI2.∣ ECR.mapCtxᴿ ext₂ γ
        ⊢² M ⊑ Λ⊑Λ²PostTerm V′ B ∶ prefix-p₂
    prefix-value : Value (Λ⊑Λ²PostTerm V′ B)
    prefix-reduction :
      (Λ V′) ⟨ (inst c′) B′≢★ ⟩
        —↠[ bind ★ ∷ bind (＇ Fin.zero) ∷ [] ]
      Λ⊑Λ²PostTerm V′ B ⟨
        applyConsistency (bind {Δ = suc Δᴿ} (＇ Fin.zero))
          (↑ᶜ (close-instᶜ c′)) ⟩


Λ-post-prefix-concrete-base : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {rel : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p}
    {c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → {B′≢★ : B′ ≢ ★}
  → ΛPostPrefixPackageAt rel c′ B′≢★
  → ΛPostPrefixPackageAtBase rel
      (right-bind-right-bind-world-extendᴿ
        {W = W} {B = ★} {C = ＇ Fin.zero})
      c′ B′≢★
Λ-post-prefix-concrete-base prefix =
  record
    { prefix-p₂ = ΛPostPrefixPackageAt.prefix-p₂ prefix
    ; prefix-relation = ΛPostPrefixPackageAt.prefix-relation prefix
    ; prefix-value = ΛPostPrefixPackageAt.prefix-value prefix
    ; prefix-reduction = ΛPostPrefixPackageAt.prefix-reduction prefix
    }


smartCommaLift-target-store : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
  → CTI2.SmartCommaLiftᴸ W Wᵐ
  → CTI2.targetStoreʷ Wᵐ ≡ CTI2.targetStoreʷ W
smartCommaLift-target-store (CTI2.smart-fresh-behind guard) =
  CTI2.SmartFreshBehindGuard.targetStore-same guard
smartCommaLift-target-store (CTI2.smart-merge-alias guard) =
  CTI2.SmartAliasMergeGuard.targetStore-same guard


smartLiftCtxᴸ-target-ctx : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
  → CTI2.SmartLiftCtxᴸ {W = W} {Wᵐ = Wᵐ} γ γᵐ
  → CTI2.tgtCtxʷ γᵐ ≡ CTI2.tgtCtxʷ γ
smartLiftCtxᴸ-target-ctx CTI2.smart-lift-[] = refl
smartLiftCtxᴸ-target-ctx (CTI2.smart-lift-∷ liftγ) =
  cong (_ ∷_) (smartLiftCtxᴸ-target-ctx liftγ)


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


post-source-conceal-partner-ok : ∀ {Δᴸ Δᴿ Δ₂}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)} {Xᴿ?}
    {c : Conv↓ Δᴸ A A′}
  → CTI2.SourceConcealPartnerOK W₂ M c Xᴿ?
      (Λ⊑Λ²PostTerm V′ B)
post-source-conceal-partner-ok {c = seal X R} =
  CTI2.seal-partner-ok (CTI2.plain-target CTI2.not-↑)
post-source-conceal-partner-ok {c = c ↦↓ d} =
  CTI2.fun-conceal-target
post-source-conceal-partner-ok {c = `∀↓ c} =
  CTI2.all-conceal-target
post-source-conceal-partner-ok {c = id↓ A} =
  CTI2.id-conceal-target


Λ-strip-prefix-p₂ : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)}
  → (plan : ΛTwoInsertPostPlan W)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → A CTI2.⊑ᵂ⟨ W ⟩ `∀ B
  → A CTI2.⊑ᵂ⟨ W₂ plan ⟩ ΛResidualSource₂ B
Λ-strip-prefix-p₂ {W = W} {A = A} {B = B}
    plan ⦃ Bnv ⦄ ⦃ zero∈B ⦄ q =
  subst≡
    (λ C → A CTI2.⊑ᵂ⟨ W₂ plan ⟩ C)
    (residual-source₂-eq B)
    (Λ-post-outer-obligation
      {W = W} {Aₒ = A} {B = B} plan
      ⦃ Bnv = Bnv ⦄ ⦃ zero∈B = zero∈B ⦄ q)


right-bind-right-bind-mono : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
  → CTI2.ImpEnvMono W Wᵖ
  → CTI2.ImpEnvMono
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld Wᵖ ★) (＇ Fin.zero))
right-bind-right-bind-mono {W = W} {Wᵖ = Wᵖ} mono =
  rightOnlyImpEnvMono
    {W = CTI2.rightOnlyWorld W ★}
    {Wᵖ = CTI2.rightOnlyWorld Wᵖ ★}
    {B = ＇ Fin.zero}
    (rightOnlyImpEnvMono {W = W} {Wᵖ = Wᵖ} {B = ★} mono)


right-bind-right-bind-rebaseᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → CTI2.RebaseAtᴸ
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld Wᵖ ★) (＇ Fin.zero))
      Xᴸ?
right-bind-right-bind-rebaseᴸ rb =
  TE.rightRebaseAtᴸ {B = ＇ Fin.zero}
    (TE.rightRebaseAtᴸ {B = ★} rb)


right-bind-right-bind-tag-rebaseᴸ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → CTI2.TagRebaseAtᴸ
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld W ★) (＇ Fin.zero))
      (CTI2.rightOnlyWorld (CTI2.rightOnlyWorld Wᵖ ★) (＇ Fin.zero))
      Xᴸ?
      (TE.mapPivot (toRenameᵗ wk↪ᵗ)
        (TE.mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?))
right-bind-right-bind-tag-rebaseᴸ rb =
  TE.rightTagRebaseAtᴸ {B = ＇ Fin.zero}
    (TE.rightTagRebaseAtᴸ {B = ★} rb)


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


Λ-post-prefix-base→package-at : ∀ {fuel Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
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
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂)
  → ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★
  → InstPostCatalogPackageAt fuel rel vM vΛV′ c′ B′≢★
      c<fuel q
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W₂ ext₂
Λ-post-prefix-base→package-at {fuel = fuel} {Δᴿ = Δᴿ}
    {Δ₂ = Δ₂} {W = W} {W₂ = W₂} {V′ = V′}
    {A = A} {B = B} {B′ = B′}
    inst-decrease rel vM vΛV′ c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ c<fuel q ext₂ prefix =
  record
    { at-B₂ = ΛResidualSource₂ B
    ; at-post = Λ⊑Λ²PostTerm V′ B
    ; at-p₂ = ΛPostPrefixPackageAtBase.prefix-p₂ prefix
    ; at-post-relation =
        ΛPostPrefixPackageAtBase.prefix-relation prefix
    ; at-ν₂ = _
    ; at-residual-target = ΛResidualTarget₂ B′
    ; at-residual-q =
        subst≡ (λ C → A CTI2.⊑ᵂ⟨ W₂ ⟩ C)
          (residual-target₂-eq B′)
          (ECR.transport⊑ᵂ ext₂ q)
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
        ΛPostPrefixPackageAtBase.prefix-reduction prefix
    ; at-spine-descent =
        spine-descent-zero
          (ΛPostPrefixPackageAtBase.prefix-value prefix)
          (ΛPostPrefixPackageAtBase.prefix-relation prefix)
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


Λ⊑Λ²-base-prefix-at-base : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
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
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂)
  → ΛPostWindowGeometry W W₂ ext₂
  → (liftγ : CTI2.LiftCtx I.X⊑X γ γᴮ)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → CTI2.liftWorldBoth I.X⊑X W CTI2.∣ γᴮ
      ⊢² V ⊑ V′ ∶ body-p
  → ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★
Λ⊑Λ²-base-prefix-at-base {Δᴿ = Δᴿ} {W₂ = W₂}
    {V′ = V′} {A = A} {B = B} rel vV vV′ c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ ext₂ geom liftγ Anv zero∈A bodyRel
    with Λ⊑Λ²-post-body-transport-at geom Anv zero∈A
      liftγ vV vV′ bodyRel
... | γ₂ᴸ , body-p₂ , top-p₂ ,
      liftγ₂ , vPost , post⊢ , bodyRel₂ =
  record
    { prefix-p₂ =
        subst≡ (λ C → `∀ A CTI2.⊑ᵂ⟨ W₂ ⟩ C)
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


Λ⊑²-plain-shared-prefix-at : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (liftγᴸ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTI2.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → ΛPostPrefixPackageAt
      (CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
        (CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel inner-p) outer-p)
      c′ B′≢★
Λ⊑²-plain-shared-prefix-at vV vV′ c′ B′≢★ liftγᴸ liftγᴮ
    Anv zero∈A outer∈ target⊢ bodyRel =
  Λ⊑²-smart-recursive-prefix-at outerRel (CT.Λ vV) c′ B′≢★
    liftγᴸ nonvar-all outer∈ innerRel
    (Λ⊑Λ²-base-prefix-at innerRel vV vV′ c′ B′≢★ liftγᴮ
      Anv zero∈A bodyRel)
  where
  innerRel = CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel _

  outerRel =
    CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
      innerRel _


Λ⊑²-plain-recursive-prefix-at-base : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᴸ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ W)
      (CTI2.liftWorldLeft I.X⊑★ W₂)}
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vV : CT.Value V)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → CTI2.LiftCtxᴸ I.X⊑★ (ECR.mapCtxᴿ ext₂ γ)
      (ECR.mapCtxᴿ extᴸ₂ γᴸ)
  → (bodyRel : CTI2.liftWorldLeft I.X⊑★ W CTI2.∣ γᴸ
      ⊢² V ⊑ Λ V′ ∶ body-p)
  → (top-p₂ : `∀ A CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase bodyRel extᴸ₂ c′ B′≢★
  → ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★
Λ⊑²-plain-recursive-prefix-at-base {Δᴿ = Δᴿ}
    {W₂ = W₂} {γ = γ} {γᴸ = γᴸ}
    {V′ = V′} {B = B} {ext₂ = ext₂} {extᴸ₂ = extᴸ₂}
    rel vV c′ B′≢★ Anv zero∈A liftγ₂ bodyRel top-p₂ bodyPrefix =
  record
    { prefix-p₂ = top-p₂
    ; prefix-relation =
        Λ⊑²-at-rewrap Anv zero∈A liftγ₂ vV target⊢
          (ΛPostPrefixPackageAtBase.prefix-relation bodyPrefix)
    ; prefix-value =
        ΛPostPrefixPackageAtBase.prefix-value bodyPrefix
    ; prefix-reduction =
        ΛPostPrefixPackageAtBase.prefix-reduction bodyPrefix
    }
  where
  postRel = ΛPostPrefixPackageAtBase.prefix-relation bodyPrefix

  postTarget⊢ᴸ :
      ⟨ suc (suc Δᴿ) ,
        CTI2.targetStoreʷ (CTI2.liftWorldLeft I.X⊑★ W₂) ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ extᴸ₂ γᴸ) ⟩
      ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B
  postTarget⊢ᴸ = CTI2T.target-typing² postRel

  target⊢ :
      ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
      ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B
  target⊢ =
    subst≡
      (λ Γ → ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ , Γ ⟩
        ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B)
      (liftCtxᴸ-target liftγ₂)
      postTarget⊢ᴸ


Λ⊑²-smart-recursive-prefix-at-base : ∀ {Δᴸ Δᴿ Δ Δᵐ Δ₂ Δᵐ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTI2.World (suc Δᴸ) Δᴿ Δᵐ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᵐ₂ : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) Δᵐ₂}
    {γ : CTI2.CtxImp W} {γᵐ : CTI2.CtxImp Wᵐ}
    {V : CT.Term (suc Δᴸ)} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨ Wᵐ ⟩ `∀ B}
    {p : `∀ A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᵐ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) Wᵐ Wᵐ₂}
  → (rel : W CTI2.∣ γ ⊢² Λ V ⊑ Λ V′ ∶ p)
  → (vV : CT.Value V)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → CTI2.SmartCommaLiftᴸ W₂ Wᵐ₂
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᵐ₂ γᵐ)
  → (bodyRel : Wᵐ CTI2.∣ γᵐ ⊢² V ⊑ Λ V′ ∶ body-p)
  → (top-p₂ : `∀ A CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase bodyRel extᵐ₂ c′ B′≢★
  → ΛPostPrefixPackageAtBase rel ext₂ c′ B′≢★
Λ⊑²-smart-recursive-prefix-at-base {Δᴿ = Δᴿ}
    {W₂ = W₂} {Wᵐ₂ = Wᵐ₂} {γ = γ} {γᵐ = γᵐ}
    {V′ = V′} {B = B} {ext₂ = ext₂} {extᵐ₂ = extᵐ₂}
    rel vV c′ B′≢★ Anv zero∈A liftW₂ liftγ₂ bodyRel top-p₂
    bodyPrefix =
  record
    { prefix-p₂ = top-p₂
    ; prefix-relation =
        CTI2.Λ⊑²-smart-comma Anv zero∈A liftW₂ liftγ₂ vV
          target⊢
          (ΛPostPrefixPackageAtBase.prefix-relation bodyPrefix)
          top-p₂
    ; prefix-value =
        ΛPostPrefixPackageAtBase.prefix-value bodyPrefix
    ; prefix-reduction =
        ΛPostPrefixPackageAtBase.prefix-reduction bodyPrefix
    }
  where
  postRel = ΛPostPrefixPackageAtBase.prefix-relation bodyPrefix

  postTarget⊢ᵐ :
      ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ Wᵐ₂ ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ extᵐ₂ γᵐ) ⟩
      ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B
  postTarget⊢ᵐ = CTI2T.target-typing² postRel

  target⊢ :
      ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ ,
        CTI2.tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
      ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B
  target⊢ =
    subst≡
      (λ Γ → ⟨ suc (suc Δᴿ) , CTI2.targetStoreʷ W₂ , Γ ⟩
        ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B)
      (smartLiftCtxᴸ-target-ctx liftγ₂)
      (subst≡
        (λ Σ → ⟨ suc (suc Δᴿ) , Σ ,
          CTI2.tgtCtxʷ (ECR.mapCtxᴿ extᵐ₂ γᵐ) ⟩
          ⊢ Λ⊑Λ²PostTerm V′ B ⦂ ΛResidualSource₂ B)
        (smartCommaLift-target-store liftW₂)
        postTarget⊢ᵐ)


Λ⊑²-plain-shared-prefix-at-base : ∀ {Δᴸ Δᴿ Δ Δ₂ Δᶠ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᶠ₂ : CTI2.World (suc Δᴸ) (suc (suc Δᴿ)) Δᶠ₂}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᶠ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      (CTI2.liftWorldLeft I.X⊑★ W) Wᶠ₂}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (liftγᴸ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTI2.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → CTI2.SmartCommaLiftᴸ W₂ Wᶠ₂
  → CTI2.SmartLiftCtxᴸ
      (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᶠ₂ γᴸ)
  → ΛPostWindowGeometry
      (CTI2.liftWorldLeft I.X⊑★ W) Wᶠ₂ extᶠ₂
  → (`∀ (`∀ A) CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase
      (CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
        (CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel inner-p) outer-p)
      ext₂ c′ B′≢★
Λ⊑²-plain-shared-prefix-at-base vV vV′ c′ B′≢★ liftγᴸ liftγᴮ
    Anv zero∈A outer∈ target⊢ bodyRel liftW₂ liftγ₂ geom top-p₂ =
  Λ⊑²-smart-recursive-prefix-at-base outerRel (CT.Λ vV)
    c′ B′≢★ nonvar-all outer∈ liftW₂ liftγ₂ innerRel top-p₂
    (Λ⊑Λ²-base-prefix-at-base innerRel vV vV′ c′ B′≢★
      _ geom liftγᴮ Anv zero∈A bodyRel)
  where
  innerRel = CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel _

  outerRel =
    CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
      innerRel _


Λ⊑²-plain-shared-smart-plan-prefix-at-base : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {γᴸ : CTI2.CtxImp (CTI2.liftWorldLeft I.X⊑★ W)}
    {γᴮ : CTI2.CtxImp
      (CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W))}
    {V : CT.Term (suc (suc Δᴸ))} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty (suc (suc Δᴸ))} {B : Ty (suc Δᴿ)}
    {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {body-p : A CTI2.⊑ᵂ⟨
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
      ⟩ B}
    {inner-p : `∀ A CTI2.⊑ᵂ⟨
      CTI2.liftWorldLeft I.X⊑★ W ⟩ `∀ B}
    {outer-p : `∀ (`∀ A) CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (vV : CT.Value V)
  → (vV′ : CT.Value V′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (liftγᴸ : CTI2.LiftCtxᴸ I.X⊑★ γ γᴸ)
  → (liftγᴮ : CTI2.LiftCtx I.X⊑X γᴸ γᴮ)
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (outer∈ : Fin.zero ∈ᵗ `∀ A)
  → (target⊢ :
      ⟨ Δᴿ , CTI2.targetStoreʷ W , CTI2.tgtCtxʷ γ ⟩
        ⊢ Λ V′ ⦂ `∀ B)
  → (bodyRel :
      CTI2.liftWorldBoth I.X⊑X (CTI2.liftWorldLeft I.X⊑★ W)
        CTI2.∣ γᴮ ⊢² V ⊑ V′ ∶ body-p)
  → ΛPostPrefixPackageAtBase
      (CTI2.Λ⊑² nonvar-all outer∈ liftγᴸ (CT.Λ vV) target⊢
        (CTI2.Λ⊑Λ² liftγᴮ vV vV′ bodyRel inner-p) outer-p)
      (right-bind-right-bind-world-extendᴿ
        {W = W} {B = ★} {C = ＇ Fin.zero})
      c′ B′≢★
Λ⊑²-plain-shared-smart-plan-prefix-at-base {W = W} {A = A} {B = B}
    {outer-p = outer-p} vV vV′ c′ B′≢★ liftγᴸ liftγᴮ
    Anv zero∈A outer∈ target⊢ bodyRel =
  Λ⊑²-plain-shared-prefix-at-base vV vV′ c′ B′≢★
    liftγᴸ liftγᴮ Anv zero∈A outer∈ target⊢ bodyRel
    (CTI2.smart-fresh-behind (Λ⊑²-smart-fresh-guard {W = W}))
    (mapCtxᴿ-smart-fresh-liftᴸ liftγᴸ)
    (Λ-concrete-post-window
      {W = CTI2.liftWorldLeft I.X⊑★ W})
    (Λ-strip-prefix-p₂ {W = W} {A = `∀ (`∀ A)} {B = B}
      Λ-concrete-two-insert-post-plan outer-p)


Λ-post-prefix-cast⊑²-base : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {νᴸ : Env∼ Δᴸ}
    {p₀ : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {p : A′ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
    {prem : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p₀}
    (c : νᴸ ⊢ A ∼ A′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (top-p₂ : A′ CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase prem ext₂ c′ B′≢★
  → ΛPostPrefixPackageAtBase (CTI2.cast⊑² c prem p) ext₂
      c′ B′≢★
Λ-post-prefix-cast⊑²-base c B′≢★ top-p₂ prefix =
  record
    { prefix-p₂ = top-p₂
    ; prefix-relation =
        CTI2.cast⊑² c
          (ΛPostPrefixPackageAtBase.prefix-relation prefix)
          top-p₂
    ; prefix-value = ΛPostPrefixPackageAtBase.prefix-value prefix
    ; prefix-reduction =
        ΛPostPrefixPackageAtBase.prefix-reduction prefix
    }


rebaseAtᴸ-target-store : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → CTI2.targetStoreʷ Wᵖ ≡ CTI2.targetStoreʷ W
rebaseAtᴸ-target-store CTI2.rebase-idᴸ = refl
rebaseAtᴸ-target-store (CTI2.rebase-varᴸ rb) =
  CTI2.SameRuntime.targetStore-same (CTI2.RebaseAt.sameRuntime rb)
rebaseAtᴸ-target-store (CTI2.rebase-onlyᴸ to-star disaligned rep) =
  refl


rebaseAtᴸ-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → ∀ Y → toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
rebaseAtᴸ-target-frozen CTI2.rebase-idᴸ Y = refl
rebaseAtᴸ-target-frozen (CTI2.rebase-varᴸ rb) =
  CTI2.RebaseAt.ηᴿ-frozen rb
rebaseAtᴸ-target-frozen (CTI2.rebase-onlyᴸ to-star disaligned rep) =
  λ Y → refl


tagRebaseAtᴸ-target-store : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → CTI2.targetStoreʷ Wᵖ ≡ CTI2.targetStoreʷ W
tagRebaseAtᴸ-target-store CTI2.tag-rebase-idᴸ = refl
tagRebaseAtᴸ-target-store (CTI2.tag-rebase-varᴸ rb) =
  CTI2.SameRuntime.targetStore-same (CTI2.RebaseAt.sameRuntime rb)
tagRebaseAtᴸ-target-store
    (CTI2.tag-rebase-onlyᴸ to-star disaligned rep) = refl


tagRebaseAtᴸ-target-frozen : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → CTI2.TagRebaseAtᴸ W Wᵖ Xᴸ? Xᴿ?
  → ∀ Y → toRenameᵗ (CTI2.ηᴿʷ Wᵖ) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y
tagRebaseAtᴸ-target-frozen CTI2.tag-rebase-idᴸ Y = refl
tagRebaseAtᴸ-target-frozen (CTI2.tag-rebase-varᴸ rb) =
  CTI2.RebaseAt.ηᴿ-frozen rb
tagRebaseAtᴸ-target-frozen
    (CTI2.tag-rebase-onlyᴸ to-star disaligned rep) Y = refl


rebaseTargetWindowInsert : ∀ {Δᴸ Δᴿ Δ Δ′}
    {π : Δ ↪ᵗ Δ′} {κ : suc Δ ↪ᵗ Δ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ′ : CTI2.World Δᴸ (suc Δᴿ) Δ′}
    {ins : TE.TargetInsert wk↪ᵗ π W W′}
    {insᵖ : TE.TargetInsert wk↪ᵗ π Wᵖ Wᵖ′}
  → TE.TargetWindowInsert ins κ
  → (∀ Y → toRenameᵗ (CTI2.ηᴿʷ Wᵖ′) Y
      ≡ toRenameᵗ (CTI2.ηᴿʷ W′) Y)
  → TE.TargetWindowInsert insᵖ κ
rebaseTargetWindowInsert win frozen = record
  { windowEmbedding = TE.windowEmbedding win
  ; window-zero = trans (frozen Fin.zero) (TE.window-zero win)
  ; window-old = TE.window-old win
  }


record ΛRebaseChildPostPlan {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    (plan : ΛTwoInsertPostPlan W) (Xᴸ? : Maybe (Fin.Fin Δᴸ))
    : Set₁ where
  field
    childPlan : ΛTwoInsertPostPlan Wᵖ
    sameΔ₂ : Δ₂ childPlan ≡ Δ₂ plan
    postMono : CTI2.ImpEnvMono W Wᵖ
      → CTI2.ImpEnvMono (W₂ plan)
          (subst≡ (CTI2.World _ _) sameΔ₂ (W₂ childPlan))
    postRebase : CTI2.RebaseAtᴸ
      (W₂ plan) (subst≡ (CTI2.World _ _) sameΔ₂ (W₂ childPlan))
      Xᴸ?


record ΛTagRebaseChildPostPlan {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    (plan : ΛTwoInsertPostPlan W)
    (Xᴸ? : Maybe (Fin.Fin Δᴸ)) (Xᴿ? : Maybe (Fin.Fin Δᴿ))
    : Set₁ where
  field
    childPlan : ΛTwoInsertPostPlan Wᵖ
    sameΔ₂ : Δ₂ childPlan ≡ Δ₂ plan
    postMono : CTI2.ImpEnvMono W Wᵖ
      → CTI2.ImpEnvMono (W₂ plan)
          (subst≡ (CTI2.World _ _) sameΔ₂ (W₂ childPlan))
    postRebase : CTI2.TagRebaseAtᴸ
      (subst≡ (CTI2.World _ _) sameΔ₂ (W₂ childPlan))
      (W₂ plan) Xᴸ?
      (TE.mapPivot (toRenameᵗ wk↪ᵗ)
        (TE.mapPivot (toRenameᵗ wk↪ᵗ) Xᴿ?))


Λ-two-insert-rebase-child : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ?}
  → (plan : ΛTwoInsertPostPlan W)
  → CTI2.RebaseAtᴸ W Wᵖ Xᴸ?
  → ΛRebaseChildPostPlan plan Xᴸ?
Λ-two-insert-rebase-child plan rb
    with TE.insertRebaseAtᴸ (ins₁ plan) rb
Λ-two-insert-rebase-child plan rb | Wᵖ₁ , insᵖ₁ , rb₁
    with TE.insertRebaseAtᴸ (ins₂ plan) rb₁
Λ-two-insert-rebase-child plan rb
    | Wᵖ₁ , insᵖ₁ , rb₁ | Wᵖ₂ , insᵖ₂ , rb₂ =
  record
    { childPlan = child ; sameΔ₂ = refl
    ; postMono = λ mono → TE.impEnvMono-insert (ins₂ plan) insᵖ₂
        (TE.impEnvMono-insert (ins₁ plan) insᵖ₁ mono)
    ; postRebase = rb₂
    }
  where
  follows₁ = trans (rebaseAtᴸ-target-store rb₁)
    (trans (targetFollows₁ plan)
      (cong (applyStores (bind ★ ∷ []))
        (sym (rebaseAtᴸ-target-store rb))))
  follows₂ = trans (rebaseAtᴸ-target-store rb₂)
    (trans (targetFollows₂ plan)
      (cong (applyStores (bind (＇ Fin.zero) ∷ []))
        (sym (rebaseAtᴸ-target-store rb₁))))
  store₁ = rebaseAtᴸ-target-store rb₁
  store₂ = rebaseAtᴸ-target-store rb₂
  winᵖ₁ = rebaseTargetWindowInsert
    (targetWindow₁ (windowFacts plan))
    (rebaseAtᴸ-target-frozen rb₁)
  winᵖ₂ = rebaseTargetWindowInsert
    (targetWindow₂ (windowFacts plan))
    (rebaseAtᴸ-target-frozen rb₂)
  extᵖ = composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ insᵖ₁ follows₁)
    (target-insert-bind-world-extendᴿ insᵖ₂ follows₂)
  facts = record
    { targetWindow₁ = winᵖ₁ ; targetWindow₂ = winᵖ₂
    ; pivotMark = subst≡ (λ C → CTI2.impEnvʷ
          (CR.renameWorld (skip (κ₂ plan))
            (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) C ≡ I.X⊑★)
        (sym (CR.toRenameᵗ-∘ (skip (κ₂ plan))
          (CTI2.ηᴿʷ (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) Fin.zero))
        (CR.renameEnv-image (skip (κ₂ plan))
          (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) Fin.zero)
    ; targetStoreTransport = subst≡
        (λ Σ₁ → StoreTransport (store-lift Σ₁)
          (CTI2.targetStoreʷ Wᵖ₂)) (sym store₁)
        (subst≡ (λ Σ₂ → StoreTransport
            (store-lift (CTI2.targetStoreʷ (W₁ plan))) Σ₂)
          (sym store₂) (targetStoreTransport (windowFacts plan)))
    ; firstTargetZeroResolves = subst≡
        (λ Σ → CTI2.resolveVar Σ Fin.zero ≡ ★)
        (sym store₁) (firstTargetZeroResolves (windowFacts plan))
    ; targetZeroResolves = subst≡
        (λ Σ → CTI2.resolveVar Σ Fin.zero ≡ ★)
        (sym store₂) (targetZeroResolves (windowFacts plan))
    ; targetOtherResolves = λ Z neq → subst≡
        (λ Σ₁ → CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ₂) Z
          ≡ CTI2.resolveVar (store-lift Σ₁) Z) (sym store₁)
        (subst≡ (λ Σ₂ → CTI2.resolveVar Σ₂ Z
            ≡ CTI2.resolveVar
              (store-lift (CTI2.targetStoreʷ (W₁ plan))) Z)
          (sym store₂) (targetOtherResolves (windowFacts plan) Z neq))
    ; midSourcePivotMark =
        route1-mid-source-pivot-from-windows winᵖ₁ winᵖ₂ }
  first-entry = subst≡
    (λ Σ → Σ ∋ Fin.zero ⦂ ⇑ᵗ ★) (sym follows₁) (Z∋ refl)
  support = Λ-route1-post-window-support-at facts
    (Λ-route1-mid-fresh-mono-at facts)
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just Fin.zero ] _)
      (sym follows₂) (generated-reveal-⊢↑-present z (Z∋ refl)))
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just (Fin.suc Fin.zero) ] _)
      (sym follows₂) (TE.reveal-renameˣ StoreRename-suc-bind
        (generated-reveal-⊢↑-present z first-entry)))
  child = record
    { Δ₁ = Δ₁ plan ; Δ₂ = Δ₂ plan ; W₁ = Wᵖ₁ ; W₂ = Wᵖ₂
    ; π₁ = π₁ plan ; π₂ = π₂ plan
    ; κ₁ = κ₁ plan ; κ₂ = κ₂ plan
    ; ins₁ = insᵖ₁ ; ins₂ = insᵖ₂
    ; targetFollows₁ = follows₁ ; targetFollows₂ = follows₂
    ; windowFacts = facts ; postExtend = extᵖ
    ; postGeometry = Λ-route1-post-window-at facts support
    }


Λ-two-insert-tag-rebase-child : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : CTI2.World Δᴸ Δᴿ Δ} {Xᴸ? Xᴿ?}
  → (plan : ΛTwoInsertPostPlan W)
  → CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?
  → ΛTagRebaseChildPostPlan plan Xᴸ? Xᴿ?
Λ-two-insert-tag-rebase-child plan rb
    with TE.reverseTagRebaseAtᴸ (ins₁ plan) rb
Λ-two-insert-tag-rebase-child plan rb | Wᵖ₁ , insᵖ₁ , rb₁
    with TE.reverseTagRebaseAtᴸ (ins₂ plan) rb₁
Λ-two-insert-tag-rebase-child plan rb
    | Wᵖ₁ , insᵖ₁ , rb₁ | Wᵖ₂ , insᵖ₂ , rb₂ =
  record
    { childPlan = child ; sameΔ₂ = refl
    ; postMono = λ mono → TE.impEnvMono-insert (ins₂ plan) insᵖ₂
        (TE.impEnvMono-insert (ins₁ plan) insᵖ₁ mono)
    ; postRebase = rb₂
    }
  where
  store₀ = tagRebaseAtᴸ-target-store rb
  store₁ = tagRebaseAtᴸ-target-store rb₁
  store₂ = tagRebaseAtᴸ-target-store rb₂
  follows₁ = trans (sym store₁)
    (trans (targetFollows₁ plan)
      (cong (applyStores (bind ★ ∷ [])) store₀))
  follows₂ = trans (sym store₂)
    (trans (targetFollows₂ plan)
      (cong (applyStores (bind (＇ Fin.zero) ∷ [])) store₁))
  winᵖ₁ = rebaseTargetWindowInsert
    (targetWindow₁ (windowFacts plan))
    (λ Y → sym (tagRebaseAtᴸ-target-frozen rb₁ Y))
  winᵖ₂ = rebaseTargetWindowInsert
    (targetWindow₂ (windowFacts plan))
    (λ Y → sym (tagRebaseAtᴸ-target-frozen rb₂ Y))
  extᵖ = composeWorldExtendᴿ
    (target-insert-bind-world-extendᴿ insᵖ₁ follows₁)
    (target-insert-bind-world-extendᴿ insᵖ₂ follows₂)
  facts = record
    { targetWindow₁ = winᵖ₁ ; targetWindow₂ = winᵖ₂
    ; pivotMark = subst≡ (λ C → CTI2.impEnvʷ
          (CR.renameWorld (skip (κ₂ plan))
            (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) C ≡ I.X⊑★)
        (sym (CR.toRenameᵗ-∘ (skip (κ₂ plan))
          (CTI2.ηᴿʷ (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) Fin.zero))
        (CR.renameEnv-image (skip (κ₂ plan))
          (CTI2.impEnvʷ (CTI2.liftWorldBoth I.X⊑★ Wᵖ₁)) Fin.zero)
    ; targetStoreTransport = subst≡
        (λ Σ₁ → StoreTransport (store-lift Σ₁)
          (CTI2.targetStoreʷ Wᵖ₂)) store₁
        (subst≡ (λ Σ₂ → StoreTransport
            (store-lift (CTI2.targetStoreʷ (W₁ plan))) Σ₂)
          store₂ (targetStoreTransport (windowFacts plan)))
    ; firstTargetZeroResolves = subst≡
        (λ Σ → CTI2.resolveVar Σ Fin.zero ≡ ★)
        store₁ (firstTargetZeroResolves (windowFacts plan))
    ; targetZeroResolves = subst≡
        (λ Σ → CTI2.resolveVar Σ Fin.zero ≡ ★)
        store₂ (targetZeroResolves (windowFacts plan))
    ; targetOtherResolves = λ Z neq → subst≡
        (λ Σ₁ → CTI2.resolveVar (CTI2.targetStoreʷ Wᵖ₂) Z
          ≡ CTI2.resolveVar (store-lift Σ₁) Z) store₁
        (subst≡ (λ Σ₂ → CTI2.resolveVar Σ₂ Z
            ≡ CTI2.resolveVar
              (store-lift (CTI2.targetStoreʷ (W₁ plan))) Z)
          store₂ (targetOtherResolves (windowFacts plan) Z neq))
    ; midSourcePivotMark =
        route1-mid-source-pivot-from-windows winᵖ₁ winᵖ₂ }
  first-entry = subst≡
    (λ Σ → Σ ∋ Fin.zero ⦂ ⇑ᵗ ★) (sym follows₁) (Z∋ refl)
  support = Λ-route1-post-window-support-at facts
    (Λ-route1-mid-fresh-mono-at facts)
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just Fin.zero ] _)
      (sym follows₂) (generated-reveal-⊢↑-present z (Z∋ refl)))
    (λ z → subst≡ (λ Σ → Σ CTI2.⊢↑[ just (Fin.suc Fin.zero) ] _)
      (sym follows₂) (TE.reveal-renameˣ StoreRename-suc-bind
        (generated-reveal-⊢↑-present z first-entry)))
  child = record
    { Δ₁ = Δ₁ plan ; Δ₂ = Δ₂ plan ; W₁ = Wᵖ₁ ; W₂ = Wᵖ₂
    ; π₁ = π₁ plan ; π₂ = π₂ plan
    ; κ₁ = κ₁ plan ; κ₂ = κ₂ plan
    ; ins₁ = insᵖ₁ ; ins₂ = insᵖ₂
    ; targetFollows₁ = follows₁ ; targetFollows₂ = follows₂
    ; windowFacts = facts ; postExtend = extᵖ
    ; postGeometry = Λ-route1-post-window-at facts support
    }


Λ-post-prefix-reveal⊑²-base : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᵖ₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p₀ : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
    {p : A′ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {Xᴸ?}
    {c : Conv↑ Δᴸ A A′}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᵖ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) Wᵖ Wᵖ₂}
    {c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ Λ V′ ∶ p₀}
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.RebaseAtᴸ W Wᵖ Xᴸ?)
  → (sc : CTI2.SameCtx γ γᵖ)
  → (c⊢ : CTI2.sourceStoreʷ W CTI2.⊢↑[ Xᴸ? ] c)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → CTI2.ImpEnvMono W₂ Wᵖ₂
  → CTI2.RebaseAtᴸ W₂ Wᵖ₂ Xᴸ?
  → CTI2.SameCtx (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᵖ₂ γᵖ)
  → CTI2.sourceStoreʷ W₂ CTI2.⊢↑[ Xᴸ? ] c
  → (top-p₂ : A′ CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase prem extᵖ₂ c′ B′≢★
  → ΛPostPrefixPackageAtBase
      (CTI2.reveal⊑² mono rb sc c⊢ prem p) ext₂ c′ B′≢★
Λ-post-prefix-reveal⊑²-base mono rb sc c⊢ B′≢★ mono₂ rb₂
    sc₂ c⊢₂ top-p₂ prefix =
  record
    { prefix-p₂ = top-p₂
    ; prefix-relation =
        CTI2.reveal⊑² mono₂ rb₂ sc₂ c⊢₂
          (ΛPostPrefixPackageAtBase.prefix-relation prefix)
          top-p₂
    ; prefix-value = ΛPostPrefixPackageAtBase.prefix-value prefix
    ; prefix-reduction =
        ΛPostPrefixPackageAtBase.prefix-reduction prefix
    }


Λ-post-prefix-conceal⊑²-base : ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {Wᵖ : CTI2.World Δᴸ Δᴿ Δ}
    {W₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {Wᵖ₂ : CTI2.World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CTI2.CtxImp W} {γᵖ : CTI2.CtxImp Wᵖ}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A A′ : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p₀ : A CTI2.⊑ᵂ⟨ Wᵖ ⟩ `∀ B}
    {p : A′ CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
    {Xᴸ? Xᴿ?} {Xᴿ₂? : Maybe (Fin.Fin (suc (suc Δᴿ)))}
    {c : Conv↓ Δᴸ A A′}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {extᵖ₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) Wᵖ Wᵖ₂}
    {c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′}
    {prem : Wᵖ CTI2.∣ γᵖ ⊢² M ⊑ Λ V′ ∶ p₀}
  → (ok : CTI2.SourceConcealPartnerOK Wᵖ M c Xᴿ? (Λ V′))
  → (mono : CTI2.ImpEnvMono W Wᵖ)
  → (rb : CTI2.TagRebaseAtᴸ Wᵖ W Xᴸ? Xᴿ?)
  → (sc : CTI2.SameCtx γ γᵖ)
  → (c⊢ : CTI2.sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → CTI2.SourceConcealPartnerOK Wᵖ₂ M c Xᴿ₂?
      (Λ⊑Λ²PostTerm V′ B)
  → CTI2.ImpEnvMono W₂ Wᵖ₂
  → CTI2.TagRebaseAtᴸ Wᵖ₂ W₂ Xᴸ? Xᴿ₂?
  → CTI2.SameCtx (ECR.mapCtxᴿ ext₂ γ) (ECR.mapCtxᴿ extᵖ₂ γᵖ)
  → CTI2.sourceStoreʷ W₂ CTI2.⊢↓[ Xᴸ? ] c
  → (top-p₂ : A′ CTI2.⊑ᵂ⟨ W₂ ⟩ ΛResidualSource₂ B)
  → ΛPostPrefixPackageAtBase prem extᵖ₂ c′ B′≢★
  → ΛPostPrefixPackageAtBase
      (CTI2.conceal⊑² ok mono rb sc c⊢ prem p) ext₂ c′ B′≢★
Λ-post-prefix-conceal⊑²-base ok mono rb sc c⊢ B′≢★ ok₂ mono₂
    rb₂ sc₂ c⊢₂ top-p₂ prefix =
  record
    { prefix-p₂ = top-p₂
    ; prefix-relation =
        CTI2.conceal⊑² ok₂ mono₂ rb₂ sc₂ c⊢₂
          (ΛPostPrefixPackageAtBase.prefix-relation prefix)
          top-p₂
    ; prefix-value = ΛPostPrefixPackageAtBase.prefix-value prefix
    ; prefix-reduction =
        ΛPostPrefixPackageAtBase.prefix-reduction prefix
    }


Λ-post-prefix-hereditary : ∀ {Δᴸ Δᴿ Δ}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {γ : CTI2.CtxImp W}
    {M : CT.Term Δᴸ} {V′ : CT.Term (suc Δᴿ)}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A CTI2.⊑ᵂ⟨ W ⟩ `∀ B}
  → (plan : ΛTwoInsertPostPlan W)
  → (rel : W CTI2.∣ γ ⊢² M ⊑ Λ V′ ∶ p)
  → CT.Value M
  → CT.Value V′
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → ΛPostPrefixPackageAtBase rel (postExtend plan) c′ B′≢★
Λ-post-prefix-hereditary {W = W} {A = `∀ A} {B = B} plan
    rel@(CTI2.Λ⊑Λ² liftγ vV vV′ bodyRel q)
    (CT.Λ source-value) target-value c′
    ⦃ Bnv ⦄ ⦃ zero∈B ⦄ B′≢★ =
  Λ⊑Λ²-base-prefix-at-base rel vV vV′ c′ B′≢★
    (postExtend plan) (postGeometry plan) liftγ Anv zero∈A bodyRel
  where
  source-facts : NonVar A × Fin.zero ∈ᵗ A
  source-facts = Λ-source-body-nonvar-occurs
    {W = W} {A = A} {B = B} q
  Anv = proj₁ source-facts
  zero∈A = proj₂ source-facts
Λ-post-prefix-hereditary plan
    rel@(CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ bodyRel q)
    (CT.Λ source-value) target-value c′ B′≢★ =
  Λ⊑²-smart-recursive-prefix-at-base rel vV c′ B′≢★
    Anv zero∈A (frontPostLift front)
    (frontPostLiftCtx front liftγ) bodyRel
    (Λ-strip-prefix-p₂ plan q)
    (Λ-post-prefix-hereditary (frontChildPlan front) bodyRel
      vV target-value c′ B′≢★)
  where
  front = Λ-two-insert-front-child plan
Λ-post-prefix-hereditary plan
    rel@(CTI2.Λ⊑²-smart-comma Anv zero∈A liftW liftγ vV
      target⊢ bodyRel q)
    (CT.Λ source-value) target-value c′ B′≢★ =
  Λ⊑²-smart-recursive-prefix-at-base rel vV c′ B′≢★
    Anv zero∈A (ΛSmartChildPostPlan.postLift child)
    (ΛSmartChildPostPlan.postLiftCtx child liftγ) bodyRel
    (Λ-strip-prefix-p₂ plan q)
    (Λ-post-prefix-hereditary
      (ΛSmartChildPostPlan.childPlan child) bodyRel
      vV target-value c′ B′≢★)
  where
  child = Λ-two-insert-smart-child plan liftW
Λ-post-prefix-hereditary plan
    rel@(CTI2.cast⊑² c prem q)
    (vM 《 inert 》) target-value c′ B′≢★ =
  Λ-post-prefix-cast⊑²-base c B′≢★
    (Λ-strip-prefix-p₂ plan q)
    (Λ-post-prefix-hereditary plan prem vM target-value c′ B′≢★)
Λ-post-prefix-hereditary plan
    rel@(CTI2.reveal⊑² mono rb sc c⊢ prem q)
    (vM ↑ reveal-value) target-value c′ B′≢★
    with Λ-two-insert-rebase-child plan rb
Λ-post-prefix-hereditary plan
    rel@(CTI2.reveal⊑² mono rb sc c⊢ prem q)
    (vM ↑ reveal-value) target-value c′ B′≢★
    | record
        { childPlan = child ; sameΔ₂ = refl
        ; postMono = post-mono ; postRebase = post-rb } =
  Λ-post-prefix-reveal⊑²-base mono rb sc c⊢ B′≢★
    (post-mono mono) post-rb
    (mapCtxᴿ-sameCtx (postExtend plan) (postExtend child) sc)
    (TE.source-reveal-insert (ins₂ plan)
      (TE.source-reveal-insert (ins₁ plan) c⊢))
    (Λ-strip-prefix-p₂ plan q)
    (Λ-post-prefix-hereditary child prem vM target-value c′ B′≢★)
Λ-post-prefix-hereditary plan
    rel@(CTI2.conceal⊑² ok mono rb sc c⊢ prem q)
    (vM ↓ conceal-value) target-value c′ B′≢★
    with Λ-two-insert-tag-rebase-child plan rb
Λ-post-prefix-hereditary plan
    rel@(CTI2.conceal⊑² ok mono rb sc c⊢ prem q)
    (vM ↓ conceal-value) target-value c′ B′≢★
    | record
        { childPlan = child ; sameΔ₂ = refl
        ; postMono = post-mono ; postRebase = post-rb } =
  Λ-post-prefix-conceal⊑²-base ok mono rb sc c⊢ B′≢★
    post-source-conceal-partner-ok (post-mono mono) post-rb
    (mapCtxᴿ-sameCtx (postExtend plan) (postExtend child) sc)
    (TE.source-conceal-insert (ins₂ plan)
      (TE.source-conceal-insert (ins₁ plan) c⊢))
    (Λ-strip-prefix-p₂ plan q)
    (Λ-post-prefix-hereditary child prem vM target-value c′ B′≢★)
