module proof.DGG.Catchup.InstInversionDef where

-- File Charter:
--   * States the M5 target-instantiation inversion package surfaces.
--   * Packages the post-catalog relation, residual provenance, and
--     target-spine descent output needed by the right-instantiation
--     relational continuations.
--   * States the fuel-free structural value-instantiation descent surface.
--   * Contains no proof scripts and depends only on core syntax/reduction,
--     the catch-up Def surfaces, and the stage-1 DGG world-extension
--     interface.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import Imprecision using (X⊑★; X⊑X)
open import Consistency using
  (Env∼; _⊢_∼_; ∀ᶜ_; inst_; gen_; extᵐ; instᵐ; genᵐ;
   ↑ᶜ_; close-instᶜ; keep; toRenameᵗ; wk↪ᵗ)
open import Conversion using
  (Conv↑; Conv↓; `∀↑_; `∀↓_; 〖_,_↑_〗; rename↑)
open import CastTerms using
  (Term; Value; GenSafe; ⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; _↑_;
   _↓_; Λ_; _⦂∀_[_]; renameᵗᵐ)
open import Reduction using
  (StoreChanges; _—↠[_]_; applyTys; applyBody; bind; _∷_; [])

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.InstCatchupRightDef using
  (InstCastAllocPrefixᵀ; AllValueViewStepCatalogᵀ)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (CatchupCast⁻; Catchup⁻Embedᵀ; FuelStepSurface;
   inst-alloc-decreaseᵀ; castSize)
open import proof.DGG.Catchup.StructuralValueInstantiationStateDef using
  (name-type-app-frame; _▻ⁱ_; []ⁱ)
open import proof.DGG.Catchup.StructuralTargetInstantiationDef using
  (StructuralTargetInstantiationPackage)
open import proof.DGG.Catchup.StructuralInstantiationDescentDef using
  (StructuralNamePostPlan; StructuralNameChainPlan)
open import proof.DGG.Catchup.StructuralStrictViewSurfaceDef using
  (StructuralStrictViewSurfaces; StructuralNameInstantiationᵀ)
open import proof.DGG.Inversion.SpineValueDef using (AllValueView)
open CTI2 using
  (World; CtxImp; LiftCtx; LiftCtxᴸ; liftWorldBoth;
   liftWorldLeft; rightOnlyWorld; targetStoreʷ; tgtCtxʷ;
   _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


Λ⊑Λ²TargetSplit₂ : ∀ {Δ}
  → TyVar (suc Δ)
  → Ty (suc (suc Δ))
Λ⊑Λ²TargetSplit₂ Fin.zero = ★
Λ⊑Λ²TargetSplit₂ (Fin.suc X) = ＇ (Fin.suc (Fin.suc X))


Λ⊑Λ²BodyAfter★ : ∀ {Δ} → Ty (suc Δ) → Ty (suc (suc Δ))
Λ⊑Λ²BodyAfter★ B = applyBody (bind ★) B


Λ⊑Λ²PostTerm : ∀ {Δ}
  → Term (suc Δ)
  → Ty (suc Δ)
  → Term (suc (suc Δ))
Λ⊑Λ²PostTerm V′ B =
  (renameᵗᵐ (keep wk↪ᵗ) V′ ↑
    〖 Fin.zero , ⇑ᵗ (＇ Fin.zero) ↑ Λ⊑Λ²BodyAfter★ B 〗)
  ↑ rename↑ Fin.suc (〖 Fin.zero , ★ ↑ B 〗)


RightBindUnderLeftLiftᵀ : Set
RightBindUnderLeftLiftᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
  → ECR.WorldExtendᴿ (bind B ∷ [])
      (liftWorldLeft X⊑★ W)
      (liftWorldLeft X⊑★ (rightOnlyWorld W B))


MapCtxᴿLiftᴸᵀ : RightBindUnderLeftLiftᵀ → Set
MapCtxᴿLiftᴸᵀ right-bind-under-left-lift =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {B : Ty Δᴿ}
    {γ : CtxImp W} {γᴸ : CtxImp (liftWorldLeft X⊑★ W)}
  → (ext : ECR.WorldExtendᴿ (bind B ∷ []) W
      (rightOnlyWorld W B))
  → LiftCtxᴸ X⊑★ γ γᴸ
  → LiftCtxᴸ X⊑★
      (ECR.mapCtxᴿ ext γ)
      (ECR.mapCtxᴿ right-bind-under-left-lift γᴸ)


Λ⊑²CPSRewrapᵀ :
  (right-bind-under-left-lift : RightBindUnderLeftLiftᵀ)
  → MapCtxᴿLiftᴸᵀ right-bind-under-left-lift
  → Set
Λ⊑²CPSRewrapᵀ right-bind-under-left-lift mapCtxᴿ-liftᴸ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γᴸ : CtxImp (liftWorldLeft X⊑★ W)}
    {V : Term (suc Δᴸ)} {post : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {Balloc : Ty Δᴿ} {C : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldLeft X⊑★
      (rightOnlyWorld W Balloc) ⟩ C}
    {p₂ : `∀ A ⊑ᵂ⟨ rightOnlyWorld W Balloc ⟩ C}
  → (ext : ECR.WorldExtendᴿ (bind Balloc ∷ []) W
      (rightOnlyWorld W Balloc))
  → NonVar A
  → Fin.zero ∈ᵗ A
  → (liftγ : LiftCtxᴸ X⊑★ γ γᴸ)
  → (vV : Value V)
  → ⟨ suc Δᴿ , targetStoreʷ (rightOnlyWorld W Balloc) ,
      tgtCtxʷ (ECR.mapCtxᴿ ext γ) ⟩ ⊢ post ⦂ C
  → liftWorldLeft X⊑★ (rightOnlyWorld W Balloc)
      ∣ ECR.mapCtxᴿ right-bind-under-left-lift γᴸ
      ⊢² V ⊑ post ∶ body-p
  → rightOnlyWorld W Balloc
      ∣ ECR.mapCtxᴿ ext γ
      ⊢² Λ V ⊑ post ∶ p₂


Λ⊑²AtRewrapᵀ : Set
Λ⊑²AtRewrapᵀ =
  ∀ {Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : World Δᴸ Δᴿ Δ} {W₂ : World Δᴸ Δᴿ₂ Δ₂}
    {γ : CtxImp W} {γᴸ : CtxImp (liftWorldLeft X⊑★ W)}
    {V : Term (suc Δᴸ)} {post : Term Δᴿ₂}
    {A : Ty (suc Δᴸ)} {B : Ty Δᴿ₂}
    {body-p : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩ B}
    {p₂ : `∀ A ⊑ᵂ⟨ W₂ ⟩ B}
    {χs₂ : StoreChanges Δᴿ Δᴿ₂}
    {ext₂ : ECR.WorldExtendᴿ χs₂ W W₂}
    {extᴸ₂ : ECR.WorldExtendᴿ χs₂
      (liftWorldLeft X⊑★ W) (liftWorldLeft X⊑★ W₂)}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ (ECR.mapCtxᴿ ext₂ γ)
      (ECR.mapCtxᴿ extᴸ₂ γᴸ)
  → Value V
  → ⟨ Δᴿ₂ , targetStoreʷ W₂ , tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
      ⊢ post ⦂ B
  → liftWorldLeft X⊑★ W₂ ∣ ECR.mapCtxᴿ extᴸ₂ γᴸ
      ⊢² V ⊑ post ∶ body-p
  → W₂ ∣ ECR.mapCtxᴿ ext₂ γ ⊢² Λ V ⊑ post ∶ p₂


Λ⊑Λ²PostBodyTransportᵀ : Set
Λ⊑Λ²PostBodyTransportᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {γᴮ : CtxImp (liftWorldBoth X⊑X W)}
    {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)))
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtx X⊑X γ γᴮ
  → Value V
  → Value V′
  → liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γ₂ᴸ ∈ CtxImp (liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero))) ]
    Σ[ body-p₂ ∈ A ⊑ᵂ⟨ liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
    Σ[ top-p₂ ∈ `∀ A ⊑ᵂ⟨
        rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero) ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
      LiftCtxᴸ X⊑★ (ECR.mapCtxᴿ ext₂ γ) γ₂ᴸ
      × Value (Λ⊑Λ²PostTerm V′ B)
      × ⟨ suc (suc Δᴿ) ,
          targetStoreʷ
            (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ,
          tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
          ⊢ Λ⊑Λ²PostTerm V′ B ⦂
          substᵗ Λ⊑Λ²TargetSplit₂ B
      × liftWorldLeft X⊑★
          (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero))
          ∣ γ₂ᴸ ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂


Λ⊑Λ²PostBodyTransportAtᵀ : Set
Λ⊑Λ²PostBodyTransportAtᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : World Δᴸ Δᴿ Δ}
    {W₂ : World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {γ : CtxImp W}
    {γᴮ : CtxImp (liftWorldBoth X⊑X W)}
    {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂)
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtx X⊑X γ γᴮ
  → Value V
  → Value V′
  → liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γ₂ᴸ ∈ CtxImp (liftWorldLeft X⊑★ W₂) ]
    Σ[ body-p₂ ∈ A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
    Σ[ top-p₂ ∈ `∀ A ⊑ᵂ⟨ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
      LiftCtxᴸ X⊑★ (ECR.mapCtxᴿ ext₂ γ) γ₂ᴸ
      × Value (Λ⊑Λ²PostTerm V′ B)
      × ⟨ suc (suc Δᴿ) , targetStoreʷ W₂ ,
          tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
          ⊢ Λ⊑Λ²PostTerm V′ B ⦂
          substᵗ Λ⊑Λ²TargetSplit₂ B
      × liftWorldLeft X⊑★ W₂ ∣ γ₂ᴸ
          ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂


data Λ⊑Λ²LeftTower : ∀ {Δᴸ Δᴿ Δ Δ₂}
    (W : World Δᴸ Δᴿ Δ)
    (W₂ : World Δᴸ (suc (suc Δᴿ)) Δ₂)
    (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂)
  → Set₁ where
  left-tower-zero : ∀ {Δᴸ Δᴿ Δ}
      {W : World Δᴸ Δᴿ Δ}
    → (ext₂ : ECR.WorldExtendᴿ
        (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
        W (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)))
    → Λ⊑Λ²LeftTower W
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ext₂

  left-tower-suc : ∀ {Δᴸ Δᴿ Δ Δ₂}
      {W : World Δᴸ Δᴿ Δ}
      {W₂ : World Δᴸ (suc (suc Δᴿ)) Δ₂}
      {ext₂ : ECR.WorldExtendᴿ
        (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    → Λ⊑Λ²LeftTower W W₂ ext₂
    → (extᴸ₂ : ECR.WorldExtendᴿ
        (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
        (liftWorldLeft X⊑★ W) (liftWorldLeft X⊑★ W₂))
    → Λ⊑Λ²LeftTower (liftWorldLeft X⊑★ W)
        (liftWorldLeft X⊑★ W₂) extᴸ₂


Λ⊑Λ²PostBodyTransportᴸᵀ : Set₁
Λ⊑Λ²PostBodyTransportᴸᵀ =
  ∀ {Δᴸ Δᴿ Δ Δ₂}
    {W : World Δᴸ Δᴿ Δ}
    {W₂ : World Δᴸ (suc (suc Δᴿ)) Δ₂}
    {ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ []) W W₂}
    {γ : CtxImp W}
    {γᴮ : CtxImp (liftWorldBoth X⊑X W)}
    {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
  → Λ⊑Λ²LeftTower W W₂ ext₂
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtx X⊑X γ γᴮ
  → Value V
  → Value V′
  → liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γ₂ᴸ ∈ CtxImp (liftWorldLeft X⊑★ W₂) ]
    Σ[ body-p₂ ∈ A ⊑ᵂ⟨ liftWorldLeft X⊑★ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
    Σ[ top-p₂ ∈ `∀ A ⊑ᵂ⟨ W₂ ⟩
        substᵗ Λ⊑Λ²TargetSplit₂ B ]
      LiftCtxᴸ X⊑★ (ECR.mapCtxᴿ ext₂ γ) γ₂ᴸ
      × Value (Λ⊑Λ²PostTerm V′ B)
      × ⟨ suc (suc Δᴿ) , targetStoreʷ W₂ ,
          tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩
          ⊢ Λ⊑Λ²PostTerm V′ B ⦂
          substᵗ Λ⊑Λ²TargetSplit₂ B
      × liftWorldLeft X⊑★ W₂ ∣ γ₂ᴸ
          ⊢² V ⊑ Λ⊑Λ²PostTerm V′ B ∶ body-p₂


Catchup⁻NonStarᵀ : Set
Catchup⁻NonStarᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B} {q : A ⊑ᵂ⟨ W ⟩ B′}
  → NonStar B
  → NonStar B′
  → (c : ν ⊢ B ∼ B′)
  → CatchupCast⁻ {W = W} {A = A} p c q


InstResidualProvenanceᵀ : Set
InstResidualProvenanceᵀ =
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ (suc Δᴿ) Δ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ renameᵗ (toRenameᵗ wk↪ᵗ) (B [ ★ ]ᵗ)}
    {q : A ⊑ᵂ⟨ W ⟩ renameᵗ (toRenameᵗ wk↪ᵗ) B′}
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → CatchupCast⁻ {W = W} {A = A} p
      (↑ᶜ (close-instᶜ c′)) q


record InstSpineDescentPackage {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γ : CtxImp W)
    (M : Term Δᴸ)
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    (post : Term Δᴿ)
    (p : A ⊑ᵂ⟨ W ⟩ B) : Set₁ where
  field
    Δᴿ′ : TyCtx
    χs : StoreChanges Δᴿ Δᴿ′
    Δ′ : TyCtx
    W′ : World Δᴸ Δᴿ′ Δ′
    ext : ECR.WorldExtendᴿ χs W W′
    final : Term Δᴿ′
    final-value : Value final
    post-reduction : post —↠[ χs ] final
    final-relation :
      W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ final ∶
        ECR.transport⊑ᵂ ext p


-- Stage-2 root callers own the catalog geometry: they supply the assembled
-- name-instantiation worker, hereditary source/chain plans, and the completed
-- root target package instead of relying on a target-only normalizer.
StructuralValueInstantiationᵀ : Set₁
StructuralValueInstantiationᵀ =
  ∀ {fuel Δᴸ Δᴿ Δ} {W : World Δᴸ (suc Δᴿ) Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {V : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {R : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ `∀ (applyBody (bind R) B)}
    {q : A ⊑ᵂ⟨ W ⟩
      applyBody (bind R) B [ ＇ Fin.zero ]ᵗ}
  → StructuralStrictViewSurfaces
  → StructuralNameInstantiationᵀ
  → FuelStepSurface fuel
  → Catchup⁻Embedᵀ
  → inst-alloc-decreaseᵀ
  → (plan : StructuralNamePostPlan W A
      (applyBody (bind R) B [ ＇ Fin.zero ]ᵗ) q)
  → StructuralNameChainPlan {fuel = fuel} W γ A
      (applyBody (bind R) B [ ＇ Fin.zero ]ᵗ) q plan
  → W ∣ γ ⊢² M ⊑ renameᵗᵐ wk↪ᵗ V ∶ p
  → Value M
  → Value V
  → AllValueView V
  → StructuralTargetInstantiationPackage W (renameᵗᵐ wk↪ᵗ V)
      (name-type-app-frame (applyBody (bind R) B) Fin.zero
        refl refl ▻ⁱ []ⁱ)
  → InstSpineDescentPackage W γ M
      (renameᵗᵐ wk↪ᵗ V ⦂∀ applyBody (bind R) B [ ＇ Fin.zero ]) q


record InstPostCatalogPackageAt (fuel : ℕ)
    {Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
    (vM : Value M)
    (vM′ : Value M′)
    (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    (B′≢★ : B′ ≢ ★)
    (c<fuel : castSize ((inst c′) B′≢★) < fuel)
    (q : A ⊑ᵂ⟨ W ⟩ B′)
    (χs₂ : StoreChanges Δᴿ Δᴿ₂)
    (W₂ : World Δᴸ Δᴿ₂ Δ₂)
    (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂) : Set₁ where
  field
    at-B₂ : Ty Δᴿ₂
    at-post : Term Δᴿ₂
    at-p₂ : A ⊑ᵂ⟨ W₂ ⟩ at-B₂
    at-ν₂ : Env∼ Δᴿ₂
    at-residual-target : Ty Δᴿ₂
    at-residual-q : A ⊑ᵂ⟨ W₂ ⟩ at-residual-target
    at-residual-target-eq : at-residual-target ≡ applyTys χs₂ B′
    at-residual-cast : at-ν₂ ⊢ at-B₂ ∼ at-residual-target
    at-residual-provenance :
      CatchupCast⁻ {W = W₂} {A = A} at-p₂ at-residual-cast
        at-residual-q
    at-residual-fuel :
      suc (castSize at-residual-cast) < fuel
    at-prefix-reduction :
      M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs₂ ]
        at-post ⟨ at-residual-cast ⟩
    at-spine-descent :
      InstSpineDescentPackage W₂ (ECR.mapCtxᴿ ext₂ γ) M
        at-post at-p₂


record InstPostCatalogPackage (fuel : ℕ)
    {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
    (vM : Value M)
    (vM′ : Value M′)
    (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    (B′≢★ : B′ ≢ ★)
    (c<fuel : castSize ((inst c′) B′≢★) < fuel)
    (q : A ⊑ᵂ⟨ W ⟩ B′) : Set₁ where
  field
    Δᴿ₂ : TyCtx
    χs₂ : StoreChanges Δᴿ Δᴿ₂
    Δ₂ : TyCtx
    W₂ : World Δᴸ Δᴿ₂ Δ₂
    ext₂ : ECR.WorldExtendᴿ χs₂ W W₂
    B₂ : Ty Δᴿ₂
    post : Term Δᴿ₂
    p₂ : A ⊑ᵂ⟨ W₂ ⟩ B₂
    ν₂ : Env∼ Δᴿ₂
    residual-target : Ty Δᴿ₂
    residual-q : A ⊑ᵂ⟨ W₂ ⟩ residual-target
    residual-target-eq : residual-target ≡ applyTys χs₂ B′
    residual-cast : ν₂ ⊢ B₂ ∼ residual-target
    residual-provenance :
      CatchupCast⁻ {W = W₂} {A = A} p₂ residual-cast
        residual-q
    spine-descent :
      InstSpineDescentPackage W₂ (ECR.mapCtxᴿ ext₂ γ) M post p₂
    finish :
      Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              ECR.transport⊑ᵂ ext q))


record InstInversionPackage (fuel : ℕ) : Set₁ where
  field
    fuel-step : FuelStepSurface fuel
    inst-prefix : InstCastAllocPrefixᵀ
    all-value-step-catalog : AllValueViewStepCatalogᵀ
    inst-alloc-decrease : inst-alloc-decreaseᵀ
    catchup⁻-embed : Catchup⁻Embedᵀ

    Λ-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {V′ : Term (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
        {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ Λ V′
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    ∀-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : extᵐ ν₀ ⊢ B₀ ∼ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ⟨ ∀ᶜ d ⟩
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    gen-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B C : Ty (suc Δᴿ)}
        {B₀ B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : genᵐ ν₀ ⊢ ⇑ᵗ B₀ ∼ C}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → ⦃ Cnv : NonVar C ⦄
      → ⦃ zero∈C : Fin.zero ∈ᵗ C ⦄
      → (B₀≢★ : B₀ ≢ ★)
      → GenSafe d
      → M′ ≡ V′ ⟨ (gen d) B₀≢★ ⟩
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    reveal-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↑ (suc Δᴿ) B₀ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ↑ `∀↑ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    conceal-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↓ (suc Δᴿ) B₀ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ↓ `∀↓ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q
