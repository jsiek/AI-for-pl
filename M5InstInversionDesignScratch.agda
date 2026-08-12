module M5InstInversionDesignScratch where

-- File Charter:
--   * Root-level scratch for the M5 target-instantiation inversion design.
--   * Imports the promoted live package records from `InstInversionDef`.
--   * Checks that such packages project mechanically to the live
--     `InstRelContinuationSurface`, without adding live proof code.

open import proof.DGG.Catchup.InstCatchupRightRelDef using
  (InstRelContinuationSurface)
open import proof.DGG.Catchup.InstInversionDef using
  (InstInversionPackage; InstPostCatalogPackage;
   InstPostCatalogPackageAt; Λ⊑Λ²PostBodyTransportᵀ;
   Λ⊑Λ²PostTerm; Λ⊑Λ²TargetSplit₂; Λ⊑²AtRewrapᵀ;
   Λ⊑²CPSRewrapᵀ; MapCtxᴿLiftᴸᵀ; RightBindUnderLeftLiftᵀ)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Types
open import Consistency using
  (Env∼; _⊢_∼_; instᵐ; inst_; keep; skip; toRenameᵗ; wk↪ᵗ)
open import CastTerms using
  (Term; Value; ⟨_,_,_⟩; _⊢_⦂_; _⟨_⟩; Λ_; renameᵗᵐ)
import Imprecision as I
open import Imprecision using (VarImp; X⊑★; X⊑X)
open import Reduction using (StoreChanges; _—↠[_]_; bind; _∷_; [])
open import TyStore using (store-lift; store-bind)
open import proof.DGG.Catchup.ValueCatchupRightDef using (castSize)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.TargetExtend as TE
import proof.DGG.TermImpDecay as TD
import proof.DGG.WorldDecay as WD
open CTI2 using (World; CtxImp; LiftCtx; LiftCtxᴸ; liftWorldBoth;
  liftWorldLeft; rightOnlyWorld; targetStoreʷ; tgtCtxʷ;
  _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


inst-post-at→package : ∀ {fuel Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
    {W : World Δᴸ Δᴿ Δ} {W₂ : World Δᴸ Δᴿ₂ Δ₂}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    {χs₂ : StoreChanges Δᴿ Δᴿ₂}
  → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
  → (vM : Value M)
  → (vM′ : Value M′)
  → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
  → ⦃ Bnv : NonVar B ⦄
  → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
  → (B′≢★ : B′ ≢ ★)
  → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
  → (q : A ⊑ᵂ⟨ W ⟩ B′)
  → (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂)
  → (Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
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


ΛLiftToBindFreshWorld : ∀ {Δᴸ Δᴿ Δ}
  → VarImp
  → World Δᴸ Δᴿ Δ
  → World (suc Δᴸ) (suc (suc Δᴿ)) (suc (suc (suc Δ)))
ΛLiftToBindFreshWorld v W =
  CTI2.world
    (skip (keep (skip (CTI2.ηᴸʷ W))))
    (skip (keep (keep (CTI2.ηᴿʷ W))))
    (I.instᵐ (I.extendᵐ v (I.instᵐ (CTI2.impEnvʷ W))))
    (store-lift (CTI2.sourceStoreʷ W))
    (store-bind (store-bind (CTI2.targetStoreʷ W) ★) (＇ Fin.zero))


ΛLiftToBindFreshTransportᵀ : Set
ΛLiftToBindFreshTransportᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {v : VarImp}
    {γ : CtxImp (liftWorldBoth v (rightOnlyWorld W ★))}
    {M : Term (suc Δᴸ)} {M′ : Term (suc (suc Δᴿ))}
    {A : Ty (suc Δᴸ)} {B : Ty (suc (suc Δᴿ))}
    {p : A ⊑ᵂ⟨ liftWorldBoth v (rightOnlyWorld W ★) ⟩ B}
  → liftWorldBoth v (rightOnlyWorld W ★) ∣ γ ⊢² M ⊑ M′ ∶ p
  → Σ[ γᵇ ∈ CtxImp (ΛLiftToBindFreshWorld v W) ]
    Σ[ pᵇ ∈ A ⊑ᵂ⟨ ΛLiftToBindFreshWorld v W ⟩ B ]
      ΛLiftToBindFreshWorld v W ∣ γᵇ ⊢² M ⊑ M′ ∶ pᵇ


ΛLiftToBindFreshDecay :
  ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → WD.EnvDecay
      (ΛLiftToBindFreshWorld X⊑X W)
      (ΛLiftToBindFreshWorld X⊑★ W)
ΛLiftToBindFreshDecay = WD.env-decay refl refl refl refl mono
  where
  mono : ∀ {Δ} {μ : I.ImpEnv Δ}
    → (Z : Fin.Fin (suc (suc (suc Δ))))
    → I.instᵐ (I.extendᵐ X⊑X (I.instᵐ μ)) Z ≡ X⊑★
    → I.instᵐ (I.extendᵐ X⊑★ (I.instᵐ μ)) Z ≡ X⊑★
  mono Fin.zero eq = refl
  mono (Fin.suc Fin.zero) ()
  mono (Fin.suc (Fin.suc Fin.zero)) eq = refl
  mono (Fin.suc (Fin.suc (Fin.suc Z))) eq = eq


Λ⊑Λ²-first-insert-decay-lift-to-bind-preflight :
  ΛLiftToBindFreshTransportᵀ
  → ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γᴮ : CtxImp (liftWorldBoth X⊑X W)}
    {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
  → liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ γᵈ ∈ CtxImp (ΛLiftToBindFreshWorld X⊑★ W) ]
    Σ[ Bᵈ ∈ Ty (suc (suc Δᴿ)) ]
    Σ[ postᵈ ∈ Term (suc (suc Δᴿ)) ]
    Σ[ pᵈ ∈ A ⊑ᵂ⟨ ΛLiftToBindFreshWorld X⊑★ W ⟩ Bᵈ ]
      ΛLiftToBindFreshWorld X⊑★ W ∣ γᵈ ⊢² V ⊑ postᵈ ∶ pᵈ
Λ⊑Λ²-first-insert-decay-lift-to-bind-preflight
    convert {W = W} {V′ = V′} {B = B} bodyRel
    with convert
      {M′ = renameᵗᵐ (keep wk↪ᵗ) V′}
      {B = renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B}
      (TD.⊢²-decay
        {W = liftWorldBoth X⊑X (rightOnlyWorld W ★)}
        {Wᵈ = liftWorldBoth X⊑★ (rightOnlyWorld W ★)}
        TD.liftBothBinderDecay
        (TE.⊢²-target-insert
          (TE.keepRightBindTargetInsert {B = ★} {v = X⊑X})
          bodyRel))
Λ⊑Λ²-first-insert-decay-lift-to-bind-preflight
    convert {W = W} {V′ = V′} {B = B} bodyRel
  | γᵇ , pᵇ , relᵇ =
  γᵇ ,
  renameᵗ (toRenameᵗ (keep wk↪ᵗ)) B ,
  renameᵗᵐ (keep wk↪ᵗ) V′ ,
  pᵇ ,
  relᵇ


ΛPostRevealRebuildᵀ : Set
ΛPostRevealRebuildᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {γᵈ : CtxImp (ΛLiftToBindFreshWorld X⊑★ W)}
    {V : Term (suc Δᴸ)}
    {prePost : Term (suc (suc Δᴿ))}
    {A : Ty (suc Δᴸ)} {Bᵈ : Ty (suc (suc Δᴿ))}
    {pre-p : A ⊑ᵂ⟨ ΛLiftToBindFreshWorld X⊑★ W ⟩ Bᵈ}
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)))
  → ΛLiftToBindFreshWorld X⊑★ W ∣ γᵈ
      ⊢² V ⊑ prePost ∶ pre-p
  → Σ[ γ₂ᴸ ∈ CtxImp (liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero))) ]
    Σ[ B₂ ∈ Ty (suc (suc Δᴿ)) ]
    Σ[ post ∈ Term (suc (suc Δᴿ)) ]
    Σ[ body-p₂ ∈ A ⊑ᵂ⟨ liftWorldLeft X⊑★
        (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ⟩ B₂ ]
    Σ[ top-p₂ ∈ `∀ A ⊑ᵂ⟨
        rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero) ⟩ B₂ ]
      LiftCtxᴸ X⊑★ (ECR.mapCtxᴿ ext₂ γ) γ₂ᴸ
      × Value post
      × ⟨ suc (suc Δᴿ) ,
          targetStoreʷ
            (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ,
          tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩ ⊢ post ⦂ B₂
      × liftWorldLeft X⊑★
          (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero))
          ∣ γ₂ᴸ ⊢² V ⊑ post ∶ body-p₂


Λ⊑Λ²-base-rewrap-preflight :
  Λ⊑Λ²PostBodyTransportᵀ
  → ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {γᴮ : CtxImp (liftWorldBoth X⊑X W)}
    {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
    {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
    {body-p : A ⊑ᵂ⟨ liftWorldBoth X⊑X W ⟩ B}
  → (ext₂ : ECR.WorldExtendᴿ
      (bind ★ ∷ bind (＇ Fin.zero) ∷ [])
      W (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)))
  → (Anv : NonVar A)
  → (zero∈A : Fin.zero ∈ᵗ A)
  → (liftγ : LiftCtx X⊑X γ γᴮ)
  → (vV : Value V)
  → (vV′ : Value V′)
  → liftWorldBoth X⊑X W ∣ γᴮ ⊢² V ⊑ V′ ∶ body-p
  → Σ[ B₂ ∈ Ty (suc (suc Δᴿ)) ]
    Σ[ post ∈ Term (suc (suc Δᴿ)) ]
    Σ[ p₂ ∈ `∀ A ⊑ᵂ⟨
      rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero) ⟩ B₂ ]
      Value post
      × ⟨ suc (suc Δᴿ) ,
          targetStoreʷ
            (rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)) ,
          tgtCtxʷ (ECR.mapCtxᴿ ext₂ γ) ⟩ ⊢ post ⦂ B₂
      × rightOnlyWorld (rightOnlyWorld W ★) (＇ Fin.zero)
          ∣ ECR.mapCtxᴿ ext₂ γ ⊢² Λ V ⊑ post ∶ p₂
Λ⊑Λ²-base-rewrap-preflight transport {V′ = V′} {B = B}
    ext₂ Anv zero∈A liftγ vV
    vV′ bodyRel
    with transport ext₂ Anv zero∈A liftγ vV vV′ bodyRel
Λ⊑Λ²-base-rewrap-preflight transport {V′ = V′} {B = B}
    ext₂ Anv zero∈A liftγ vV
    vV′ bodyRel
  | γ₂ᴸ , body-p₂ , top-p₂ , liftγ₂ , vPost , post⊢ , bodyRel₂ =
  substᵗ Λ⊑Λ²TargetSplit₂ B , Λ⊑Λ²PostTerm V′ B , top-p₂ ,
  vPost , post⊢ ,
  CTI2.Λ⊑² Anv zero∈A liftγ₂ vV post⊢ bodyRel₂ top-p₂


record RecursiveΛInversionPreflight (fuel : ℕ) : Set₁ where
  field
    derivation-recursive-Λ-at : ∀ {Δᴸ Δᴿ Δ Δᴿ₂ Δ₂}
        {W : World Δᴸ Δᴿ Δ} {W₂ : World Δᴸ Δᴿ₂ Δ₂}
        {γ : CtxImp W}
        {M : Term Δᴸ} {V′ : Term (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
        {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {χs₂ : StoreChanges Δᴿ Δᴿ₂}
      → (rel : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value (Λ V′))
      → Value V′
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → (ext₂ : ECR.WorldExtendᴿ χs₂ W W₂)
      → InstPostCatalogPackageAt fuel rel vM vM′ c′ B′≢★
          c<fuel q χs₂ W₂ ext₂

    derivation-recursive-Λ : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {M : Term Δᴸ} {V′ : Term (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
        {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
      → (rel : W ∣ γ ⊢² M ⊑ Λ V′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value (Λ V′))
      → Value V′
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    Λ⊑²-rewrap : ∀ {Δᴸ Δᴿ Δ}
        {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
        {γᴸ : CtxImp (liftWorldLeft X⊑★ W)}
        {V : Term (suc Δᴸ)} {V′ : Term (suc Δᴿ)}
        {A : Ty (suc Δᴸ)} {B : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {body-p : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ `∀ B}
        {p : `∀ A ⊑ᵂ⟨ W ⟩ `∀ B}
      → (Anv : NonVar A)
      → (zero∈A : Fin.zero ∈ᵗ A)
      → (liftγ : LiftCtxᴸ X⊑★ γ γᴸ)
      → (vV : Value V)
      → (vΛV : Value (Λ V))
      → (vΛV′ : Value (Λ V′))
      → (target⊢ :
          ⟨ Δᴿ , targetStoreʷ W , tgtCtxʷ γ ⟩
            ⊢ (Λ V′) ⦂ `∀ B)
      → (rel : liftWorldLeft X⊑★ W ∣ γᴸ ⊢² V ⊑ Λ V′ ∶
          body-p)
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (body-q : A ⊑ᵂ⟨ liftWorldLeft X⊑★ W ⟩ B′)
      → (q : `∀ A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vV vΛV′ c′ B′≢★
          c<fuel body-q
      → InstPostCatalogPackage fuel
          (CTI2.Λ⊑² Anv zero∈A liftγ vV
            target⊢ rel p)
          vΛV vΛV′ c′ B′≢★ c<fuel q


record LeftLiftRightBindPreflight : Set₁ where
  field
    right-bind-under-left-lift : RightBindUnderLeftLiftᵀ
    mapCtxᴿ-liftᴸ : MapCtxᴿLiftᴸᵀ right-bind-under-left-lift


Λ⊑²-cps-rewrap-preflight :
  (right-bind-under-left-lift : RightBindUnderLeftLiftᵀ)
  → (mapCtxᴿ-liftᴸ : MapCtxᴿLiftᴸᵀ right-bind-under-left-lift)
  → Λ⊑²CPSRewrapᵀ right-bind-under-left-lift mapCtxᴿ-liftᴸ
Λ⊑²-cps-rewrap-preflight right-bind-under-left-lift mapCtxᴿ-liftᴸ
    {p₂ = p₂} ext Anv zero∈A liftγ vV target⊢ bodyRel =
  CTI2.Λ⊑² Anv zero∈A (mapCtxᴿ-liftᴸ ext liftγ) vV
    target⊢ bodyRel p₂


Λ⊑²-at-rewrap-preflight : Λ⊑²AtRewrapᵀ
Λ⊑²-at-rewrap-preflight {p₂ = p₂} Anv zero∈A liftγ vV
    target⊢ bodyRel =
  CTI2.Λ⊑² Anv zero∈A liftγ vV target⊢ bodyRel p₂


inst-inversion→rel-surface : ∀ {fuel}
  → InstInversionPackage fuel
  → InstRelContinuationSurface fuel
inst-inversion→rel-surface pkg = record
  { fuel-step = InstInversionPackage.fuel-step pkg
  ; inst-prefix = InstInversionPackage.inst-prefix pkg
  ; all-value-step-catalog =
      InstInversionPackage.all-value-step-catalog pkg
  ; inst-alloc-decrease = InstInversionPackage.inst-alloc-decrease pkg
  ; catchup⁻-embed = InstInversionPackage.catchup⁻-embed pkg
  ; Λ-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.Λ-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; ∀-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.∀-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; gen-cont = λ rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★
      c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.gen-package pkg
          rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★ c<fuel q)
  ; reveal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.reveal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; conceal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.conceal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  }
