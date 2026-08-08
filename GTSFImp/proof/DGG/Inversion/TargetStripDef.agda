module proof.DGG.Inversion.TargetStripDef where

-- File Charter:
--   * States the target-tag-at-star strip members used by the source-strip
--     core rebuild proof.
--   * Packages the terminal target-star premise for plain and left-lifted
--     source terms.
--   * Contains no proof scripts and keeps the statements frozen against
--     `BodyStripCheck`.

open import Data.Nat using (suc)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _↓_; _⟨_⟩; _⊢_⦂_; ⟨_,_,_⟩)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; CtxImp; LiftCtxᴸ; RebaseAt; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; targetStoreʷ; tgtCtxʷ)

record TargetStripAt★Data {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ) : Set where
  constructor target-strip★-data
  field
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y★
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : A ⊑ᵂ⟨ W★ ⟩ ★
    premise★ : W★ ∣ γ★ ⊢² V ⊑ U ∶ q★

record TargetStripAt★ᴸData {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ) : Set where
  constructor target-strip★ᴸ-data
  field
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    γ★ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W★)
    lift★ : LiftCtxᴸ X⊑★ γ★ γ★ᴸ
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y★
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : `∀ A ⊑ᵂ⟨ W★ ⟩ ★
    body★ : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W★ ⟩ ★
    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , tgtCtxʷ γ★ ⟩ ⊢ U ⦂ ★
    premise★ :
      CTI2.liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U ∶ body★

TargetStripAt★ : Set
TargetStripAt★ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
    {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ

TargetStripAt★ᴸ : Set
TargetStripAt★ᴸ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ)}
    {V : Term (suc Δᴸ)} {U : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★}
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ
