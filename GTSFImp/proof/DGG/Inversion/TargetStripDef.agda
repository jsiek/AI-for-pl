module proof.DGG.Inversion.TargetStripDef where

-- File Charter:
--   * States the sliced target-tag-at-star strip surface used by the
--     source-strip core rebuild proof.
--   * Separates right-variable target-seal descent from target-tag
--     dispatch, while keeping the old compound target-strip members as
--     corollaries.
--   * Contains only statement packages and lightweight corollary wiring.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms using
  (Term; Value; _↓_; _⟨_⟩; _⊢_⦂_; ⟨_,_,_⟩; seal)
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using
  (World; CtxImp; LiftCtxᴸ; RebaseAt; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ; tgtCtxʷ)

record TargetSealTerminusData {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ) : Set where
  constructor target-seal-terminus-data
  field
    U★ : Term Δᴿ
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : A ⊑ᵂ⟨ W★ ⟩ ★
    premise★ : W★ ∣ γ★ ⊢² V ⊑ U★ ∶ q★

record TargetSealTerminusᴸData {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ) : Set where
  constructor target-seal-terminusᴸ-data
  field
    U★ : Term Δᴿ
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    γᵒᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵒ)
    γ★ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W★)
    liftᵒ : LiftCtxᴸ X⊑★ γᵒ γᵒᴸ
    lift★ : LiftCtxᴸ X⊑★ γ★ γ★ᴸ
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    body★ : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W★ ⟩ ★
    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , tgtCtxʷ γ★ ⟩ ⊢ U★ ⦂ ★
    premise★ :
      CTI2.liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U★ ∶ body★

record TargetStripAt★Data {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
    (p : A ⊑ᵂ⟨ Wᵖ ⟩ ★) : Set where
  constructor target-strip★-data
  field
    U★ : Term Δᴿ
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    q★ : A ⊑ᵂ⟨ W★ ⟩ ★
    premise★ : W★ ∣ γ★ ⊢² V ⊑ U★ ∶ q★
    reemit :
      W★ ∣ γ★ ⊢² V ⊑ U★ ∶ q★
      → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p

record TargetStripAt★ᴸData {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
    (γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ))
    (p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★) : Set where
  constructor target-strip★ᴸ-data
  field
    U★ : Term Δᴿ
    Y★ : TyVar Δᴿ
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    γ★ᴸ : CtxImp (CTI2.liftWorldLeft X⊑★ W★)
    lift★ : LiftCtxᴸ X⊑★ γ★ γ★ᴸ
    mono★ : CTI2.ImpEnvMono Wᵒ W★
    same★ : CTI2.SameCtx γᵒ γ★
    boundary★ : RebaseAt W★ Wᵒ Xᴸ Y
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ ★
    body★ : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W★ ⟩ ★
    U⊢★ : ⟨ Δᴿ , targetStoreʷ W★ , tgtCtxʷ γ★ ⟩ ⊢ U★ ⦂ ★
    premise★ :
      CTI2.liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U★ ∶ body★
    reemit :
      CTI2.liftWorldLeft X⊑★ W★ ∣ γ★ᴸ ⊢² V ⊑ U★ ∶ body★
      → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
          V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p

------------------------------------------------------------------------
-- Slice 1: target seal descent at a right-variable obligation
------------------------------------------------------------------------

SealDescentAtVar : Set
SealDescentAtVar =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γʳ : CtxImp Wʳ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {r : A ⊑ᵂ⟨ Wʳ ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γʳ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
  → TargetSealTerminusData Wᵒ γᵒ V A U Xᴸ Y S

SealDescentAtVarᴸ : Set
SealDescentAtVarᴸ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wʳ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γʳ : CtxImp Wʳ}
    {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wʳ)}
    {V : Term (suc Δᴸ)} {U : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {r : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wʳ ⟩ ＇ Y}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wʳ
  → RebaseAt Wʳ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γʳ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γʳ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wʳ ∣ γᵇ ⊢²
      V ⊑ U ↓ seal Y S ∶ r
  → TargetSealTerminusᴸData Wᵒ γᵒ V A U Xᴸ Y S

------------------------------------------------------------------------
-- Slice 2: target tag dispatch at ★
------------------------------------------------------------------------

record TagNodeAt★ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (N : Term Δᴿ) (Y : TyVar Δᴿ) : Set where
  constructor tag-node★
  field
    r★ : A ⊑ᵂ⟨ W ⟩ ＇ Y
    premiseᵛ : W ∣ γ ⊢² V ⊑ N ∶ r★

record TagNodeAt★ᴸ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ W))
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (N : Term Δᴿ) (Y : TyVar Δᴿ) : Set where
  constructor tag-node★ᴸ
  field
    r★ᴸ : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ W ⟩ ＇ Y
    premiseᵛᴸ :
      CTI2.liftWorldLeft X⊑★ W ∣ γᵇ ⊢² V ⊑ N ∶ r★ᴸ

data TagDispatchAt★Case {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (N : Term Δᴿ) (Xᴸ : TyVar Δᴸ) (Y : TyVar Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (p : A ⊑ᵂ⟨ Wᵖ ⟩ ★) : Set where

  dispatch-tag :
    TagNodeAt★ Wᵖ γᵖ V A N Y
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y cY p

  dispatch-source-fold :
    (∀ {U S}
      → N ≡ U ↓ seal Y S
      → Value U
      → targetStoreʷ Wᵒ ∋ Y ⦂ S
      → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ p)
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y cY p

  dispatch-nonvar-empty :
    ⊥
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y cY p

data TagDispatchAt★ᴸCase {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (Wᵖ : World Δᴸ Δᴿ Δ) (γᵖ : CtxImp Wᵖ)
    (γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ))
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (N : Term Δᴿ) (Xᴸ : TyVar Δᴸ) (Y : TyVar Δᴿ)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★)
    (p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★) : Set where

  dispatch-tagᴸ :
    TagNodeAt★ᴸ Wᵖ γᵇ V A N Y
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵖ γᵇ V A N Xᴸ Y cY p

  dispatch-source-foldᴸ :
    (∀ {U S}
      → N ≡ U ↓ seal Y S
      → Value U
      → targetStoreʷ Wᵒ ∋ Y ⦂ S
      → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ γᵇ p)
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵖ γᵇ V A N Xᴸ Y cY p

  dispatch-nonvar-emptyᴸ :
    ⊥
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵖ γᵇ V A N Xᴸ Y cY p

TagDispatchAt★ : Set
TagDispatchAt★ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {V : Term Δᴸ} {N : Term Δᴿ}
    {A : Ty Δᴸ} {Xᴸ : TyVar Δᴸ}
    {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → SpineValue V
  → Value N
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → Wᵖ ∣ γᵖ ⊢² V ⊑ N ⟨ cY ⟩ ∶ p
  → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y cY p

TagDispatchAt★ᴸ : Set
TagDispatchAt★ᴸ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ)}
    {V : Term (suc Δᴸ)} {N : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {Xᴸ : TyVar Δᴸ}
    {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ}
    {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★}
  → SpineValue V
  → Value N
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ N ⟨ cY ⟩ ∶ p
  → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵖ γᵇ V A N Xᴸ Y cY p

TargetStripAt★ : Set
TargetStripAt★ =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ}
    {Y : TyVar Δᴿ} {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wᵖ ∣ γᵖ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ p

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
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → sourceStoreʷ Wᵒ ∋ Xᴸ ⦂ ★
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ Y S cY Wᵖ γᵖ γᵇ p

target-strip★-from-slices :
  SealDescentAtVar
  → TagDispatchAt★
  → TargetStripAt★
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc source∈ target∈ D
    with tag-dispatch sv (vU ↓ seal) mono rb sc source∈ D
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc source∈ target∈ D
    | dispatch-tag (tag-node★ r prem)
    with seal-at-var sv vU mono rb sc source∈ target∈ prem
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc source∈ target∈ D
    | dispatch-tag (tag-node★ r prem)
    | target-seal-terminus-data U★ Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premise★ =
  target-strip★-data U★ Y★ W★ γ★ mono★ same★ boundary★ target∈★
    q★ premise★ (λ _ → D)
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc source∈ target∈ D
    | dispatch-source-fold resume =
  resume refl vU target∈
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc source∈ target∈ D
    | dispatch-nonvar-empty bad =
  ⊥-elim bad

target-strip★ᴸ-from-slices :
  SealDescentAtVarᴸ
  → TagDispatchAt★ᴸ
  → TargetStripAt★ᴸ
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc source∈ target∈ liftγ D
    with tag-dispatchᴸ sv (vU ↓ seal) mono rb sc source∈ liftγ D
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc source∈ target∈ liftγ D
    | dispatch-tagᴸ (tag-node★ᴸ r prem)
    with seal-at-varᴸ sv vU mono rb sc source∈ target∈ liftγ prem
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc source∈ target∈ liftγ D
    | dispatch-tagᴸ (tag-node★ᴸ r prem)
    | target-seal-terminusᴸ-data U★ Y★ W★ γ★ γᵒᴸ γ★ᴸ liftᵒ lift★
        mono★ same★ boundary★ target∈★ body★ U⊢★ premise★ =
  target-strip★ᴸ-data U★ Y★ W★ γ★ γ★ᴸ lift★ mono★ same★
    boundary★ target∈★ body★ U⊢★ premise★ (λ _ → D)
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc source∈ target∈ liftγ D
    | dispatch-source-foldᴸ resume =
  resume refl vU target∈
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc source∈ target∈ liftγ D
    | dispatch-nonvar-emptyᴸ bad =
  ⊥-elim bad
