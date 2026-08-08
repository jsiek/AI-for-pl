module SliceCheck where

-- Scratch-only validation for SLICE-DESIGN.md.
-- This module states a target-tag/target-seal slicing surface and checks
-- that the frozen TargetStripAt★ and TargetStripAt★ᴸ members, the Λ core
-- rebuild, and the target-walk composition can be expressed through it.

import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  renaming (subst to subst≡)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SourceStripDef using
  (CoreRebuild; SourceAtom; SourceColumnStrip; SourceCorePremise;
   SourceSpineStrip; SourceTagSealCore; TargetChainData; atom-Λ;
   atom-ƛ; atom-$; core-sealed; core-tagged; core-terminus;
   core-untagged; source-strip; target-chain-data)
open import proof.DGG.Inversion.TargetStripDef using
  (TargetStripAt★; TargetStripAt★Data; TargetStripAt★ᴸ;
   TargetStripAt★ᴸData; target-strip★-data; target-strip★ᴸ-data)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)
open import proof.DGG.Inversion.SpineValueDef using
  (SpineValue; sv-ƛ; sv-Λ; sv-$)
import proof.DGG.TerminusRebuildProbe as TRP

open CTI2 using
  (World; CtxImp; LiftCtxᴸ; RebaseAt; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ; tgtCtxʷ)

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
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → Wʳ ∣ γʳ ⊢² V ⊑ U ↓ seal Y S ∶ r
  → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ

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
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γʳ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wʳ ∣ γᵇ ⊢²
      V ⊑ U ↓ seal Y S ∶ r
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ

------------------------------------------------------------------------
-- Slice 2: target tag dispatch at ★, with opaque target payload
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
    (N : Term Δᴿ) (Xᴸ : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where

  dispatch-tag :
    TagNodeAt★ Wᵖ γᵖ V A N Y
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

  dispatch-source-fold :
    (∀ {U S}
      → N ≡ U ↓ seal Y S
      → Value U
      → targetStoreʷ Wᵒ ∋ Y ⦂ S
      → TargetStripAt★Data Wᵒ γᵒ V A U Xᴸ)
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

  dispatch-nonvar-empty :
    ⊥
    → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

data TagDispatchAt★ᴸCase {Δᴸ Δᴿ Δ}
    (Wᵒ : World Δᴸ Δᴿ Δ) (γᵒ : CtxImp Wᵒ)
    (Wᵖ : World Δᴸ Δᴿ Δ)
    (γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ))
    (V : Term (suc Δᴸ)) (A : Ty (suc Δᴸ))
    (N : Term Δᴿ) (Xᴸ : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where

  dispatch-tagᴸ :
    TagNodeAt★ᴸ Wᵖ γᵇ V A N Y
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵇ V A N Xᴸ Y

  dispatch-source-foldᴸ :
    (∀ {U S}
      → N ≡ U ↓ seal Y S
      → Value U
      → targetStoreʷ Wᵒ ∋ Y ⦂ S
      → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ)
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵇ V A N Xᴸ Y

  dispatch-nonvar-emptyᴸ :
    ⊥
    → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵇ V A N Xᴸ Y

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
  → Wᵖ ∣ γᵖ ⊢² V ⊑ N ⟨ cY ⟩ ∶ p
  → TagDispatchAt★Case Wᵒ γᵒ Wᵖ γᵖ V A N Xᴸ Y

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
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ N ⟨ cY ⟩ ∶ p
  → TagDispatchAt★ᴸCase Wᵒ γᵒ Wᵖ γᵇ V A N Xᴸ Y

------------------------------------------------------------------------
-- Validation A: frozen target-strip members are corollaries
------------------------------------------------------------------------

target-strip★-from-slices :
  SealDescentAtVar
  → TagDispatchAt★
  → TargetStripAt★
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc target∈ D
    with tag-dispatch sv (vU ↓ seal) mono rb sc D
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc target∈ D
    | dispatch-tag (tag-node★ r prem) =
  seal-at-var sv vU mono rb sc target∈ prem
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc target∈ D
    | dispatch-source-fold resume =
  resume refl vU target∈
target-strip★-from-slices seal-at-var tag-dispatch
    sv vU mono rb sc target∈ D
    | dispatch-nonvar-empty bad =
  ⊥-elim bad

target-strip★ᴸ-from-slices :
  SealDescentAtVarᴸ
  → TagDispatchAt★ᴸ
  → TargetStripAt★ᴸ
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc target∈ liftγ D
    with tag-dispatchᴸ sv (vU ↓ seal) mono rb sc liftγ D
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc target∈ liftγ D
    | dispatch-tagᴸ (tag-node★ᴸ r prem) =
  seal-at-varᴸ sv vU mono rb sc target∈ liftγ prem
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc target∈ liftγ D
    | dispatch-source-foldᴸ resume =
  resume refl vU target∈
target-strip★ᴸ-from-slices seal-at-varᴸ tag-dispatchᴸ
    sv vU mono rb sc target∈ liftγ D
    | dispatch-nonvar-emptyᴸ bad =
  ⊥-elim bad

------------------------------------------------------------------------
-- Validation B: Λ core rebuild re-derives through the slices
------------------------------------------------------------------------

open TargetStripAt★ᴸData
  renaming
    ( Y★ to Y★ᴸ; W★ to W★ᴸ; γ★ to γ★ᴸᵘ
    ; γ★ᴸ to γ★ᴸᵇ; lift★ to lift★ᴸ; mono★ to mono★ᴸ
    ; same★ to same★ᴸ; boundary★ to boundary★ᴸ
    ; target∈★ to target∈★ᴸ; q★ to q★ᴸ; body★ to body★ᴸ
    ; U⊢★ to U⊢★ᴸ; premise★ to premise★ᴸ )

lambda-core-from-target-strip★ᴸ :
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ : World Δᴸ Δᴿ Δ} {γᵒ : CtxImp Wᵒ}
    {V : Term (suc Δᴸ)} {U : Term Δᴿ}
    {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → Value V
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ
  → CoreRebuild Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S
lambda-core-from-target-strip★ᴸ Anv z∈A vV d =
  core-terminus
    (target-chain-data
      (Y★ᴸ d) ★ refl (W★ᴸ d) (γ★ᴸᵘ d) (mono★ᴸ d)
      (same★ᴸ d) (boundary★ᴸ d) (target∈★ᴸ d) (q★ᴸ d)
      (CTI2.Λ⊑² Anv z∈A (lift★ᴸ d) vV (U⊢★ᴸ d)
        (premise★ᴸ d) (q★ᴸ d)))

private
  rebase-target-membership-forward : ∀ {Δᴸ Δᴿ Δ}
      {W′ W : World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
    → RebaseAt W′ W X Y
    → targetStoreʷ W ∋ Y ⦂ S
    → targetStoreʷ W′ ∋ Y ⦂ S
  rebase-target-membership-forward rb Y∈ =
    subst≡ (λ Σ → Σ ∋ _ ⦂ _)
      (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb)) Y∈

  source-atom-spine : ∀ {Δ : TyCtx} {P : Term Δ}
    → SourceAtom P
    → SpineValue P
  source-atom-spine (atom-ƛ N) = sv-ƛ N
  source-atom-spine (atom-Λ sv) = sv-Λ sv
  source-atom-spine (atom-$ κ) = sv-$ κ

source-tag-seal-core-from-slices :
  SealDescentAtVar
  → SealDescentAtVarᴸ
  → TagDispatchAt★
  → TagDispatchAt★ᴸ
  → SourceTagSealCore
source-tag-seal-core-from-slices sealD sealDᴸ tag tagᴸ
    atom vU mono rb sc target∈ (core-untagged qᶜ D) =
  core-sealed _ _ mono sc (CTI2.rebase-varᴸ rb)
    (rebase-target-membership-forward rb target∈) qᶜ D
source-tag-seal-core-from-slices sealD sealDᴸ tag tagᴸ {Xᴸ = Xᴸ}
    (atom-Λ sv) vU mono rb sc target∈
    (core-tagged
      (CTI2.Λ⊑² Anv z∈A liftγ vV target⊢ prem q)) =
  lambda-core-from-target-strip★ᴸ Anv z∈A vV strip★ᴸ
  where
  strip★ᴸ =
    target-strip★ᴸ-from-slices sealDᴸ tagᴸ
      sv vU mono rb sc target∈ liftγ prem
source-tag-seal-core-from-slices sealD sealDᴸ tag tagᴸ {Xᴸ = Xᴸ}
    atom vU mono rb sc target∈ (core-tagged D)
    with target-strip★-from-slices sealD tag (source-atom-spine atom)
      vU mono rb sc target∈ D
source-tag-seal-core-from-slices sealD sealDᴸ tag tagᴸ {Xᴸ = Xᴸ}
    atom vU mono rb sc target∈ (core-tagged D)
    | target-strip★-data Y★ W★ γ★ mono★ same★ boundary★
        target∈★ q★ premise★ =
  core-terminus
    (target-chain-data
      Y★ _ refl W★ γ★ mono★ same★ boundary★ target∈★ q★ premise★)

------------------------------------------------------------------------
-- Validation C: source strip workers remain expressible
------------------------------------------------------------------------

record SharedFoldConsumers : Set₁ where
  field
    source-column : SourceColumnStrip
    source-spine : SourceSpineStrip
    seal-descent : SealDescentAtVar
    seal-descentᴸ : SealDescentAtVarᴸ
    tag-dispatch : TagDispatchAt★
    tag-dispatchᴸ : TagDispatchAt★ᴸ

walk-from-shared-fold-consumers :
  SharedFoldConsumers
  → TargetTagSealWalk
walk-from-shared-fold-consumers consumers {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    with source-spine sv vU mono rb sc X∈ Y∈ D
  where
  open SharedFoldConsumers consumers
walk-from-shared-fold-consumers consumers {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Wᵒ γᵒ qᵒ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
        boundaryᵖᵒ atom target∈ᵒ premiseᶜ resume =
  resume
    (source-tag-seal-core-from-slices
      seal-descent seal-descentᴸ tag-dispatch tag-dispatchᴸ
      {Xᴸ = Xᴸ} {q = qᵒ}
      atom vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ target∈ᵒ premiseᶜ)
  where
  open SharedFoldConsumers consumers

------------------------------------------------------------------------
-- Validation D: TerminusRebuildProbe packages still fit
------------------------------------------------------------------------

instanceA-body-data :
  TargetStripAt★ᴸData TRP.InstanceA.W [] (ƛ (` 0))
    TRP.InstanceA.body TRP.InstanceA.U TRP.InstanceA.X
instanceA-body-data =
  target-strip★ᴸ-data
    TRP.InstanceA.Y
    TRP.InstanceA.W
    []
    []
    CTI2.liftᴸ-[]
    (TRP.mono-refl {W = TRP.InstanceA.W})
    CTI2.same-[]
    TRP.InstanceA.rb-X-Y
    TRP.InstanceA.Y∈
    TRP.InstanceA.source-∀⊑★
    TRP.InstanceA.body⊑★
    TRP.InstanceA.U-⊢
    TRP.InstanceA.body-U²

instanceA-core :
  CoreRebuild TRP.InstanceA.W [] (Λ (ƛ (` 0)))
    (`∀ TRP.InstanceA.body) TRP.InstanceA.U
    TRP.InstanceA.X TRP.InstanceA.Y ★
instanceA-core =
  lambda-core-from-target-strip★ᴸ nonvar-fun (∈-fun-left var-∈)
    (ƛ (` 0)) instanceA-body-data

instanceB-seal-handoff :
  TagNodeAt★ TRP.InstanceB.W [] TRP.InstanceB.V
    (＇ TRP.InstanceB.X) TRP.InstanceB.target-chain TRP.InstanceB.Y
instanceB-seal-handoff =
  tag-node★ TRP.InstanceB.X⊑Y TRP.InstanceB.premise-chain²

instanceB-tag-case :
  TagDispatchAt★Case TRP.InstanceB.W [] TRP.InstanceB.W []
    TRP.InstanceB.V (＇ TRP.InstanceB.X)
    TRP.InstanceB.target-chain TRP.InstanceB.X TRP.InstanceB.Y
instanceB-tag-case = dispatch-tag instanceB-seal-handoff
