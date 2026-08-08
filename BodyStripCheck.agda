module BodyStripCheck where

-- Scratch-only validation for BODYSTRIP-DESIGN.md.
-- This file states the proposed target-strip-at-star package as a hypothesis
-- and checks the dependent indices needed by the Λ core rebuild.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SourceStripDef using
  (CoreRebuild; SourceSpineStrip; SourceTagSealCore; TargetChainData;
   core-terminus; source-strip; target-chain-data)
open import proof.DGG.Inversion.TargetWalkDef using (TargetTagSealWalk)
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
import proof.DGG.TerminusRebuildProbe as TRP

open CTI2 using
  (World; CtxImp; LiftCtxᴸ; RebaseAt; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ; tgtCtxʷ)

------------------------------------------------------------------------
-- Proposed terminal packages
------------------------------------------------------------------------

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

open TargetStripAt★Data
  renaming
    ( Y★ to Y★ᵈ; W★ to W★ᵈ; γ★ to γ★ᵈ; mono★ to mono★ᵈ
    ; same★ to same★ᵈ; boundary★ to boundary★ᵈ
    ; target∈★ to target∈★ᵈ; q★ to q★ᵈ; premise★ to premise★ᵈ )
open TargetStripAt★ᴸData
  renaming
    ( Y★ to Y★ᴸ; W★ to W★ᴸ; γ★ to γ★ᴸᵘ
    ; γ★ᴸ to γ★ᴸᵇ; lift★ to lift★ᴸ; mono★ to mono★ᴸ
    ; same★ to same★ᴸ; boundary★ to boundary★ᴸ
    ; target∈★ to target∈★ᴸ; q★ to q★ᴸ; body★ to body★ᴸ
    ; U⊢★ to U⊢★ᴸ; premise★ to premise★ᴸ )

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
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → TargetStripAt★ᴸData Wᵒ γᵒ V A U Xᴸ

------------------------------------------------------------------------
-- Validation A: the blocked Λ core branch follows from the lifted member
------------------------------------------------------------------------

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
      (Y★ᴸ d) ★ refl (W★ᴸ d) (γ★ᴸᵘ d) (mono★ᴸ d) (same★ᴸ d)
      (boundary★ᴸ d) (target∈★ᴸ d) (q★ᴸ d)
      (CTI2.Λ⊑² Anv z∈A (lift★ᴸ d) vV (U⊢★ᴸ d)
        (premise★ᴸ d) (q★ᴸ d)))

lambda-core-from-member :
  TargetStripAt★ᴸ
  → ∀ {Δᴸ Δᴿ Δ}
      {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
      {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
      {γᵇ : CtxImp (CTI2.liftWorldLeft X⊑★ Wᵖ)}
      {V : Term (suc Δᴸ)} {U : Term Δᴿ}
      {A : Ty (suc Δᴸ)} {S : Ty Δᴿ}
      {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
      {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
      {bodyp : A ⊑ᵂ⟨ CTI2.liftWorldLeft X⊑★ Wᵖ ⟩ ★}
  → NonVar A
  → Fin.zero ∈ᵗ A
  → LiftCtxᴸ X⊑★ γᵖ γᵇ
  → SpineValue V
  → Value V
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → CTI2.liftWorldLeft X⊑★ Wᵖ ∣ γᵇ ⊢²
      V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ bodyp
  → CoreRebuild Wᵒ γᵒ (Λ V) (`∀ A) U Xᴸ Y S
lambda-core-from-member stripᴸ Anv z∈A liftγ sv vV vU mono rb sc
    Y∈ bodyD =
  lambda-core-from-target-strip★ᴸ Anv z∈A vV
    (stripᴸ sv vU mono rb sc Y∈ liftγ bodyD)

------------------------------------------------------------------------
-- Validation B: TerminusRebuildProbe Instance A's body fits the package
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

------------------------------------------------------------------------
-- Validation C: walk-from-strip composition remains unchanged
------------------------------------------------------------------------

walk-from-strip-with-target-strip★ :
  SourceSpineStrip
  → TargetStripAt★
  → TargetStripAt★ᴸ
  → SourceTagSealCore
  → TargetTagSealWalk
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    with strip sv vU mono rb sc X∈ Y∈ D
walk-from-strip-with-target-strip★ strip strip★ strip★ᴸ core {Xᴸ = Xᴸ}
    sv vU mono rb sc X∈ Y∈ D
    | source-strip P A Wᵒ γᵒ qᵒ Wᵖ γᵖ pᵖ monoᵒᵖ sameᵒᵖ
        boundaryᵖᵒ atom target∈ᵒ premiseᶜ resume =
  resume
    (core {Xᴸ = Xᴸ} {q = qᵒ}
      atom vU monoᵒᵖ boundaryᵖᵒ sameᵒᵖ target∈ᵒ premiseᶜ)
