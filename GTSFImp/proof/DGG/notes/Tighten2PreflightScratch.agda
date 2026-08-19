module Tighten2PreflightScratch where

-- Root-level scratch for the second rep-★ tightening pre-flight.
-- This does not edit the live GTSFImp relation.  It models the proposed
-- source-payload-indexed partner predicate and checks formation/emptiness
-- facts for the stopped migration points.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!; toRenameᵗ)
open import CastTerms using (Term; _⟨_⟩)
open import Imprecision

import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision2 as CTIR
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.LambdaImpProbe as LIP
import proof.DGG.StarRepChainProbe as SRC
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.TagBoundaryProbe as TBP
import proof.DGG.TerminusRebuildProbe as TRB
import proof.DGG.Examples2 as Ex2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.Parked.ParkedD4CheckpointLemma as D4

open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Proposed source-payload-indexed rep-★ partner predicate
------------------------------------------------------------------------

CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W X Y =
  toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y

data Rep★PartnerOK₂ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged : ∀ {P Xᴿ? M′}
    → CTI2.NotTopTag M′
      -------------------------------------------
    → Rep★PartnerOK₂ W X P Xᴿ? M′

  rep★-nonvar-tag : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK₂ W X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-outer-var-tag : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK₂ W X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → Rep★PartnerOK₂ W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

------------------------------------------------------------------------
-- Stopped meta obligations: partner formation from in-hand evidence
------------------------------------------------------------------------

target-chain-85-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → (Yᵒ : TyVar Δᴿ)
  → (＇ X₂) ⊑ᵂ⟨ W ⟩ (＇ Y₂)
  → Rep★PartnerOK₂ W X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
target-chain-85-partner {W = W} {X₂ = X₂} {Y₂ = Y₂} {V₂ = V₂}
    {U₂ = U₂} {Aᴸ = Aᴸ} {Aᴿ = Aᴿ} {μᴸ = μᴸ} {μᴿ = μᴿ}
    {X₂∼★ = X₂∼★} {Y₂∼★ = Y₂∼★} {cX = cX} {cY = cY}
    {AnsX = AnsX} {AnsY = AnsY} Yᵒ p₂ =
  rep★-matched-inner-tags {Y = Yᵒ} {X₂ = X₂} {Y₂ = Y₂}
    {V₂ = V₂} {U₂ = U₂} {Aᴸ = Aᴸ} {Aᴿ = Aᴿ}
    {μᴸ = μᴸ} {μᴿ = μᴿ} {X₂∼★ = X₂∼★}
    {Y₂∼★ = Y₂∼★} {cX = cX} {cY = cY}
    {AnsX = AnsX} {AnsY = AnsY}
    (SVD.variable-obligation-aligns {W = W} {X = X₂} {Y = Y₂} p₂)

target-descent-138-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → (Yᵒ : TyVar Δᴿ)
  → (＇ X₂) ⊑ᵂ⟨ W ⟩ (＇ Y₂)
  → Rep★PartnerOK₂ W X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
target-descent-138-partner = target-chain-85-partner

right-inj-612-partner : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → (Yᵒ : TyVar Δᴿ)
  → CenterAligned W X₂ Y₂
  → Rep★PartnerOK₂ W X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
right-inj-612-partner {X₂ = X₂} {Y₂ = Y₂} Yᵒ aligned =
  rep★-matched-inner-tags {Y = Yᵒ} {X₂ = X₂} {Y₂ = Y₂}
    aligned

------------------------------------------------------------------------
-- Payoffs: no-target variable tags and ℕ-tagged payloads stay empty
------------------------------------------------------------------------

var-tag-no-target-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₂ W X P nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty (rep★-untagged ())
var-tag-no-target-empty (rep★-nonvar-tag ())

nat-payload-var-tag-no-target-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {ι : Base} {Y₂ : TyVar Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {G∼★ : μᴸ ⊢ (‵ ι) ∼★} {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cG : μᴸ ⊢ Aᴸ ∼ ‵ ι} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsG : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₂ W X
      (V₂ ⟨ _! {G = ‵ ι} ⦃ Gᵍ = ‵ ι ⦄
            ⦃ G∼★ = G∼★ ⦄ cG ⦃ Ans = AnsG ⦄ ⟩)
      nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
nat-payload-var-tag-no-target-empty = var-tag-no-target-empty

data MatchedInnerTagsOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  matched-inner-tags-ok : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → MatchedInnerTagsOK W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

bare-payload-matched-inner-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Yᵒ : TyVar Δᴿ}
    {Y₂ : TyVar Δᴿ} {V : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → (∀ {X₂ V₂ Aᴸ μᴸ}
        {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
        {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {AnsX : NonStar Aᴸ}
      → V ≢
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩))
  → MatchedInnerTagsOK W X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-matched-inner-empty not-inner (matched-inner-tags-ok _) =
  not-inner refl

ground-target-still-admitted : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {M : Term Δᴿ} {A G : Ty Δᴿ} {μ : Env∼ Δᴿ}
    {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
    {c : μ ⊢ A ∼ G} {Ans : NonStar A}
  → NonVar G
  → Rep★PartnerOK₂ W X P Xᴿ?
      (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
            c ⦃ Ans = Ans ⦄ ⟩)
ground-target-still-admitted = rep★-nonvar-tag

------------------------------------------------------------------------
-- Current stopped tree gates imported read-only
------------------------------------------------------------------------

star-rep-chain-gate :
  SRC.W ∣ [] ⊢² SRC.M ⊑ SRC.target-sealed ∶ SRC.q
star-rep-chain-gate = SRC.output

chain-ride-gate :
  CRP.W₂ ∣ [] ⊢² CRP.V ⊑ CRP.U ∶ CRP.q₂
chain-ride-gate = CRP.probe-premise

tag-boundary-gate :
  TBP.probe-W₅ ∣ [] ⊢² TBP.probe-V ⊑ TBP.probe-M₅ ∶ TBP.p₅
tag-boundary-gate = TBP.probe-source-seal²

terminus-B-gate :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
terminus-B-gate = TRB.InstanceB.tagged-input

lambda-imp-ground-wrapper-empty-gate = LIP.probe-sealed-arg-empty

example12-checkpoint₄-gate = Ex2.example12-checkpoint₄
nat-chain-checkpoint₄-gate = Ex2.nat-chain-checkpoint₄
left-path-checkpoint-final-gate = Ex2.left-path-checkpoint-final

catalog-adversarial-source-chain-initial-gate =
  P3.adversarial-source-chain-initial²
catalog-adversarial-source-chain-checkpoint₁-gate =
  P3.adversarial-source-chain-checkpoint₁
catalog-skew-star-inst-initial-gate = P3.skew-star-inst-initial²
catalog-tag-boundary-star-inst-initial-gate =
  P3.tag-boundary-star-inst-initial²
catalog-star-inst-checkpoint₁-gate = P3.star-inst-checkpoint₁
catalog-higher-order-shared-arg-initial-gate =
  P3.higher-order-shared-arg-initial²
catalog-D4-checkpoint-gate = D4.D4-checkpoint
