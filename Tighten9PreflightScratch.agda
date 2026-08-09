module Tighten9PreflightScratch where

-- Root-level scratch for tighten pre-flight 9.
-- Purpose: model option (i) from PEDIGREE-DESIGN-MEMO.md's round-18
-- addendum, where `conceal⊑²` ties the source-conceal partner pedigree
-- to the source tag-rebase target pivot.
-- Primary exports: a tied source-conceal wrapper, the round-18 package
-- witness from same-index evidence, and verbatim aliases for the round-8
-- subheads, worker empties, and laundering batteries.
-- Key dependencies: the live CTI2 relation, SealTransferCore package
-- helpers, and Tighten8PreflightScratch.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; id; _!)
open import CastTerms using (Term; Inert; _⟨_⟩; _↓_)
open import Conversion using (Conv↓; seal)
open import Imprecision

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealTransferCore as STC
import proof.DGG.TerminusRebuildProbe as TRP
import SourceStarPackageCounterScratch as SSC
import Tighten8PreflightScratch as T8

open CTI2 using
  (World; CtxImp; RebaseAt; TagRebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; _⊢↓[_]_)

module B = TRP.InstanceB

------------------------------------------------------------------------
-- Tied source-conceal surface
------------------------------------------------------------------------

conceal⊑²₉ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
  → CTI2.SourceConcealPartnerOK W′ M c Xᴿ? M′
  → CTI2.ImpEnvMono W W′
  → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
  → CTI2.SameCtx γ γ′
  → CTI2.sourceStoreʷ W ⊢↓[ Xᴸ? ] c
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A′ ⊑ᵂ⟨ W ⟩ B)
    -----------------------------
  → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
conceal⊑²₉ ok mono rb sc c⊢ D q =
  CTI2.conceal⊑² ok mono rb sc c⊢ D q

source-star-premise₉ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.ImpEnvMono W W′
  → TagRebaseAtᴸ W′ W (just X) Xᴿ?
  → CTI2.SameCtx γ γ′
  → CTI2.sourceStoreʷ W ⊢↓[ just X ] seal X ★
  → CTI2.Rep★PartnerOK W′ X V Xᴿ? U
  → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
  → W ∣ γ ⊢² V ↓ seal X ★ ⊑ U ∶ q
source-star-premise₉ mono rb sc source⊢ partner prem =
  conceal⊑²₉
    (CTI2.seal-partner-ok (CTI2.star-rep-target partner))
    mono rb sc source⊢ prem _

------------------------------------------------------------------------
-- Round-18 source-conceal package shape
------------------------------------------------------------------------

round18-source-conceal-package₉ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTI2.Rep★PartnerOK Wᵖ X P (just Y) U
  → W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
  → STC.TaggedTransferOutput W γ P U X (just Y)
round18-source-conceal-package₉ =
  STC.tagged-transfer-output-from-transport

round18-source-star-premise-package₉ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : ★ ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ ★}
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W X Y
  → CTI2.SameCtx γ γ′
  → CTI2.sourceStoreʷ W ⊢↓[ just X ] seal X ★
  → CTI2.Rep★PartnerOK W′ X V (just Y) U
  → W′ ∣ γ′ ⊢² V ⊑ U ∶ p
  → W ∣ γ ⊢² V ⊑ U ∶ ★⊑★
  → W ∣ γ ⊢² V ↓ seal X ★ ⊑ U ∶ q
    × STC.TaggedTransferOutput W γ V U X (just Y)
round18-source-star-premise-package₉ mono rb sc source⊢ partner prem pkgPrem =
  source-star-premise₉ mono (CTI2.tag-rebase-varᴸ rb) sc source⊢
    partner prem ,
  round18-source-conceal-package₉ rb partner pkgPrem

------------------------------------------------------------------------
-- Verbatim round-8 checks under the tied model
------------------------------------------------------------------------

round16-cast-subhead-package₉ :
  ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ : World Δᴸ Δᴿ Δ}
    {γ₂ : CtxImp W₂}
    {X : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★}
  → RebaseAt W₃ W₂ X Yᵖ
  → CTI2.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → W₂ ∣ γ₂ ⊢² P ↓ seal X ★ ⊑ U ∶ q₂
  → T8.TaggedTransferOutput₈ W₂ γ₂
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵖ)
round16-cast-subhead-package₉ =
  T8.round16-cast-subhead-package₈

round16-source-seal-subhead₉ :
  ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ W₀ : World Δᴸ Δᴿ Δ}
    {γ₂ : CtxImp W₂}
    {X : TyVar Δᴸ} {Yᵖ Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★}
  → RebaseAt W₃ W₂ X Yᵖ
  → RebaseAt W₂ W₀ X Y
  → CTI2.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → W₂ ∣ γ₂ ⊢² P ↓ seal X ★ ⊑ U ∶ q₂
  → T8.TaggedTransferOutput₈ W₂ γ₂
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵖ)
round16-source-seal-subhead₉ =
  T8.round16-source-seal-subhead₈

worker-source-seal-var-tag-no-target-after-cast-empty₉ :
    ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → CTI2.SourceConcealPartnerOK W P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
worker-source-seal-var-tag-no-target-after-cast-empty₉ =
  T8.worker-source-seal-var-tag-no-target-after-cast-empty₈

wrong-pedigree-package-empty₉ :
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {X : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → CTI2.CenterAligned W X Y
  → Y₂ ≢ Y
  → T8.TaggedTransferOutput₈ W γ P U X (just Y₂)
  → ⊥
wrong-pedigree-package-empty₉ =
  T8.wrong-pedigree-package-empty₈

wrong-pedigree-round-trip-blocked₉ :
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {X : TyVar Δᴸ} {Yᵢ Yᵒ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → CTI2.CenterAligned W X Yᵢ
  → Yᵒ ≢ Yᵢ
  → T8.TaggedTransferOutput₈ W γ
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵒ)
  → ⊥
wrong-pedigree-round-trip-blocked₉ =
  T8.wrong-pedigree-round-trip-blocked₈

different-name-round-trip-no-launder₉ =
  T8.different-name-round-trip-no-launder₈

non-rep★-round-trip-no-launder₉ =
  T8.non-rep★-round-trip-no-launder₈

round15-counterexample-stays-closed₉ :
  T8.TaggedTransferOutput₈ B.W [] SSC.source-output-tag SSC.target-tag
    B.X (just B.Y₂)
  → ⊥
round15-counterexample-stays-closed₉ =
  T8.round15-counterexample-stays-closed₈

round15-live-output-partner-still-empty₉ :
  CTI2.Rep★PartnerOK B.W B.X SSC.source-output-tag
    (just B.Y₂) SSC.target-tag
  → ⊥
round15-live-output-partner-still-empty₉ =
  T8.round15-live-output-partner-still-empty₈
