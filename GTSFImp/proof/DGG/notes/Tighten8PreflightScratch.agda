module Tighten8PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 8.
-- Purpose: model option B from PEDIGREE-DESIGN-MEMO.md: the paired
-- conceal rule consumes a partner package indexed by the premise-world
-- partner, while the conclusion target name stays only in RebaseAt.
-- Primary exports: the premise-world package surface, round-16 package
-- builders, laundering/emptiness refutations, and the InstanceB countercheck.
-- Key dependencies: the live propagated CTX.Rep★PartnerOK discipline,
-- SealTransferCore transport, and SourceStarPackageCounterScratch.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≢_; _≡_; refl; sym; trans)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!; id; toRenameᵗ)
open import CastTerms using (Term; Inert; _⟨_⟩; _↓_)
open import Conversion using (Conv↑; Conv↓; seal; _↦↓_; `∀↓_; id↓)
open import Imprecision

import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.SealTransferCore as STC
import proof.DGG.TerminusRebuildProbe as TRP
import SourceStarPackageCounterScratch as SSC
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)

module B = TRP.InstanceB

open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Premise-world partner index
------------------------------------------------------------------------

aligned-functional₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → CTX.CenterAligned W X Y
  → CTX.CenterAligned W X Y′
  → Y ≡ Y′
aligned-functional₈ {W = W} aligned aligned′ =
  toRenameᵗ-injective (CTX.ηᴿʷ W) (trans (sym aligned) aligned′)

data PremisePartnerAt {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Maybe (TyVar Δᴿ) → Set where
  premise-partner-just : ∀ {Y}
    → CTX.CenterAligned W X Y
      -------------------------------
    → PremisePartnerAt W X (just Y)

  premise-partner-nothing :
      (∀ Y → CTX.CenterAligned W X Y → ⊥)
      ------------------------------------
    → PremisePartnerAt W X nothing

premise-partner-wrong-just-empty₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
  → CTX.CenterAligned W X Y
  → Y₂ ≢ Y
  → PremisePartnerAt W X (just Y₂)
  → ⊥
premise-partner-wrong-just-empty₈ {W = W} {X = X} {Y = Y}
    {Y₂ = Y₂} aligned Y₂≢Y
    (premise-partner-just {Y = .Y₂} aligned₂) =
  Y₂≢Y
    (sym (aligned-functional₈ {W = W} {X = X} {Y = Y}
      {Y′ = Y₂} aligned aligned₂))

------------------------------------------------------------------------
-- Revised matched/package surface
------------------------------------------------------------------------

data MatchedConcealPartnerOK₈ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  matched-seal-star-partner₈ : ∀ {P X Xᴿ? M′}
    → CTX.Rep★PartnerOK W X P Xᴿ? M′
      ----------------------------------------------------
    → MatchedConcealPartnerOK₈ W P (seal X ★) Xᴿ? M′

  matched-seal-nonstar₈ : ∀ {P X R Xᴿ? M′}
    → NonStar R
      ----------------------------------------------------
    → MatchedConcealPartnerOK₈ W P (seal X R) Xᴿ? M′

  matched-fun-conceal-target₈ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₈ W P (c ↦↓ d) Xᴿ? M′

  matched-all-conceal-target₈ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₈ W P (`∀↓ c) Xᴿ? M′

  matched-id-conceal-target₈ : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₈ W P (id↓ A) Xᴿ? M′

record TaggedTransferOutput₈ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Xᴿ? : Maybe (TyVar Δᴿ)) : Set where
  constructor tagged-transfer-output₈
  field
    premise₈ : W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    pedigree₈ : PremisePartnerAt W X Xᴿ?
    partner₈ : MatchedConcealPartnerOK₈ W P (seal X ★) Xᴿ? U

record PairedSealEmission₈ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Y : TyVar Δᴿ)
    (Xᴿ? : Maybe (TyVar Δᴿ)) : Set where
  constructor paired-seal-emission₈
  field
    Wᵖ₈ : World Δᴸ Δᴿ Δ
    γᵖ₈ : CtxImp Wᵖ₈
    mono₈ : CTX.ImpEnvMono W Wᵖ₈
    rebase₈ : RebaseAt Wᵖ₈ W X Y
    same₈ : CTX.SameCtx γ γᵖ₈
    source⊢₈ : CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X ★
    target⊢₈ : CTX.targetStoreʷ W Conv.⊢↓[ just Y ] seal Y ★
    package₈ : TaggedTransferOutput₈ Wᵖ₈ γᵖ₈ P U X Xᴿ?

emit-tagged-transfer₈ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ} {Xᴿ? : Maybe (TyVar Δᴿ)}
  → CTX.ImpEnvMono W Wᵖ
  → RebaseAt Wᵖ W X Y
  → CTX.SameCtx γ γᵖ
  → CTX.sourceStoreʷ W Conv.⊢↓[ just X ] seal X ★
  → CTX.targetStoreʷ W Conv.⊢↓[ just Y ] seal Y ★
  → TaggedTransferOutput₈ Wᵖ γᵖ P U X Xᴿ?
  → PairedSealEmission₈ W γ P U X Y Xᴿ?
emit-tagged-transfer₈ mono rb sc source⊢ target⊢ pkg =
  paired-seal-emission₈ _ _ mono rb sc source⊢ target⊢ pkg

tagged-transfer-output-from-transport₈ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → CTX.Rep★PartnerOK Wᵖ X P (just Y) U
  → W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
  → TaggedTransferOutput₈ W γ P U X (just Y)
tagged-transfer-output-from-transport₈ rb ok prem =
  tagged-transfer-output₈ prem
    (premise-partner-just (CTX.RebaseAt.pivotAligned rb))
    (matched-seal-star-partner₈
      (STC.transport-rep★-partner-ok rb ok))

round16-cast-subhead-package₈ : ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ : World Δᴸ Δᴿ Δ}
    {γ₂ : CtxImp W₂}
    {X : TyVar Δᴸ} {Yᵖ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★}
  → RebaseAt W₃ W₂ X Yᵖ
  → CTX.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → W₂ ∣ γ₂ ⊢² P ↓ seal X ★ ⊑ U ∶ q₂
  → TaggedTransferOutput₈ W₂ γ₂
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵖ)
round16-cast-subhead-package₈ rbᵖ partner D₂ =
  tagged-transfer-output₈
    (CTI2.cast⊑² (id (＇ _) !) D₂ ★⊑★)
    (premise-partner-just (CTX.RebaseAt.pivotAligned rbᵖ))
    (matched-seal-star-partner₈
      (CTX.rep★-round-trip
        (STC.transport-rep★-partner-ok rbᵖ partner)))

round16-source-seal-subhead₈ : ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ W₀ : World Δᴸ Δᴿ Δ}
    {γ₂ : CtxImp W₂}
    {X : TyVar Δᴸ} {Yᵖ Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★}
  → RebaseAt W₃ W₂ X Yᵖ
  → RebaseAt W₂ W₀ X Y
  → CTX.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → W₂ ∣ γ₂ ⊢² P ↓ seal X ★ ⊑ U ∶ q₂
  → TaggedTransferOutput₈ W₂ γ₂
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵖ)
round16-source-seal-subhead₈ rbᵖ link partner D₂ =
  round16-cast-subhead-package₈ rbᵖ partner D₂

emit-tagged-transfer-peel₈ : ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ W₀ : World Δᴸ Δᴿ Δ}
    {γ₀ : CtxImp W₀} {γ₂ : CtxImp W₂}
    {X : TyVar Δᴸ} {Yᵖ Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {q₂ : (＇ X) ⊑ᵂ⟨ W₂ ⟩ ★}
  → CTX.ImpEnvMono W₀ W₂
  → RebaseAt W₃ W₂ X Yᵖ
  → RebaseAt W₂ W₀ X Y
  → CTX.SameCtx γ₀ γ₂
  → CTX.sourceStoreʷ W₀ Conv.⊢↓[ just X ] seal X ★
  → CTX.targetStoreʷ W₀ Conv.⊢↓[ just Y ] seal Y ★
  → CTX.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → W₂ ∣ γ₂ ⊢² P ↓ seal X ★ ⊑ U ∶ q₂
  → PairedSealEmission₈ W₀ γ₀
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X Y (just Yᵖ)
emit-tagged-transfer-peel₈ mono rbᵖ link sc source⊢ target⊢ partner D₂ =
  emit-tagged-transfer₈ mono link sc source⊢ target⊢
    (round16-source-seal-subhead₈ rbᵖ link partner D₂)

------------------------------------------------------------------------
-- Laundering and emptiness checks
------------------------------------------------------------------------

wrong-pedigree-package-empty₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {X : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → CTX.CenterAligned W X Y
  → Y₂ ≢ Y
  → TaggedTransferOutput₈ W γ P U X (just Y₂)
  → ⊥
wrong-pedigree-package-empty₈ aligned Y₂≢Y pkg =
  premise-partner-wrong-just-empty₈ aligned Y₂≢Y
    (TaggedTransferOutput₈.pedigree₈ pkg)

wrong-pedigree-round-trip-blocked₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {X : TyVar Δᴸ} {Yᵢ Yᵒ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → CTX.CenterAligned W X Yᵢ
  → Yᵒ ≢ Yᵢ
  → TaggedTransferOutput₈ W γ
      ((P ↓ seal X ★) ⟨ id (＇ X) ! ⟩) U X (just Yᵒ)
  → ⊥
wrong-pedigree-round-trip-blocked₈ aligned Yᵒ≢Yᵢ pkg =
  wrong-pedigree-package-empty₈ aligned Yᵒ≢Yᵢ pkg

var-tag-no-target-empty₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → CTX.Rep★PartnerOK W X P nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty₈ (CTX.rep★-untagged ())
var-tag-no-target-empty₈ (CTX.rep★-nonvar-tag ())
var-tag-no-target-empty₈ (CTX.rep★-round-trip ok) =
  var-tag-no-target-empty₈ ok

source-seal-var-tag-no-target-empty₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → CTX.SourceConcealPartnerOK W P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-empty₈
    (CTX.seal-partner-ok (CTX.star-rep-target ok)) =
  var-tag-no-target-empty₈ ok
source-seal-var-tag-no-target-empty₈
    (CTX.seal-partner-ok (CTX.plain-target ()))

worker-source-seal-var-tag-no-target-after-cast-empty₈ :
    ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → CTX.SourceConcealPartnerOK W P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
worker-source-seal-var-tag-no-target-after-cast-empty₈ inert ok =
  source-seal-var-tag-no-target-empty₈ ok

bare-payload-var-tag-mismatch-empty₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Y₂ : TyVar Δᴿ} {V : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → (∀ {X₂ V₂ Aᴸ μᴸ}
        {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
        {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {AnsX : NonStar Aᴸ}
      → V ≢
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩))
  → (∀ {P₀ Aˣ μˣ}
        {X∼★ : μˣ ⊢ (＇ X) ∼★}
        {cX : μˣ ⊢ Aˣ ∼ ＇ X} {AnsX : NonStar Aˣ}
      → V ≢
        ((P₀ ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩))
  → (CTX.CenterAligned W X Y₂ → ⊥)
  → CTX.Rep★PartnerOK W X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₈ not-inner not-roundtrip
    not-aligned (CTX.rep★-untagged ())
bare-payload-var-tag-mismatch-empty₈ not-inner not-roundtrip
    not-aligned (CTX.rep★-nonvar-tag ())
bare-payload-var-tag-mismatch-empty₈ not-inner not-roundtrip
    not-aligned (CTX.rep★-var-tag aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₈ not-inner not-roundtrip
    not-aligned (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  not-inner refl
bare-payload-var-tag-mismatch-empty₈ not-inner not-roundtrip
    not-aligned (CTX.rep★-round-trip ok) =
  not-roundtrip refl

different-name-round-trip-no-launder₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X Z : TyVar Δᴸ}
    {Yᵒ Y₂ : TyVar Δᴿ} {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {Aᶻ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μᶻ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {Z∼★ : μᶻ ⊢ (＇ Z) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cZ : μᶻ ⊢ Aᶻ ∼ ＇ Z}
    {cY : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsZ : NonStar Aᶻ} {AnsY : NonStar Bᴿ}
  → Z ≢ X
  → (CTX.CenterAligned W X Y₂ → ⊥)
  → (CTX.CenterAligned W Z Y₂ → ⊥)
  → CTX.Rep★PartnerOK W X
      ((P ↓ seal Z ★)
        ⟨ _! {G = ＇ Z} ⦃ Gᵍ = ＇ Z ⦄
            ⦃ G∼★ = Z∼★ ⦄ cZ ⦃ Ans = AnsZ ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
different-name-round-trip-no-launder₈ Z≢X not-outer
    not-wrapper (CTX.rep★-untagged ())
different-name-round-trip-no-launder₈ Z≢X not-outer
    not-wrapper (CTX.rep★-nonvar-tag ())
different-name-round-trip-no-launder₈ Z≢X not-outer
    not-wrapper (CTX.rep★-var-tag aligned) =
  not-outer aligned
different-name-round-trip-no-launder₈ Z≢X not-outer
    not-wrapper (CTX.rep★-matched-inner-tags Z≢X′ aligned) =
  not-wrapper aligned
different-name-round-trip-no-launder₈ Z≢X not-outer
    not-wrapper (CTX.rep★-round-trip ok) =
  Z≢X refl

non-rep★-round-trip-no-launder₈ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Y₂ : TyVar Δᴿ} {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {R Aˣ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Bᴿ}
  → NonStar R
  → (CTX.CenterAligned W X Y₂ → ⊥)
  → CTX.Rep★PartnerOK W X
      ((P ↓ seal X R)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
non-rep★-round-trip-no-launder₈ Rns not-aligned
    (CTX.rep★-untagged ())
non-rep★-round-trip-no-launder₈ Rns not-aligned
    (CTX.rep★-nonvar-tag ())
non-rep★-round-trip-no-launder₈ Rns not-aligned
    (CTX.rep★-var-tag aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₈ Rns not-aligned
    (CTX.rep★-matched-inner-tags X≢X aligned) =
  X≢X refl
non-rep★-round-trip-no-launder₈ () not-aligned
    (CTX.rep★-round-trip ok)

------------------------------------------------------------------------
-- Concrete round-15/InstanceB package remains closed
------------------------------------------------------------------------

round15-counterexample-stays-closed₈ :
  TaggedTransferOutput₈ B.W [] SSC.source-output-tag SSC.target-tag
    B.X (just B.Y₂)
  → ⊥
round15-counterexample-stays-closed₈ pkg =
  wrong-pedigree-package-empty₈
    (CTX.RebaseAt.pivotAligned B.rb-X-Y)
    (λ Y₂≡Y → SSC.Y≢Y₂ (sym Y₂≡Y))
    pkg

round15-live-output-partner-still-empty₈ :
  CTX.Rep★PartnerOK B.W B.X SSC.source-output-tag
    (just B.Y₂) SSC.target-tag
  → ⊥
round15-live-output-partner-still-empty₈ =
  SSC.no-output-partner
