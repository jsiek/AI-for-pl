module Tighten7PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 7.
-- Purpose: model the anchored recursive round-trip candidate, check the
-- round-16 source-seal sub-head, and test whether the round-6 laundering
-- attacks stay closed.
-- Primary exports: the `₇` partner predicates, the round-16 sub-head model,
-- transport sketches, laundering witnesses/refutations, and the concrete
-- InstanceB package test.
-- Key dependencies: SealTransferCore for the disciplined live inner
-- transport subset, CastTermImprecision2 for live worlds/rules, and
-- SourceStarPackageCounterScratch for the round-15 negative instance.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≢_; _≡_; refl; sym; trans)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!; toRenameᵗ)
open import CastTerms using (Term; Inert; _⟨_⟩; _↓_)
open import Conversion using (Conv↑; Conv↓; seal; _↦↓_; `∀↓_; id↓)
open import Imprecision

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealTransferCore as STC
import proof.DGG.TerminusRebuildProbe as TRP
import SourceStarPackageCounterScratch as SSC

module B = TRP.InstanceB

open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Anchored rep-★ partner predicate model
------------------------------------------------------------------------

data Rep★PartnerOK₇ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged₇ : ∀ {P Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → Rep★PartnerOK₇ W X P Xᴿ? M′

  rep★-nonvar-tag₇ : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK₇ W X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-var-tag₇ : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CTI2.CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK₇ W X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags₇ : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → X₂ ≢ X
    → CTI2.CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → Rep★PartnerOK₇ W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

  rep★-round-trip-just₇ : ∀ {P Y Yᵖ M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → CTI2.CenterAligned W X Yᵖ
    → Rep★PartnerOK₇ W X P (just Yᵖ) M′
      ------------------------------------------------------------
    → Rep★PartnerOK₇ W X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y) M′

  rep★-round-trip-nothing₇ : ∀ {P M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → Rep★PartnerOK₇ W X P nothing M′
      ------------------------------------------------------------
    → Rep★PartnerOK₇ W X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        nothing M′

data SealPartnerOK₇ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target₇ : ∀ {P Xᴿ? M′}
    → Rep★PartnerOK₇ W X P Xᴿ? M′
      ------------------------------------
    → SealPartnerOK₇ W X P ★ Xᴿ? M′

  plain-target₇ : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → SealPartnerOK₇ W X P R Xᴿ? M′

  name-protected-target₇ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      ----------------------------------------------------
    → SealPartnerOK₇ W X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOK₇ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok₇ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOK₇ W X P R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOK₇ W P (seal X R) Xᴿ? M′

  fun-conceal-target₇ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₇ W P (c ↦↓ d) Xᴿ? M′

  all-conceal-target₇ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOK₇ W P (`∀↓ c) Xᴿ? M′

  id-conceal-target₇ : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₇ W P (id↓ A) Xᴿ? M′

data MatchedConcealPartnerOK₇ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → TyVar Δᴿ → Term Δᴿ → Set where
  matched-seal-star-partner₇ : ∀ {P X Y M′}
    → Rep★PartnerOK₇ W X P (just Y) M′
      ----------------------------------------------------
    → MatchedConcealPartnerOK₇ W P (seal X ★) Y M′

  matched-seal-nonstar₇ : ∀ {P X R Y M′}
    → NonStar R
      ----------------------------------------------------
    → MatchedConcealPartnerOK₇ W P (seal X R) Y M′

  matched-fun-conceal-target₇ : ∀ {P A A′ B B′ Y M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₇ W P (c ↦↓ d) Y M′

  matched-all-conceal-target₇ : ∀ {P A B Y M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₇ W P (`∀↓ c) Y M′

  matched-id-conceal-target₇ : ∀ {P A Y M′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₇ W P (id↓ A) Y M′

------------------------------------------------------------------------
-- Disciplined live inner subset, transport, and conceal-surface mirror
------------------------------------------------------------------------

fromLiveRep★PartnerOK-just : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P M′}
  → CTI2.CenterAligned W X Y
  → CTI2.Rep★PartnerOK W X P (just Y) M′
  → Rep★PartnerOK₇ W X P (just Y) M′
fromLiveRep★PartnerOK-just aligned (CTI2.rep★-untagged nt) =
  rep★-untagged₇ nt
fromLiveRep★PartnerOK-just aligned (CTI2.rep★-nonvar-tag Gnv) =
  rep★-nonvar-tag₇ Gnv
fromLiveRep★PartnerOK-just aligned (CTI2.rep★-var-tag aligned′) =
  rep★-var-tag₇ aligned′
fromLiveRep★PartnerOK-just aligned
    (CTI2.rep★-matched-inner-tags X₂≢X aligned′) =
  rep★-matched-inner-tags₇ X₂≢X aligned′
fromLiveRep★PartnerOK-just aligned (CTI2.rep★-round-trip ok) =
  rep★-round-trip-just₇ aligned
    (fromLiveRep★PartnerOK-just aligned ok)

fromLiveRep★PartnerOK-nothing : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {P M′}
  → CTI2.Rep★PartnerOK W X P nothing M′
  → Rep★PartnerOK₇ W X P nothing M′
fromLiveRep★PartnerOK-nothing (CTI2.rep★-untagged nt) =
  rep★-untagged₇ nt
fromLiveRep★PartnerOK-nothing (CTI2.rep★-nonvar-tag Gnv) =
  rep★-nonvar-tag₇ Gnv
fromLiveRep★PartnerOK-nothing (CTI2.rep★-round-trip ok) =
  rep★-round-trip-nothing₇ (fromLiveRep★PartnerOK-nothing ok)

transport-non-pivot-aligned₇ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → X₂ ≢ X
  → CTI2.CenterAligned Wᵖ X₂ Y₂
  → CTI2.CenterAligned W X₂ Y₂
transport-non-pivot-aligned₇ rb X₂≢X aligned =
  trans (CTI2.RebaseAt.ηᴸ-off-pivot rb X₂≢X)
    (trans aligned (sym (CTI2.RebaseAt.ηᴿ-frozen rb _)))

transportRep★PartnerOK-nothing₇ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {M′ : Term Δᴿ}
  → RebaseAt Wᵖ W X Y
  → Rep★PartnerOK₇ Wᵖ X P nothing M′
  → Rep★PartnerOK₇ W X P nothing M′
transportRep★PartnerOK-nothing₇ rb (rep★-untagged₇ nt) =
  rep★-untagged₇ nt
transportRep★PartnerOK-nothing₇ rb (rep★-nonvar-tag₇ Gnv) =
  rep★-nonvar-tag₇ Gnv
transportRep★PartnerOK-nothing₇ rb
    (rep★-round-trip-nothing₇ ok) =
  rep★-round-trip-nothing₇ (transportRep★PartnerOK-nothing₇ rb ok)

source-round-trip-seal-star₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Yᵖ : TyVar Δᴿ}
    {P M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → CTI2.CenterAligned W X Yᵖ
  → Rep★PartnerOK₇ W X P (just Yᵖ) M′
  → SourceConcealPartnerOK₇ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) (just Y) M′
source-round-trip-seal-star₇ aligned ok =
  seal-partner-ok₇
    (star-rep-target₇ (rep★-round-trip-just₇ aligned ok))

source-round-trip-seal-star-nothing₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₇ W X P nothing M′
  → SourceConcealPartnerOK₇ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) nothing M′
source-round-trip-seal-star-nothing₇ ok =
  seal-partner-ok₇
    (star-rep-target₇ (rep★-round-trip-nothing₇ ok))

matched-round-trip-seal-star₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y Yᵖ : TyVar Δᴿ}
    {P M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → CTI2.CenterAligned W X Yᵖ
  → Rep★PartnerOK₇ W X P (just Yᵖ) M′
  → MatchedConcealPartnerOK₇ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y M′
matched-round-trip-seal-star₇ aligned ok =
  matched-seal-star-partner₇ (rep★-round-trip-just₇ aligned ok)

round16-source-seal-subhead₇ : ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ W₀ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Yᵖ Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {A μ} {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → RebaseAt W₃ W₂ X Yᵖ
  → RebaseAt W₂ W₀ X Y
  → CTI2.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → SourceConcealPartnerOK₇ W₂
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) (just Y) U
round16-source-seal-subhead₇ rbᵖ link partner =
  seal-partner-ok₇
    (star-rep-target₇
      (rep★-round-trip-just₇ (CTI2.RebaseAt.pivotAligned rbᵖ)
        (fromLiveRep★PartnerOK-just
          (CTI2.RebaseAt.pivotAligned rbᵖ)
          (STC.transport-rep★-partner-ok rbᵖ partner))))

------------------------------------------------------------------------
-- Laundering battery
------------------------------------------------------------------------

bare-payload-var-tag-mismatch-empty₇ : ∀ {Δᴸ Δᴿ Δ}
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
  → (CTI2.CenterAligned W X Y₂ → ⊥)
  → Rep★PartnerOK₇ W X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₇ not-inner not-roundtrip
    not-aligned (rep★-untagged₇ ())
bare-payload-var-tag-mismatch-empty₇ not-inner not-roundtrip
    not-aligned (rep★-nonvar-tag₇ ())
bare-payload-var-tag-mismatch-empty₇ not-inner not-roundtrip
    not-aligned (rep★-var-tag₇ aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₇ not-inner not-roundtrip
    not-aligned (rep★-matched-inner-tags₇ X₂≢X aligned) =
  not-inner refl
bare-payload-var-tag-mismatch-empty₇ not-inner not-roundtrip
    not-aligned (rep★-round-trip-just₇ aligned ok) =
  not-roundtrip refl

different-name-round-trip-no-launder₇ : ∀ {Δᴸ Δᴿ Δ}
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
  → (CTI2.CenterAligned W X Y₂ → ⊥)
  → (CTI2.CenterAligned W Z Y₂ → ⊥)
  → Rep★PartnerOK₇ W X
      ((P ↓ seal Z ★)
        ⟨ _! {G = ＇ Z} ⦃ Gᵍ = ＇ Z ⦄
            ⦃ G∼★ = Z∼★ ⦄ cZ ⦃ Ans = AnsZ ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
different-name-round-trip-no-launder₇ Z≢X not-outer
    not-wrapper (rep★-untagged₇ ())
different-name-round-trip-no-launder₇ Z≢X not-outer
    not-wrapper (rep★-nonvar-tag₇ ())
different-name-round-trip-no-launder₇ Z≢X not-outer
    not-wrapper (rep★-var-tag₇ aligned) =
  not-outer aligned
different-name-round-trip-no-launder₇ Z≢X not-outer
    not-wrapper (rep★-matched-inner-tags₇ Z≢X′ aligned) =
  not-wrapper aligned
different-name-round-trip-no-launder₇ Z≢X not-outer
    not-wrapper (rep★-round-trip-just₇ aligned ok) =
  Z≢X refl

non-rep★-round-trip-no-launder₇ : ∀ {Δᴸ Δᴿ Δ}
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
  → (CTI2.CenterAligned W X Y₂ → ⊥)
  → Rep★PartnerOK₇ W X
      ((P ↓ seal X R)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
non-rep★-round-trip-no-launder₇ Rns not-aligned
    (rep★-untagged₇ ())
non-rep★-round-trip-no-launder₇ Rns not-aligned
    (rep★-nonvar-tag₇ ())
non-rep★-round-trip-no-launder₇ Rns not-aligned
    (rep★-var-tag₇ aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₇ Rns not-aligned
    (rep★-matched-inner-tags₇ X≢X aligned) =
  X≢X refl
non-rep★-round-trip-no-launder₇ () not-aligned
    (rep★-round-trip-just₇ aligned ok)

wrong-pedigree-round-trip-launder₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTI2.CenterAligned W X Yᵢ
  → Rep★PartnerOK₇ W X
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
wrong-pedigree-round-trip-launder₇ aligned =
  rep★-round-trip-just₇ aligned (rep★-var-tag₇ aligned)

var-tag-no-target-empty₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Yᵢ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₇ W X P nothing
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty₇ (rep★-untagged₇ ())
var-tag-no-target-empty₇ (rep★-nonvar-tag₇ ())
var-tag-no-target-empty₇ (rep★-round-trip-nothing₇ ok) =
  var-tag-no-target-empty₇ ok

source-seal-var-tag-no-target-empty₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Yᵢ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsY : NonStar Aᴿ}
  → SourceConcealPartnerOK₇ W P (seal X ★) nothing
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-empty₇
    (seal-partner-ok₇ (star-rep-target₇ ok)) =
  var-tag-no-target-empty₇ ok
source-seal-var-tag-no-target-empty₇
    (seal-partner-ok₇ (plain-target₇ ()))

wrong-pedigree-matched-conceal₇ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTI2.CenterAligned W X Yᵢ
  → MatchedConcealPartnerOK₇ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Yᵒ
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
wrong-pedigree-matched-conceal₇ aligned =
  matched-seal-star-partner₇
    (wrong-pedigree-round-trip-launder₇ aligned)

------------------------------------------------------------------------
-- Concrete round-15/InstanceB reopening
------------------------------------------------------------------------

record TaggedTransferOutput₇ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where
  constructor tagged-transfer-output₇
  field
    premise₇ : W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    partner₇ : MatchedConcealPartnerOK₇ W P (seal X ★) Y U

instanceB-no-target-empty₇ :
  Rep★PartnerOK₇ B.W B.X SSC.source-output-tag nothing SSC.target-tag
  → ⊥
instanceB-no-target-empty₇ = var-tag-no-target-empty₇

instanceB-source-seal-no-target-empty₇ :
  SourceConcealPartnerOK₇ B.W SSC.source-output-tag
    (seal B.X ★) nothing SSC.target-tag
  → ⊥
instanceB-source-seal-no-target-empty₇ =
  source-seal-var-tag-no-target-empty₇

round15-counterexample-package₇ :
  TaggedTransferOutput₇ B.W [] SSC.source-output-tag SSC.target-tag
    B.X B.Y₂
round15-counterexample-package₇ =
  tagged-transfer-output₇
    (CTI2.cast⊑² B.X! SSC.counter-premise ★⊑★)
    (matched-seal-star-partner₇
      (rep★-round-trip-just₇ {P = SSC.source-tag}
        (CTI2.RebaseAt.pivotAligned B.rb-X-Y)
        (rep★-var-tag₇ (CTI2.RebaseAt.pivotAligned B.rb-X-Y))))
