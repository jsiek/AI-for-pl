module Tighten6PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 6.
-- Purpose: model the candidate that frees the recursive round-trip
-- target pedigree, check the round-16 source-seal sub-head, and test the
-- laundering/no-target payoff surface.
-- Primary exports: the `₆` partner predicates, the round-16 sub-head model,
-- pass/fail laundering witnesses, and a concrete InstanceB package reopened
-- by the freed clause.
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

import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.SealTransferCore as STC
import proof.DGG.TerminusRebuildProbe as TRP
import SourceStarPackageCounterScratch as SSC

module B = TRP.InstanceB

open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Freed rep-★ partner predicate model
------------------------------------------------------------------------

data Rep★PartnerOK₆ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged₆ : ∀ {P Xᴿ? M′}
    → CTX.NotTopTag M′
      ------------------------------------
    → Rep★PartnerOK₆ W X P Xᴿ? M′

  rep★-nonvar-tag₆ : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK₆ W X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-var-tag₆ : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CTX.CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK₆ W X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags₆ : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → X₂ ≢ X
    → CTX.CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → Rep★PartnerOK₆ W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

  rep★-round-trip₆ : ∀ {P Xᴿ? Xᴿ?ᵢ M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → Rep★PartnerOK₆ W X P Xᴿ?ᵢ M′
      ------------------------------------------------------------
    → Rep★PartnerOK₆ W X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        Xᴿ? M′

data SealPartnerOK₆ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target₆ : ∀ {P Xᴿ? M′}
    → Rep★PartnerOK₆ W X P Xᴿ? M′
      ------------------------------------
    → SealPartnerOK₆ W X P ★ Xᴿ? M′

  plain-target₆ : ∀ {P R Xᴿ? M′}
    → CTX.NotTopTag M′
      ------------------------------------
    → SealPartnerOK₆ W X P R Xᴿ? M′

  name-protected-target₆ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      ----------------------------------------------------
    → SealPartnerOK₆ W X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOK₆ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok₆ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOK₆ W X P R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOK₆ W P (seal X R) Xᴿ? M′

  fun-conceal-target₆ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₆ W P (c ↦↓ d) Xᴿ? M′

  all-conceal-target₆ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOK₆ W P (`∀↓ c) Xᴿ? M′

  id-conceal-target₆ : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₆ W P (id↓ A) Xᴿ? M′

data MatchedConcealPartnerOK₆ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → TyVar Δᴿ → Term Δᴿ → Set where
  matched-seal-star-partner₆ : ∀ {P X Y M′}
    → Rep★PartnerOK₆ W X P (just Y) M′
      ----------------------------------------------------
    → MatchedConcealPartnerOK₆ W P (seal X ★) Y M′

  matched-seal-nonstar₆ : ∀ {P X R Y M′}
    → NonStar R
      ----------------------------------------------------
    → MatchedConcealPartnerOK₆ W P (seal X R) Y M′

  matched-fun-conceal-target₆ : ∀ {P A A′ B B′ Y M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₆ W P (c ↦↓ d) Y M′

  matched-all-conceal-target₆ : ∀ {P A B Y M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₆ W P (`∀↓ c) Y M′

  matched-id-conceal-target₆ : ∀ {P A Y M′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₆ W P (id↓ A) Y M′

------------------------------------------------------------------------
-- Disciplined live inner subset and conceal-surface mirror
------------------------------------------------------------------------

fromLiveRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {P Xᴿ? M′}
  → CTX.Rep★PartnerOK W X P Xᴿ? M′
  → Rep★PartnerOK₆ W X P Xᴿ? M′
fromLiveRep★PartnerOK (CTX.rep★-untagged nt) =
  rep★-untagged₆ nt
fromLiveRep★PartnerOK (CTX.rep★-nonvar-tag Gnv) =
  rep★-nonvar-tag₆ Gnv
fromLiveRep★PartnerOK (CTX.rep★-var-tag aligned) =
  rep★-var-tag₆ aligned
fromLiveRep★PartnerOK (CTX.rep★-matched-inner-tags X₂≢X aligned) =
  rep★-matched-inner-tags₆ X₂≢X aligned
fromLiveRep★PartnerOK (CTX.rep★-round-trip ok) =
  rep★-round-trip₆ (fromLiveRep★PartnerOK ok)

source-round-trip-seal-star₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P Xᴿ? Xᴿ?ᵢ M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₆ W X P Xᴿ?ᵢ M′
  → SourceConcealPartnerOK₆ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Xᴿ? M′
source-round-trip-seal-star₆ ok =
  seal-partner-ok₆ (star-rep-target₆ (rep★-round-trip₆ ok))

matched-round-trip-seal-star₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P Xᴿ?ᵢ M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₆ W X P Xᴿ?ᵢ M′
  → MatchedConcealPartnerOK₆ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y M′
matched-round-trip-seal-star₆ ok =
  matched-seal-star-partner₆ (rep★-round-trip₆ ok)

round16-source-seal-subhead₆ : ∀ {Δᴸ Δᴿ Δ}
    {W₃ W₂ W₀ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Yᵖ Y : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {A μ} {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → RebaseAt W₃ W₂ X Yᵖ
  → RebaseAt W₂ W₀ X Y
  → CTX.Rep★PartnerOK W₃ X P (just Yᵖ) U
  → SourceConcealPartnerOK₆ W₂
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) (just Y) U
round16-source-seal-subhead₆ rbᵖ link partner =
  seal-partner-ok₆
    (star-rep-target₆
      (rep★-round-trip₆ {Xᴿ?ᵢ = just _}
        (fromLiveRep★PartnerOK
          (STC.transport-rep★-partner-ok rbᵖ partner))))

------------------------------------------------------------------------
-- Laundering battery
------------------------------------------------------------------------

bare-payload-var-tag-mismatch-empty₆ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₆ W X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₆ not-inner not-roundtrip
    not-aligned (rep★-untagged₆ ())
bare-payload-var-tag-mismatch-empty₆ not-inner not-roundtrip
    not-aligned (rep★-nonvar-tag₆ ())
bare-payload-var-tag-mismatch-empty₆ not-inner not-roundtrip
    not-aligned (rep★-var-tag₆ aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₆ not-inner not-roundtrip
    not-aligned (rep★-matched-inner-tags₆ X₂≢X aligned) =
  not-inner refl
bare-payload-var-tag-mismatch-empty₆ not-inner not-roundtrip
    not-aligned (rep★-round-trip₆ ok) =
  not-roundtrip refl

different-name-round-trip-no-launder₆ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₆ W X
      ((P ↓ seal Z ★)
        ⟨ _! {G = ＇ Z} ⦃ Gᵍ = ＇ Z ⦄
            ⦃ G∼★ = Z∼★ ⦄ cZ ⦃ Ans = AnsZ ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
different-name-round-trip-no-launder₆ Z≢X not-outer
    not-wrapper (rep★-untagged₆ ())
different-name-round-trip-no-launder₆ Z≢X not-outer
    not-wrapper (rep★-nonvar-tag₆ ())
different-name-round-trip-no-launder₆ Z≢X not-outer
    not-wrapper (rep★-var-tag₆ aligned) =
  not-outer aligned
different-name-round-trip-no-launder₆ Z≢X not-outer
    not-wrapper (rep★-matched-inner-tags₆ Z≢X′ aligned) =
  not-wrapper aligned
different-name-round-trip-no-launder₆ Z≢X not-outer
    not-wrapper (rep★-round-trip₆ ok) =
  Z≢X refl

non-rep★-round-trip-no-launder₆ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₆ W X
      ((P ↓ seal X R)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
non-rep★-round-trip-no-launder₆ Rns not-aligned
    (rep★-untagged₆ ())
non-rep★-round-trip-no-launder₆ Rns not-aligned
    (rep★-nonvar-tag₆ ())
non-rep★-round-trip-no-launder₆ Rns not-aligned
    (rep★-var-tag₆ aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₆ Rns not-aligned
    (rep★-matched-inner-tags₆ X≢X aligned) =
  X≢X refl
non-rep★-round-trip-no-launder₆ () not-aligned
    (rep★-round-trip₆ ok)

wrong-pedigree-round-trip-launder₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTX.CenterAligned W X Yᵢ
  → Rep★PartnerOK₆ W X
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
wrong-pedigree-round-trip-launder₆ aligned =
  rep★-round-trip₆ (rep★-var-tag₆ aligned)

var-tag-no-target-launder₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTX.CenterAligned W X Yᵢ
  → Rep★PartnerOK₆ W X
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      nothing
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
var-tag-no-target-launder₆ aligned =
  rep★-round-trip₆ (rep★-var-tag₆ aligned)

source-seal-var-tag-no-target-launder₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTX.CenterAligned W X Yᵢ
  → SourceConcealPartnerOK₆ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) nothing
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
source-seal-var-tag-no-target-launder₆ aligned =
  seal-partner-ok₆
    (star-rep-target₆ (var-tag-no-target-launder₆ aligned))

wrong-pedigree-matched-conceal₆ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Yᵢ : TyVar Δᴿ} {P : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Yᵢ∼★ : μᴿ ⊢ (＇ Yᵢ) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Yᵢ}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Aᴿ}
  → CTX.CenterAligned W X Yᵢ
  → MatchedConcealPartnerOK₆ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Yᵒ
      (U ⟨ _! {G = ＇ Yᵢ} ⦃ Gᵍ = ＇ Yᵢ ⦄
            ⦃ G∼★ = Yᵢ∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
wrong-pedigree-matched-conceal₆ aligned =
  matched-seal-star-partner₆
    (wrong-pedigree-round-trip-launder₆ aligned)

------------------------------------------------------------------------
-- Concrete round-15/InstanceB reopening
------------------------------------------------------------------------

record TaggedTransferOutput₆ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where
  constructor tagged-transfer-output₆
  field
    premise₆ : W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    partner₆ : MatchedConcealPartnerOK₆ W P (seal X ★) Y U

instanceB-no-target-launder₆ :
  Rep★PartnerOK₆ B.W B.X SSC.source-output-tag nothing SSC.target-tag
instanceB-no-target-launder₆ =
  rep★-round-trip₆ {P = SSC.source-tag} {Xᴿ? = nothing}
    {Xᴿ?ᵢ = just B.Y}
    (rep★-var-tag₆ (CTX.RebaseAt.pivotAligned B.rb-X-Y))

instanceB-source-seal-no-target-launder₆ :
  SourceConcealPartnerOK₆ B.W SSC.source-output-tag
    (seal B.X ★) nothing SSC.target-tag
instanceB-source-seal-no-target-launder₆ =
  seal-partner-ok₆ (star-rep-target₆ instanceB-no-target-launder₆)

round15-counterexample-package₆ :
  TaggedTransferOutput₆ B.W [] SSC.source-output-tag SSC.target-tag
    B.X B.Y₂
round15-counterexample-package₆ =
  tagged-transfer-output₆
    (CTI2.cast⊑² B.X! SSC.counter-premise ★⊑★)
    (matched-seal-star-partner₆
      (rep★-round-trip₆ {P = SSC.source-tag}
        {Xᴿ? = just B.Y₂} {Xᴿ?ᵢ = just B.Y}
        (rep★-var-tag₆ (CTX.RebaseAt.pivotAligned B.rb-X-Y))))
