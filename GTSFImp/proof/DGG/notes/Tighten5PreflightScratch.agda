module Tighten5PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 5.
-- Purpose: model the orthogonalized partner clauses where matched inner tags
-- carry a non-pivot source proof, prove source-pivot transport, and package the
-- target-chain paired-seal emission in one common world.
-- Primary exports: the `₅` partner predicates, transport lemmas, round-13
-- same-pivot/non-pivot witnesses, payoff/exclusion lemmas, and the erased live
-- emission shape.
-- Key dependencies: CastTermImprecision2 for live worlds/rules,
-- TermImpDecay/SealPeelToolkit for the dyn-decayed rebase shape, and the
-- existing conversion/cast-term syntax.

open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality
  using (_≢_; _≡_; refl; sym; trans)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!; toRenameᵗ)
open import CastTerms using (Term; Inert; _⟨_⟩; _↓_)
open import Conversion using (Conv↑; Conv↓; seal; _↦↓_; `∀↓_; id↓)
import Conversion
open import Imprecision

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.SealPeelToolkit as SPT
import proof.DGG.TermImpDecay as TD

open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_; _⊢↓[_]_)

------------------------------------------------------------------------
-- Orthogonalized rep-★ partner predicate model
------------------------------------------------------------------------

data Rep★PartnerOK₅ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged₅ : ∀ {P Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → Rep★PartnerOK₅ W X P Xᴿ? M′

  rep★-nonvar-tag₅ : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK₅ W X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-var-tag₅ : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CTI2.CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK₅ W X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags₅ : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → X₂ ≢ X
    → CTI2.CenterAligned W X₂ Y₂
      ------------------------------------------------------------
    → Rep★PartnerOK₅ W X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

  rep★-round-trip₅ : ∀ {P Xᴿ? M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → Rep★PartnerOK₅ W X P Xᴿ? M′
      ------------------------------------------------------------
    → Rep★PartnerOK₅ W X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        Xᴿ? M′

data SealPartnerOK₅ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target₅ : ∀ {P Xᴿ? M′}
    → Rep★PartnerOK₅ W X P Xᴿ? M′
      ------------------------------------
    → SealPartnerOK₅ W X P ★ Xᴿ? M′

  plain-target₅ : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      ------------------------------------
    → SealPartnerOK₅ W X P R Xᴿ? M′

  name-protected-target₅ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      ----------------------------------------------------
    → SealPartnerOK₅ W X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOK₅ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok₅ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOK₅ W X P R Xᴿ? M′
      ----------------------------------------------------
    → SourceConcealPartnerOK₅ W P (seal X R) Xᴿ? M′

  fun-conceal-target₅ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₅ W P (c ↦↓ d) Xᴿ? M′

  all-conceal-target₅ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → SourceConcealPartnerOK₅ W P (`∀↓ c) Xᴿ? M′

  id-conceal-target₅ : ∀ {P A Xᴿ? M′}
      ----------------------------------------------------
    → SourceConcealPartnerOK₅ W P (id↓ A) Xᴿ? M′

data MatchedConcealPartnerOK₅ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → TyVar Δᴿ → Term Δᴿ → Set where
  matched-seal-star-partner₅ : ∀ {P X Y M′}
    → Rep★PartnerOK₅ W X P (just Y) M′
      ----------------------------------------------------
    → MatchedConcealPartnerOK₅ W P (seal X ★) Y M′

  matched-seal-nonstar₅ : ∀ {P X R Y M′}
    → NonStar R
      ----------------------------------------------------
    → MatchedConcealPartnerOK₅ W P (seal X R) Y M′

  matched-fun-conceal-target₅ : ∀ {P A A′ B B′ Y M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₅ W P (c ↦↓ d) Y M′

  matched-all-conceal-target₅ : ∀ {P A B Y M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₅ W P (`∀↓ c) Y M′

  matched-id-conceal-target₅ : ∀ {P A Y M′}
      ----------------------------------------------------
    → MatchedConcealPartnerOK₅ W P (id↓ A) Y M′

------------------------------------------------------------------------
-- Erasure back to the current live relation shape
------------------------------------------------------------------------

eraseRep★PartnerOK₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {P Xᴿ? M′}
  → Rep★PartnerOK₅ W X P Xᴿ? M′
  → CTI2.Rep★PartnerOK W X P Xᴿ? M′
eraseRep★PartnerOK₅ (rep★-untagged₅ nt) =
  CTI2.rep★-untagged nt
eraseRep★PartnerOK₅ (rep★-nonvar-tag₅ Gnv) =
  CTI2.rep★-nonvar-tag Gnv
eraseRep★PartnerOK₅ (rep★-var-tag₅ aligned) =
  CTI2.rep★-var-tag aligned
eraseRep★PartnerOK₅ (rep★-matched-inner-tags₅ X₂≢X aligned) =
  CTI2.rep★-matched-inner-tags aligned
eraseRep★PartnerOK₅ (rep★-round-trip₅ ok) =
  CTI2.rep★-round-trip (eraseRep★PartnerOK₅ ok)

eraseSealPartnerOK₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → SealPartnerOK₅ W X P R Xᴿ? M′
  → CTI2.SealPartnerOK W X P R Xᴿ? M′
eraseSealPartnerOK₅ (star-rep-target₅ ok) =
  CTI2.star-rep-target (eraseRep★PartnerOK₅ ok)
eraseSealPartnerOK₅ (plain-target₅ nt) =
  CTI2.plain-target nt
eraseSealPartnerOK₅ name-protected-target₅ =
  CTI2.name-protected-target

eraseSourceConcealPartnerOK₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → SourceConcealPartnerOK₅ W M c Xᴿ? M′
  → CTI2.SourceConcealPartnerOK W M c Xᴿ? M′
eraseSourceConcealPartnerOK₅ (seal-partner-ok₅ ok) =
  CTI2.seal-partner-ok (eraseSealPartnerOK₅ ok)
eraseSourceConcealPartnerOK₅ fun-conceal-target₅ =
  CTI2.fun-conceal-target
eraseSourceConcealPartnerOK₅ all-conceal-target₅ =
  CTI2.all-conceal-target
eraseSourceConcealPartnerOK₅ id-conceal-target₅ =
  CTI2.id-conceal-target

eraseMatchedConcealPartnerOK₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Y M′}
  → MatchedConcealPartnerOK₅ W M c Y M′
  → CTI2.MatchedConcealPartnerOK W M c Y M′
eraseMatchedConcealPartnerOK₅ (matched-seal-star-partner₅ ok) =
  CTI2.matched-seal-star-partner (eraseRep★PartnerOK₅ ok)
eraseMatchedConcealPartnerOK₅ (matched-seal-nonstar₅ Rns) =
  CTI2.matched-seal-nonstar Rns
eraseMatchedConcealPartnerOK₅ matched-fun-conceal-target₅ =
  CTI2.matched-fun-conceal-target
eraseMatchedConcealPartnerOK₅ matched-all-conceal-target₅ =
  CTI2.matched-all-conceal-target
eraseMatchedConcealPartnerOK₅ matched-id-conceal-target₅ =
  CTI2.matched-id-conceal-target

------------------------------------------------------------------------
-- Source-pivot transport
------------------------------------------------------------------------

transport-non-pivot-aligned₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → X₂ ≢ X
  → CTI2.CenterAligned Wᵖ X₂ Y₂
  → CTI2.CenterAligned W X₂ Y₂
transport-non-pivot-aligned₅ rb X₂≢X aligned =
  trans (CTI2.RebaseAt.ηᴸ-off-pivot rb X₂≢X)
    (trans aligned (sym (CTI2.RebaseAt.ηᴿ-frozen rb _)))

transportRep★PartnerOK₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {M′ : Term Δᴿ}
  → RebaseAt Wᵖ W X Y
  → Rep★PartnerOK₅ Wᵖ X P (just Y) M′
  → Rep★PartnerOK₅ W X P (just Y) M′
transportRep★PartnerOK₅ rb (rep★-untagged₅ nt) =
  rep★-untagged₅ nt
transportRep★PartnerOK₅ rb (rep★-nonvar-tag₅ Gnv) =
  rep★-nonvar-tag₅ Gnv
transportRep★PartnerOK₅ rb (rep★-var-tag₅ aligned) =
  rep★-var-tag₅ (CTI2.RebaseAt.pivotAligned rb)
transportRep★PartnerOK₅ rb
    (rep★-matched-inner-tags₅ X₂≢X aligned) =
  rep★-matched-inner-tags₅ X₂≢X
    (transport-non-pivot-aligned₅ rb X₂≢X aligned)
transportRep★PartnerOK₅ rb (rep★-round-trip₅ ok) =
  rep★-round-trip₅ (transportRep★PartnerOK₅ rb ok)

transportRep★PartnerOK-dyn₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P : Term Δᴸ} {M′ : Term Δᴿ}
  → RebaseAt Wᵖ W X Y
  → Rep★PartnerOK₅ (SPT.dynWorld Wᵖ) X P (just Y) M′
  → Rep★PartnerOK₅ (SPT.dynWorld W) X P (just Y) M′
transportRep★PartnerOK-dyn₅ {Wᵖ = Wᵖ} {W = W} rb ok =
  transportRep★PartnerOK₅
    (TD.decayRebaseAt (SPT.dynWorld-decay Wᵖ)
      (SPT.dynWorld-decay W) rb)
    ok

source-round-trip-seal-star₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P Xᴿ? M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₅ W X P Xᴿ? M′
  → SourceConcealPartnerOK₅ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Xᴿ? M′
source-round-trip-seal-star₅ ok =
  seal-partner-ok₅ (star-rep-target₅ (rep★-round-trip₅ ok))

matched-round-trip-seal-star₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₅ W X P (just Y) M′
  → MatchedConcealPartnerOK₅ W
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y M′
matched-round-trip-seal-star₅ ok =
  matched-seal-star-partner₅ (rep★-round-trip₅ ok)

------------------------------------------------------------------------
-- Round-13 blocked head: same-pivot through round-trip, non-pivot transport
------------------------------------------------------------------------

same-pivot-value-round-trip₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {V₂ P₀ : Term Δᴸ} {U : Term Δᴿ}
    {A μ} {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → V₂ ≡ P₀ ↓ seal X ★
  → Rep★PartnerOK₅ W X P₀ (just Y) U
  → Rep★PartnerOK₅ W X
      (V₂ ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y) U
same-pivot-value-round-trip₅ refl ok =
  rep★-round-trip₅ ok

round13-same-pivot-matched-conceal₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {V₂ P₀ : Term Δᴸ} {U : Term Δᴿ}
    {A μ} {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → RebaseAt Wᵖ W X Y
  → V₂ ≡ P₀ ↓ seal X ★
  → Rep★PartnerOK₅ Wᵖ X P₀ (just Y) U
  → MatchedConcealPartnerOK₅ W
      (V₂ ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y U
round13-same-pivot-matched-conceal₅ rb refl ok =
  matched-seal-star-partner₅
    (transportRep★PartnerOK₅ rb (rep★-round-trip₅ ok))

round13-non-pivot-matched-conceal₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ Aᴿ μᴸ μᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → RebaseAt Wᵖ W X Y
  → X₂ ≢ X
  → CTI2.CenterAligned Wᵖ X₂ Y₂
  → MatchedConcealPartnerOK₅ W
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
round13-non-pivot-matched-conceal₅ rb X₂≢X aligned =
  matched-seal-star-partner₅
    (transportRep★PartnerOK₅ rb
      (rep★-matched-inner-tags₅ X₂≢X aligned))

------------------------------------------------------------------------
-- One-common-world package and live paired-seal emission shape
------------------------------------------------------------------------

record TaggedTransferOutput₅ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (X : TyVar Δᴸ) (Y : TyVar Δᴿ) : Set where
  constructor tagged-transfer-output₅
  field
    premise₅ : W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
    partner₅ : MatchedConcealPartnerOK₅ W P (seal X ★) Y U

tagged-transfer-output-from-transport₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W₂ : World Δᴸ Δᴿ Δ} {γ₂ : CtxImp W₂}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W₂ X Y
  → Rep★PartnerOK₅ Wᵖ X P (just Y) U
  → W₂ ∣ γ₂ ⊢² P ⊑ U ∶ ★⊑★
  → TaggedTransferOutput₅ W₂ γ₂ P U X Y
tagged-transfer-output-from-transport₅ rb ok prem =
  tagged-transfer-output₅ prem
    (matched-seal-star-partner₅ (transportRep★PartnerOK₅ rb ok))

tagged-transfer-output-dyn₅ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp (SPT.dynWorld W)}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → RebaseAt Wᵖ W X Y
  → Rep★PartnerOK₅ (SPT.dynWorld Wᵖ) X P (just Y) U
  → SPT.dynWorld W ∣ γ ⊢² P ⊑ U ∶ ★⊑★
  → TaggedTransferOutput₅ (SPT.dynWorld W) γ P U X Y
tagged-transfer-output-dyn₅ rb ok prem =
  tagged-transfer-output₅ prem
    (matched-seal-star-partner₅
      (transportRep★PartnerOK-dyn₅ rb ok))

target-chain-88-emits₅ : ∀ {Δᴸ Δᴿ Δ}
    {W W₂ : World Δᴸ Δᴿ Δ} {γ : CtxImp W} {γ₂ : CtxImp W₂}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {q : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → CTI2.ImpEnvMono W W₂
  → RebaseAt W₂ W X Y
  → CTI2.SameCtx γ γ₂
  → CTI2.sourceStoreʷ W ⊢↓[ just X ] seal X ★
  → CTI2.targetStoreʷ W ⊢↓[ just Y ] seal Y ★
  → TaggedTransferOutput₅ W₂ γ₂ P U X Y
  → W ∣ γ ⊢² P ↓ seal X ★ ⊑ U ↓ seal Y ★ ∶ q
target-chain-88-emits₅ mono rb sc source⊢ target⊢ pkg =
  CTI2.conceal⊑conceal²
    (eraseMatchedConcealPartnerOK₅
      (TaggedTransferOutput₅.partner₅ pkg))
    mono rb sc source⊢ target⊢
    (TaggedTransferOutput₅.premise₅ pkg) _

------------------------------------------------------------------------
-- Payoffs: no-target variable tags remain formation-impossible
------------------------------------------------------------------------

var-tag-no-target-empty₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₅ W X P nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty₅ (rep★-untagged₅ ())
var-tag-no-target-empty₅ (rep★-nonvar-tag₅ ())
var-tag-no-target-empty₅ (rep★-round-trip₅ ok) =
  var-tag-no-target-empty₅ ok

nat-payload-var-tag-no-target-empty₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {ι : Base} {Y₂ : TyVar Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {G∼★ : μᴸ ⊢ (‵ ι) ∼★} {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cG : μᴸ ⊢ Aᴸ ∼ ‵ ι} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsG : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₅ W X
      (V₂ ⟨ _! {G = ‵ ι} ⦃ Gᵍ = ‵ ι ⦄
            ⦃ G∼★ = G∼★ ⦄ cG ⦃ Ans = AnsG ⦄ ⟩)
      nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
nat-payload-var-tag-no-target-empty₅ = var-tag-no-target-empty₅

source-seal-var-tag-no-target-empty₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → SourceConcealPartnerOK₅ W P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-empty₅
    (seal-partner-ok₅ (star-rep-target₅ ok)) =
  var-tag-no-target-empty₅ ok
source-seal-var-tag-no-target-empty₅
    (seal-partner-ok₅ (plain-target₅ ()))

source-seal-var-tag-no-target-after-cast-empty₅ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → SourceConcealPartnerOK₅ W P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-after-cast-empty₅ inert ok =
  source-seal-var-tag-no-target-empty₅ ok

------------------------------------------------------------------------
-- Poison and laundering exclusions
------------------------------------------------------------------------

bare-payload-var-tag-mismatch-empty₅ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₅ W X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₅ not-inner not-roundtrip
    not-aligned (rep★-untagged₅ ())
bare-payload-var-tag-mismatch-empty₅ not-inner not-roundtrip
    not-aligned (rep★-nonvar-tag₅ ())
bare-payload-var-tag-mismatch-empty₅ not-inner not-roundtrip
    not-aligned (rep★-var-tag₅ aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₅ not-inner not-roundtrip
    not-aligned (rep★-matched-inner-tags₅ X₂≢X aligned) =
  not-inner refl
bare-payload-var-tag-mismatch-empty₅ not-inner not-roundtrip
    not-aligned (rep★-round-trip₅ ok) =
  not-roundtrip refl

different-name-round-trip-no-launder₅ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₅ W X
      ((P ↓ seal Z ★)
        ⟨ _! {G = ＇ Z} ⦃ Gᵍ = ＇ Z ⦄
            ⦃ G∼★ = Z∼★ ⦄ cZ ⦃ Ans = AnsZ ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
different-name-round-trip-no-launder₅ Z≢X not-outer
    not-wrapper (rep★-untagged₅ ())
different-name-round-trip-no-launder₅ Z≢X not-outer
    not-wrapper (rep★-nonvar-tag₅ ())
different-name-round-trip-no-launder₅ Z≢X not-outer
    not-wrapper (rep★-var-tag₅ aligned) =
  not-outer aligned
different-name-round-trip-no-launder₅ Z≢X not-outer
    not-wrapper (rep★-matched-inner-tags₅ Z≢X′ aligned) =
  not-wrapper aligned
different-name-round-trip-no-launder₅ Z≢X not-outer
    not-wrapper (rep★-round-trip₅ ok) =
  Z≢X refl

non-rep★-round-trip-no-launder₅ : ∀ {Δᴸ Δᴿ Δ}
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
  → Rep★PartnerOK₅ W X
      ((P ↓ seal X R)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
non-rep★-round-trip-no-launder₅ Rns not-aligned
    (rep★-untagged₅ ())
non-rep★-round-trip-no-launder₅ Rns not-aligned
    (rep★-nonvar-tag₅ ())
non-rep★-round-trip-no-launder₅ Rns not-aligned
    (rep★-var-tag₅ aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₅ Rns not-aligned
    (rep★-matched-inner-tags₅ X≢X aligned) =
  X≢X refl
non-rep★-round-trip-no-launder₅ () not-aligned
    (rep★-round-trip₅ ok)
