module Tighten4PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 4.
-- Purpose: model a same-name rep-★ seal/tag round-trip see-through clause,
-- check the round-9 paired-seal re-emission heads, and retain the
-- formation-impossibility/poison-exclusion payoffs from earlier preflights.
-- Primary exports: the `₄` partner predicates, TargetChain/SourceStrip
-- re-emission witnesses, no-target emptiness lemmas, poison exclusions, and
-- read-only gates.
-- Key dependencies: CastTermImprecision2 for worlds/rules, SpineValueDef for
-- variable alignment extraction, WorldDecay for partner decay compatibility,
-- and the existing DGG probes/examples as gates.

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

import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.Inversion.SpineValueDef as SVD
open import proof.DGG.WorldDecay using (EnvDecay; env-decay)

open CTI2 using
  (World;
   RebaseAt;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Same-name rep-★ round-trip see-through partner predicate model
------------------------------------------------------------------------

CenterAligned₄ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned₄ W X Y =
  toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y

data Rep★PartnerOK₄ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged₄ : ∀ {P Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------------------
    → Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′

  rep★-nonvar-tag₄ : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      -------------------------------------------------------------
    → Rep★PartnerOK₄ Wᵖ X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-outer-var-tag₄ : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CenterAligned₄ Wᵖ X Y
      -------------------------------------------------------------
    → Rep★PartnerOK₄ Wᵖ X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags₄ : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → CenterAligned₄ Wᵖ X₂ Y₂
      -------------------------------------------------------------
    → Rep★PartnerOK₄ Wᵖ X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

  rep★-round-trip₄ : ∀ {P Xᴿ? M′ A μ}
      {X∼★ : μ ⊢ (＇ X) ∼★}
      {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
    → Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′
      -------------------------------------------------------------
    → Rep★PartnerOK₄ Wᵖ X
        ((P ↓ seal X ★)
          ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
              ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        Xᴿ? M′

data SealPartnerOK₄ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target₄ : ∀ {P Xᴿ? M′}
    → Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′
      --------------------------------------------
    → SealPartnerOK₄ Wᵖ X P ★ Xᴿ? M′

  plain-target₄ : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------------------
    → SealPartnerOK₄ Wᵖ X P R Xᴿ? M′

  name-protected-target₄ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      -----------------------------------------------------
    → SealPartnerOK₄ Wᵖ X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOK₄ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok₄ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOK₄ Wᵖ X P R Xᴿ? M′
      -----------------------------------------------------
    → SourceConcealPartnerOK₄ Wᵖ P (seal X R) Xᴿ? M′

  fun-conceal-target₄ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      -----------------------------------------------------
    → SourceConcealPartnerOK₄ Wᵖ P (c ↦↓ d) Xᴿ? M′

  all-conceal-target₄ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      -----------------------------------------------------
    → SourceConcealPartnerOK₄ Wᵖ P (`∀↓ c) Xᴿ? M′

  id-conceal-target₄ : ∀ {P A Xᴿ? M′}
      -----------------------------------------------------
    → SourceConcealPartnerOK₄ Wᵖ P (id↓ A) Xᴿ? M′

data MatchedConcealPartnerOK₄ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → TyVar Δᴿ → Term Δᴿ → Set where
  matched-seal-star-partner₄ : ∀ {P X Y M′}
    → Rep★PartnerOK₄ Wᵖ X P (just Y) M′
      -----------------------------------------------------
    → MatchedConcealPartnerOK₄ Wᵖ P (seal X ★) Y M′

  matched-seal-nonstar₄ : ∀ {P X R Y M′}
    → NonStar R
      -----------------------------------------------------
    → MatchedConcealPartnerOK₄ Wᵖ P (seal X R) Y M′

  matched-fun-conceal-target₄ : ∀ {P A A′ B B′ Y M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      -----------------------------------------------------
    → MatchedConcealPartnerOK₄ Wᵖ P (c ↦↓ d) Y M′

  matched-all-conceal-target₄ : ∀ {P A B Y M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      -----------------------------------------------------
    → MatchedConcealPartnerOK₄ Wᵖ P (`∀↓ c) Y M′

  matched-id-conceal-target₄ : ∀ {P A Y M′}
      -----------------------------------------------------
    → MatchedConcealPartnerOK₄ Wᵖ P (id↓ A) Y M′

source-round-trip-seal-star₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P Xᴿ? M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′
  → SourceConcealPartnerOK₄ Wᵖ
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Xᴿ? M′
source-round-trip-seal-star₄ ok =
  seal-partner-ok₄ (star-rep-target₄ (rep★-round-trip₄ ok))

matched-round-trip-seal-star₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {P M′ A μ}
    {X∼★ : μ ⊢ (＇ X) ∼★}
    {cX : μ ⊢ A ∼ ＇ X} {AnsX : NonStar A}
  → Rep★PartnerOK₄ Wᵖ X P (just Y) M′
  → MatchedConcealPartnerOK₄ Wᵖ
      ((P ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★) Y M′
matched-round-trip-seal-star₄ ok =
  matched-seal-star-partner₄ (rep★-round-trip₄ ok)

decayRep★PartnerOK₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → Rep★PartnerOK₄ Wᵖ X P Xᴿ? M′
  → Rep★PartnerOK₄ Wᵖᵈ X P Xᴿ? M′
decayRep★PartnerOK₄ (env-decay refl refl refl refl mono)
    (rep★-untagged₄ nt) =
  rep★-untagged₄ nt
decayRep★PartnerOK₄ (env-decay refl refl refl refl mono)
    (rep★-nonvar-tag₄ Gnv) =
  rep★-nonvar-tag₄ Gnv
decayRep★PartnerOK₄ (env-decay refl refl refl refl mono)
    (rep★-outer-var-tag₄ aligned) =
  rep★-outer-var-tag₄ aligned
decayRep★PartnerOK₄ (env-decay refl refl refl refl mono)
    (rep★-matched-inner-tags₄ aligned) =
  rep★-matched-inner-tags₄ aligned
decayRep★PartnerOK₄ dec (rep★-round-trip₄ ok) =
  rep★-round-trip₄ (decayRep★PartnerOK₄ dec ok)

decaySealPartnerOK₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → SealPartnerOK₄ Wᵖ X P R Xᴿ? M′
  → SealPartnerOK₄ Wᵖᵈ X P R Xᴿ? M′
decaySealPartnerOK₄ dec (star-rep-target₄ ok) =
  star-rep-target₄ (decayRep★PartnerOK₄ dec ok)
decaySealPartnerOK₄ dec (plain-target₄ nt) = plain-target₄ nt
decaySealPartnerOK₄ dec name-protected-target₄ =
  name-protected-target₄

decaySourceConcealPartnerOK₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → SourceConcealPartnerOK₄ Wᵖ M c Xᴿ? M′
  → SourceConcealPartnerOK₄ Wᵖᵈ M c Xᴿ? M′
decaySourceConcealPartnerOK₄ dec (seal-partner-ok₄ ok) =
  seal-partner-ok₄ (decaySealPartnerOK₄ dec ok)
decaySourceConcealPartnerOK₄ dec fun-conceal-target₄ =
  fun-conceal-target₄
decaySourceConcealPartnerOK₄ dec all-conceal-target₄ =
  all-conceal-target₄
decaySourceConcealPartnerOK₄ dec id-conceal-target₄ =
  id-conceal-target₄

decayMatchedConcealPartnerOK₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Y M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → MatchedConcealPartnerOK₄ Wᵖ M c Y M′
  → MatchedConcealPartnerOK₄ Wᵖᵈ M c Y M′
decayMatchedConcealPartnerOK₄ dec
    (matched-seal-star-partner₄ ok) =
  matched-seal-star-partner₄ (decayRep★PartnerOK₄ dec ok)
decayMatchedConcealPartnerOK₄ dec (matched-seal-nonstar₄ Rns) =
  matched-seal-nonstar₄ Rns
decayMatchedConcealPartnerOK₄ dec matched-fun-conceal-target₄ =
  matched-fun-conceal-target₄
decayMatchedConcealPartnerOK₄ dec matched-all-conceal-target₄ =
  matched-all-conceal-target₄
decayMatchedConcealPartnerOK₄ dec matched-id-conceal-target₄ =
  matched-id-conceal-target₄

------------------------------------------------------------------------
-- Round-9 and SourceStripWorker re-emission heads
------------------------------------------------------------------------

target-chain-88-reemit-partner₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵀ : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ Aᴸ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μˣ μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cX₂ : μᴸ ⊢ Aᴸ ∼ ＇ X₂}
    {cY₂ : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aˣ} {AnsX₂ : NonStar Aᴸ}
    {AnsY₂ : NonStar Bᴿ}
  → RebaseAt Wᵖ Wᵀ X Y
  → CenterAligned₄ Wᵖ X₂ Y₂
  → Rep★PartnerOK₄ Wᵖ X
      (((P ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
             ⦃ G∼★ = X₂∼★ ⦄ cX₂ ⦃ Ans = AnsX₂ ⦄ ⟩)
        ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY₂ ⦃ Ans = AnsY₂ ⦄ ⟩)
target-chain-88-reemit-partner₄ linkS aligned-inner =
  rep★-round-trip₄ (rep★-matched-inner-tags₄ aligned-inner)

target-chain-88-matched-conceal₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵀ : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {Aˣ Aᴸ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μˣ μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cX₂ : μᴸ ⊢ Aᴸ ∼ ＇ X₂}
    {cY₂ : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aˣ} {AnsX₂ : NonStar Aᴸ}
    {AnsY₂ : NonStar Bᴿ}
  → RebaseAt Wᵖ Wᵀ X Y
  → CenterAligned₄ Wᵖ X₂ Y₂
  → MatchedConcealPartnerOK₄ Wᵖ
      (((P ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
             ⦃ G∼★ = X₂∼★ ⦄ cX₂ ⦃ Ans = AnsX₂ ⦄ ⟩)
        ↓ seal X ★)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (seal X ★)
      Y
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY₂ ⦃ Ans = AnsY₂ ⦄ ⟩)
target-chain-88-matched-conceal₄ linkS aligned-inner =
  matched-seal-star-partner₄
    (rep★-round-trip₄ (rep★-matched-inner-tags₄ aligned-inner))

composeOuterRebase₄ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {Y Y′ : TyVar Δᴿ}
  → RebaseAt W′ W X Y
  → RebaseAt W₂ W′ X Y′
  → RebaseAt W₂ W X Y
composeOuterRebase₄ {W = W} {W′ = W′} {W₂ = W₂}
    {X = X} {Y = Y} rb₁ rb₂ =
  CTI2.rebase-at
    (CTI2.same-runtime
      (trans (CTI2.SameRuntime.sourceStore-same
        (CTI2.RebaseAt.sameRuntime rb₁))
        (CTI2.SameRuntime.sourceStore-same
          (CTI2.RebaseAt.sameRuntime rb₂)))
      (trans (CTI2.SameRuntime.targetStore-same
        (CTI2.RebaseAt.sameRuntime rb₁))
        (CTI2.SameRuntime.targetStore-same
          (CTI2.RebaseAt.sameRuntime rb₂))))
    source-off target-frozen (CTI2.RebaseAt.pivotAligned rb₁)
    (CTI2.RebaseAt.storeRepresentations rb₁)
  where
  source-off : ∀ {Z} → Z ≢ X
    → toRenameᵗ (CTI2.ηᴸʷ W) Z
        ≡ toRenameᵗ (CTI2.ηᴸʷ W₂) Z
  source-off Z≢X =
    trans (CTI2.RebaseAt.ηᴸ-off-pivot rb₁ Z≢X)
      (CTI2.RebaseAt.ηᴸ-off-pivot rb₂ Z≢X)

  target-frozen : ∀ Z
    → toRenameᵗ (CTI2.ηᴿʷ W) Z
        ≡ toRenameᵗ (CTI2.ηᴿʷ W₂) Z
  target-frozen Z =
    trans (CTI2.RebaseAt.ηᴿ-frozen rb₁ Z)
      (CTI2.RebaseAt.ηᴿ-frozen rb₂ Z)

record SourceStrip420Shape₄ {Δᴸ Δᴿ Δ}
    (W W′ W₂ : World Δᴸ Δᴿ Δ)
    (X X₂ : TyVar Δᴸ) (Y Y′ Y₂ : TyVar Δᴿ)
    (P : Term Δᴸ) (U : Term Δᴿ) : Set where
  constructor source-strip-420-shape₄
  field
    composed-rebase₄ : RebaseAt W₂ W X Y
    partner₄ : ∀ {Aˣ Aᴸ : Ty Δᴸ} {Cᴿ : Ty Δᴿ}
        {μˣ μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
        {X∼★ : μˣ ⊢ (＇ X) ∼★}
        {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
        {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
        {cX : μˣ ⊢ Aˣ ∼ ＇ X}
        {cX₂ : μᴸ ⊢ Aᴸ ∼ ＇ X₂}
        {cY₂ : μᴿ ⊢ Cᴿ ∼ ＇ Y₂}
        {AnsX : NonStar Aˣ} {AnsX₂ : NonStar Aᴸ}
        {AnsY₂ : NonStar Cᴿ}
      → Rep★PartnerOK₄ W₂ X
          (((P ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
                 ⦃ G∼★ = X₂∼★ ⦄ cX₂
                 ⦃ Ans = AnsX₂ ⦄ ⟩)
            ↓ seal X ★)
            ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
                ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
          (just Y)
          (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
                ⦃ G∼★ = Y₂∼★ ⦄ cY₂ ⦃ Ans = AnsY₂ ⦄ ⟩)

source-strip-worker-420-shape₄ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {X X₂ : TyVar Δᴸ} {Y Y′ Y₂ : TyVar Δᴿ}
    {P : Term Δᴸ} {U : Term Δᴿ}
  → RebaseAt W′ W X Y
  → RebaseAt W₂ W′ X Y′
  → CenterAligned₄ W₂ X₂ Y₂
  → SourceStrip420Shape₄ W W′ W₂ X X₂ Y Y′ Y₂ P U
source-strip-worker-420-shape₄ rb link aligned-inner =
  source-strip-420-shape₄ (composeOuterRebase₄ rb link)
    (rep★-round-trip₄ (rep★-matched-inner-tags₄ aligned-inner))

------------------------------------------------------------------------
-- Payoffs: no-target variable tags remain formation-impossible
------------------------------------------------------------------------

var-tag-no-target-empty₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₄ Wᵖ X P nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty₄ (rep★-untagged₄ ())
var-tag-no-target-empty₄ (rep★-nonvar-tag₄ ())
var-tag-no-target-empty₄ (rep★-round-trip₄ ok) =
  var-tag-no-target-empty₄ ok

nat-payload-var-tag-no-target-empty₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {ι : Base} {Y₂ : TyVar Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {G∼★ : μᴸ ⊢ (‵ ι) ∼★} {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cG : μᴸ ⊢ Aᴸ ∼ ‵ ι} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsG : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₄ Wᵖ X
      (V₂ ⟨ _! {G = ‵ ι} ⦃ Gᵍ = ‵ ι ⦄
            ⦃ G∼★ = G∼★ ⦄ cG ⦃ Ans = AnsG ⦄ ⟩)
      nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
nat-payload-var-tag-no-target-empty₄ = var-tag-no-target-empty₄

source-seal-var-tag-no-target-empty₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → SourceConcealPartnerOK₄ Wᵖ P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-empty₄
    (seal-partner-ok₄ (star-rep-target₄ ok)) =
  var-tag-no-target-empty₄ ok
source-seal-var-tag-no-target-empty₄
    (seal-partner-ok₄ (plain-target₄ ()))

source-seal-var-tag-no-target-after-cast-empty₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → SourceConcealPartnerOK₄ Wᵖ P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-after-cast-empty₄ inert ok =
  source-seal-var-tag-no-target-empty₄ ok

------------------------------------------------------------------------
-- Poison exclusions
------------------------------------------------------------------------

bare-payload-var-tag-mismatch-empty₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
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
  → (CenterAligned₄ Wᵖ X Y₂ → ⊥)
  → Rep★PartnerOK₄ Wᵖ X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₄ not-inner not-roundtrip
    not-aligned (rep★-untagged₄ ())
bare-payload-var-tag-mismatch-empty₄ not-inner not-roundtrip
    not-aligned (rep★-nonvar-tag₄ ())
bare-payload-var-tag-mismatch-empty₄ not-inner not-roundtrip
    not-aligned (rep★-outer-var-tag₄ aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₄ not-inner not-roundtrip
    not-aligned (rep★-matched-inner-tags₄ aligned) =
  not-inner refl
bare-payload-var-tag-mismatch-empty₄ not-inner not-roundtrip
    not-aligned (rep★-round-trip₄ ok) =
  not-roundtrip refl

different-name-round-trip-no-launder₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X Z : TyVar Δᴸ}
    {Yᵒ Y₂ : TyVar Δᴿ} {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {Aᶻ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μᶻ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {Z∼★ : μᶻ ⊢ (＇ Z) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cZ : μᶻ ⊢ Aᶻ ∼ ＇ Z}
    {cY : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsZ : NonStar Aᶻ} {AnsY : NonStar Bᴿ}
  → Z ≢ X
  → (CenterAligned₄ Wᵖ X Y₂ → ⊥)
  → (CenterAligned₄ Wᵖ Z Y₂ → ⊥)
  → Rep★PartnerOK₄ Wᵖ X
      ((P ↓ seal Z ★)
        ⟨ _! {G = ＇ Z} ⦃ Gᵍ = ＇ Z ⦄
            ⦃ G∼★ = Z∼★ ⦄ cZ ⦃ Ans = AnsZ ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
different-name-round-trip-no-launder₄ Z≢X not-outer
    not-wrapper (rep★-untagged₄ ())
different-name-round-trip-no-launder₄ Z≢X not-outer
    not-wrapper (rep★-nonvar-tag₄ ())
different-name-round-trip-no-launder₄ Z≢X not-outer
    not-wrapper (rep★-outer-var-tag₄ aligned) =
  not-outer aligned
different-name-round-trip-no-launder₄ Z≢X not-outer
    not-wrapper (rep★-matched-inner-tags₄ aligned) =
  not-wrapper aligned
different-name-round-trip-no-launder₄ Z≢X not-outer
    not-wrapper (rep★-round-trip₄ ok) =
  Z≢X refl

non-rep★-round-trip-no-launder₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Yᵒ Y₂ : TyVar Δᴿ} {P U₂ : Term Δᴸ} {U : Term Δᴿ}
    {R Aˣ Aᴿ : Ty Δᴸ} {Bᴿ : Ty Δᴿ}
    {μˣ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μˣ ⊢ (＇ X) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μˣ ⊢ Aˣ ∼ ＇ X}
    {cY : μᴿ ⊢ Bᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aˣ} {AnsY : NonStar Bᴿ}
  → NonStar R
  → (CenterAligned₄ Wᵖ X Y₂ → ⊥)
  → Rep★PartnerOK₄ Wᵖ X
      ((P ↓ seal X R)
        ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Yᵒ)
      (U ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
non-rep★-round-trip-no-launder₄ Rns not-aligned
    (rep★-untagged₄ ())
non-rep★-round-trip-no-launder₄ Rns not-aligned
    (rep★-nonvar-tag₄ ())
non-rep★-round-trip-no-launder₄ Rns not-aligned
    (rep★-outer-var-tag₄ aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₄ Rns not-aligned
    (rep★-matched-inner-tags₄ aligned) =
  not-aligned aligned
non-rep★-round-trip-no-launder₄ () not-aligned
    (rep★-round-trip₄ ok)

------------------------------------------------------------------------
-- Compatibility sweep surfaces
------------------------------------------------------------------------

record TargetSealTerminal₄ {Δᴸ Δᴿ Δ}
    (W₀ : World Δᴸ Δᴿ Δ) (γ₀ : CTI2.CtxImp W₀)
    (P : Term Δᴸ) (U : Term Δᴿ)
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ) : Set where
  constructor target-terminal₄
  field
    Wᵒ₄ : World Δᴸ Δᴿ Δ
    γᵒ₄ : CTI2.CtxImp Wᵒ₄
    rebaseᵒ₄ : RebaseAt Wᵒ₄ W₀ Xᵒ Yᵒ
    monoᵒ₄ : CTI2.ImpEnvMono W₀ Wᵒ₄
    sameᵒ₄ : CTI2.SameCtx γ₀ γᵒ₄
    premiseᵒ₄ : Wᵒ₄ ∣ γᵒ₄ ⊢² P ⊑ U ∶ ★⊑★
    partnerᵒ₄ : MatchedConcealPartnerOK₄ Wᵒ₄ P (seal Xᵒ ★) Yᵒ U

target-seal-terminal-extract-partner₄ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CTI2.CtxImp W}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → (t : TargetSealTerminal₄ W γ P U X Y)
  → MatchedConcealPartnerOK₄
      (TargetSealTerminal₄.Wᵒ₄ t) P (seal X ★) Y U
target-seal-terminal-extract-partner₄ t =
  TargetSealTerminal₄.partnerᵒ₄ t

plain-star-rep-premise-partner₄ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {V : Term Δᴸ} {U : Term Δᴿ} {Xᴿ?}
  → Rep★PartnerOK₄ Wᵖ X V Xᴿ? U
  → SourceConcealPartnerOK₄ Wᵖ V (seal X ★) Xᴿ? U
plain-star-rep-premise-partner₄ ok =
  seal-partner-ok₄ (star-rep-target₄ ok)
