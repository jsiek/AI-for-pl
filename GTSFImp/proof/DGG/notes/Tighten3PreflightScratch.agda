module Tighten3PreflightScratch where

-- Root-level scratch for rep-★ tightening pre-flight 3.
-- Purpose: model the premise-world partner formulation without editing
-- GTSFImp, check the stopped partner obligations, and retain the formation
-- impossibility payoffs used by the source-strip worker.
-- Primary exports: the `₃` partner predicates, three discharge witnesses,
-- no-target emptiness lemmas, and read-only gate imports.
-- Key dependencies: CastTermImprecision2 for worlds/rules, SpineValueDef for
-- variable alignment extraction, and the existing DGG probes as gates.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl)

open import Types
open import Consistency using (Env∼; _⊢_∼_; _⊢_∼★; _!; toRenameᵗ)
open import CastTerms using (Term; Inert; _⟨_⟩; _↓_)
open import Conversion using (Conv↑; Conv↓; seal; _↦↓_; `∀↓_; id↓)
import Conversion
open import Imprecision

import proof.DGG.CtxImp as CTI2
import proof.DGG.CastTermImprecision as CTIR
import proof.DGG.Inversion.SpineValueDef as SVD
import proof.DGG.LambdaImpProbe as LIP
import proof.DGG.StarRepChainProbe as SRC
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.TagBoundaryProbe as TBP
import proof.DGG.TerminusRebuildProbe as TRB
import proof.DGG.Examples2 as Ex2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.Parked.ParkedD4CheckpointLemma as D4
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.notes.InitialPairScratch as IP
open import proof.DGG.WorldDecay using (EnvDecay; env-decay)

open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_)
open CTIR using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Premise-world partner predicate model
------------------------------------------------------------------------

CenterAligned₃ : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned₃ W X Y =
  toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y

data Rep★PartnerOK₃ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged₃ : ∀ {P Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------------------
    → Rep★PartnerOK₃ Wᵖ X P Xᴿ? M′

  rep★-nonvar-tag₃ : ∀ {P Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      -------------------------------------------------------------
    → Rep★PartnerOK₃ Wᵖ X P Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-outer-var-tag₃ : ∀ {P M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CenterAligned₃ Wᵖ X Y
      -------------------------------------------------------------
    → Rep★PartnerOK₃ Wᵖ X P (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

  rep★-matched-inner-tags₃ : ∀ {Y X₂ Y₂ V₂ U₂ Aᴸ Aᴿ μᴸ μᴿ}
      {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
      {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
      {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
      {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
    → CenterAligned₃ Wᵖ X₂ Y₂
      -------------------------------------------------------------
    → Rep★PartnerOK₃ Wᵖ X
        (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
              ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
        (just Y)
        (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
              ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)

data SealPartnerOK₃ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Term Δᴸ → Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target₃ : ∀ {P Xᴿ? M′}
    → Rep★PartnerOK₃ Wᵖ X P Xᴿ? M′
      --------------------------------------------
    → SealPartnerOK₃ Wᵖ X P ★ Xᴿ? M′

  plain-target₃ : ∀ {P R Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------------------
    → SealPartnerOK₃ Wᵖ X P R Xᴿ? M′

  name-protected-target₃ : ∀ {P R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      -----------------------------------------------------
    → SealPartnerOK₃ Wᵖ X P R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOK₃ {Δᴸ Δᴿ Δ}
    (Wᵖ : World Δᴸ Δᴿ Δ) :
    Term Δᴸ → {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-ok₃ : ∀ {P X R Xᴿ? M′}
    → SealPartnerOK₃ Wᵖ X P R Xᴿ? M′
      -----------------------------------------------------
    → SourceConcealPartnerOK₃ Wᵖ P (seal X R) Xᴿ? M′

  fun-conceal-target₃ : ∀ {P A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      -----------------------------------------------------
    → SourceConcealPartnerOK₃ Wᵖ P (c ↦↓ d) Xᴿ? M′

  all-conceal-target₃ : ∀ {P A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      -----------------------------------------------------
    → SourceConcealPartnerOK₃ Wᵖ P (`∀↓ c) Xᴿ? M′

  id-conceal-target₃ : ∀ {P A Xᴿ? M′}
      -----------------------------------------------------
    → SourceConcealPartnerOK₃ Wᵖ P (id↓ A) Xᴿ? M′

decayRep★PartnerOK₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → Rep★PartnerOK₃ Wᵖ X P Xᴿ? M′
  → Rep★PartnerOK₃ Wᵖᵈ X P Xᴿ? M′
decayRep★PartnerOK₃ (env-decay refl refl refl refl mono)
    (rep★-untagged₃ nt) =
  rep★-untagged₃ nt
decayRep★PartnerOK₃ (env-decay refl refl refl refl mono)
    (rep★-nonvar-tag₃ Gnv) =
  rep★-nonvar-tag₃ Gnv
decayRep★PartnerOK₃ (env-decay refl refl refl refl mono)
    (rep★-outer-var-tag₃ aligned) =
  rep★-outer-var-tag₃ aligned
decayRep★PartnerOK₃ (env-decay refl refl refl refl mono)
    (rep★-matched-inner-tags₃ aligned) =
  rep★-matched-inner-tags₃ aligned

decaySealPartnerOK₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {X : TyVar Δᴸ} {P R Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → SealPartnerOK₃ Wᵖ X P R Xᴿ? M′
  → SealPartnerOK₃ Wᵖᵈ X P R Xᴿ? M′
decaySealPartnerOK₃ dec (star-rep-target₃ ok) =
  star-rep-target₃ (decayRep★PartnerOK₃ dec ok)
decaySealPartnerOK₃ dec (plain-target₃ nt) = plain-target₃ nt
decaySealPartnerOK₃ dec name-protected-target₃ =
  name-protected-target₃

decaySourceConcealPartnerOK₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ Wᵖᵈ : World Δᴸ Δᴿ Δ}
    {M : Term Δᴸ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → EnvDecay Wᵖ Wᵖᵈ
  → SourceConcealPartnerOK₃ Wᵖ M c Xᴿ? M′
  → SourceConcealPartnerOK₃ Wᵖᵈ M c Xᴿ? M′
decaySourceConcealPartnerOK₃ dec (seal-partner-ok₃ ok) =
  seal-partner-ok₃ (decaySealPartnerOK₃ dec ok)
decaySourceConcealPartnerOK₃ dec fun-conceal-target₃ =
  fun-conceal-target₃
decaySourceConcealPartnerOK₃ dec all-conceal-target₃ =
  all-conceal-target₃
decaySourceConcealPartnerOK₃ dec id-conceal-target₃ =
  id-conceal-target₃

------------------------------------------------------------------------
-- Stopped partner obligations with premise-world alignment
------------------------------------------------------------------------

target-chain-85-partner₃ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → CTI2.RebaseAt Wᵖ W X Y
  → (＇ X₂) ⊑ᵂ⟨ Wᵖ ⟩ (＇ Y₂)
  → Rep★PartnerOK₃ Wᵖ X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
target-chain-85-partner₃ {Wᵖ = Wᵖ} {X₂ = X₂} {Y₂ = Y₂}
    rb p₂ =
  rep★-matched-inner-tags₃
    (SVD.variable-obligation-aligns {W = Wᵖ} {X = X₂} {Y = Y₂} p₂)

target-chain-85-same-pivot-partner₃ : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X∼★ : μᴸ ⊢ (＇ X) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → CTI2.RebaseAt Wᵖ W X Y
  → (＇ X) ⊑ᵂ⟨ Wᵖ ⟩ (＇ Y₂)
  → Rep★PartnerOK₃ Wᵖ X
      (V₂ ⟨ _! {G = ＇ X} ⦃ Gᵍ = ＇ X ⦄
            ⦃ G∼★ = X∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
target-chain-85-same-pivot-partner₃ =
  target-chain-85-partner₃

target-descent-138-partner₃ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → CTI2.RebaseAt W′ W X Y
  → (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y₂)
  → Rep★PartnerOK₃ W′ X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
target-descent-138-partner₃ = target-chain-85-partner₃

right-inj-612-partner₃ : ∀ {Δᴸ Δᴿ Δ}
    {W′ : World Δᴸ Δᴿ Δ} {X X₂ : TyVar Δᴸ}
    {Y Y₂ : TyVar Δᴿ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {X₂∼★ : μᴸ ⊢ (＇ X₂) ∼★}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cX : μᴸ ⊢ Aᴸ ∼ ＇ X₂} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsX : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → CenterAligned₃ W′ X₂ Y₂
  → Rep★PartnerOK₃ W′ X
      (V₂ ⟨ _! {G = ＇ X₂} ⦃ Gᵍ = ＇ X₂ ⦄
            ⦃ G∼★ = X₂∼★ ⦄ cX ⦃ Ans = AnsX ⦄ ⟩)
      (just Y)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
right-inj-612-partner₃ aligned =
  rep★-matched-inner-tags₃ aligned

------------------------------------------------------------------------
-- Payoffs: no-target variable tags remain formation-impossible
------------------------------------------------------------------------

var-tag-no-target-empty₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₃ Wᵖ X P nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
var-tag-no-target-empty₃ (rep★-untagged₃ ())
var-tag-no-target-empty₃ (rep★-nonvar-tag₃ ())

nat-payload-var-tag-no-target-empty₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {V₂ : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴸ : Ty Δᴸ} {Aᴿ : Ty Δᴿ}
    {ι : Base} {Y₂ : TyVar Δᴿ}
    {μᴸ : Env∼ Δᴸ} {μᴿ : Env∼ Δᴿ}
    {G∼★ : μᴸ ⊢ (‵ ι) ∼★} {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cG : μᴸ ⊢ Aᴸ ∼ ‵ ι} {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂}
    {AnsG : NonStar Aᴸ} {AnsY : NonStar Aᴿ}
  → Rep★PartnerOK₃ Wᵖ X
      (V₂ ⟨ _! {G = ‵ ι} ⦃ Gᵍ = ‵ ι ⦄
            ⦃ G∼★ = G∼★ ⦄ cG ⦃ Ans = AnsG ⦄ ⟩)
      nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
nat-payload-var-tag-no-target-empty₃ = var-tag-no-target-empty₃

source-seal-var-tag-no-target-empty₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
  → SourceConcealPartnerOK₃ Wᵖ P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-empty₃
    (seal-partner-ok₃ (star-rep-target₃ ok)) =
  var-tag-no-target-empty₃ ok
source-seal-var-tag-no-target-empty₃
    (seal-partner-ok₃ (plain-target₃ ()))

source-seal-var-tag-no-target-after-cast-empty₃ : ∀ {Δᴸ Δᴿ Δ}
    {Wᵖ : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {P : Term Δᴸ} {U₂ : Term Δᴿ}
    {Aᴿ : Ty Δᴿ} {Y₂ : TyVar Δᴿ} {μᴿ : Env∼ Δᴿ}
    {Y₂∼★ : μᴿ ⊢ (＇ Y₂) ∼★}
    {cY : μᴿ ⊢ Aᴿ ∼ ＇ Y₂} {AnsY : NonStar Aᴿ}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → SourceConcealPartnerOK₃ Wᵖ P (seal X ★) nothing
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
source-seal-var-tag-no-target-after-cast-empty₃ inert ok =
  source-seal-var-tag-no-target-empty₃ ok

bare-payload-var-tag-mismatch-empty₃ : ∀ {Δᴸ Δᴿ Δ}
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
  → (CenterAligned₃ Wᵖ X Y₂ → ⊥)
  → Rep★PartnerOK₃ Wᵖ X V (just Yᵒ)
      (U₂ ⟨ _! {G = ＇ Y₂} ⦃ Gᵍ = ＇ Y₂ ⦄
            ⦃ G∼★ = Y₂∼★ ⦄ cY ⦃ Ans = AnsY ⦄ ⟩)
  → ⊥
bare-payload-var-tag-mismatch-empty₃ not-inner not-aligned
    (rep★-untagged₃ ())
bare-payload-var-tag-mismatch-empty₃ not-inner not-aligned
    (rep★-nonvar-tag₃ ())
bare-payload-var-tag-mismatch-empty₃ not-inner not-aligned
    (rep★-outer-var-tag₃ aligned) =
  not-aligned aligned
bare-payload-var-tag-mismatch-empty₃ not-inner not-aligned
    (rep★-matched-inner-tags₃ aligned) =
  not-inner refl

------------------------------------------------------------------------
-- Current round-2 tree gates imported read-only
------------------------------------------------------------------------

star-rep-chain-gate₃ :
  SRC.W ∣ [] ⊢² SRC.M ⊑ SRC.target-sealed ∶ SRC.q
star-rep-chain-gate₃ = SRC.output

chain-ride-gate₃ :
  CRP.W₂ ∣ [] ⊢² CRP.V ⊑ CRP.U ∶ CRP.q₂
chain-ride-gate₃ = CRP.probe-premise

tag-boundary-gate₃ :
  TBP.probe-W₅ ∣ [] ⊢² TBP.probe-V ⊑ TBP.probe-M₅ ∶ TBP.p₅
tag-boundary-gate₃ = TBP.probe-source-seal²

terminus-B-gate₃ :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
terminus-B-gate₃ = TRB.InstanceB.tagged-input

lambda-imp-ground-wrapper-empty-gate₃ = LIP.probe-sealed-arg-empty

example12-checkpoint₄-gate₃ = Ex2.example12-checkpoint₄
nat-chain-checkpoint₄-gate₃ = Ex2.nat-chain-checkpoint₄
left-path-checkpoint-final-gate₃ = Ex2.left-path-checkpoint-final

catalog-adversarial-source-chain-initial-gate₃ =
  P3.adversarial-source-chain-initial²
catalog-adversarial-source-chain-checkpoint₁-gate₃ =
  P3.adversarial-source-chain-checkpoint₁
catalog-skew-star-inst-initial-gate₃ = P3.skew-star-inst-initial²
catalog-tag-boundary-star-inst-initial-gate₃ =
  P3.tag-boundary-star-inst-initial²
catalog-star-inst-checkpoint₁-gate₃ = P3.star-inst-checkpoint₁
catalog-higher-order-shared-arg-initial-gate₃ =
  P3.higher-order-shared-arg-initial²
catalog-D4-checkpoint-gate₃ = D4.D4-checkpoint

compile-preserves-imprecision-gate₃ =
  CPI2.compile-preserves-imprecision²

initialpair-mid-input-gate₃ = IP.mid-input
initialpair-initial-gate₃ = IP.initial-Pᶜ⊑Qᶜ
