module TightenPreflightScratch where

-- Root-level scratch for the rep-★ source-seal partner tightening
-- pre-flight.  The live GTSFImp development is imported read-only; this
-- file packages the current rule with the proposed stricter condition and
-- checks the requested concrete gates against restricted wrappers.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Nat as Nat
open import Data.Unit using (⊤; tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using
  (Env∼; _⊢_∼_; _⊢_∼★; _!; toRenameᵗ)
open import Conversion using (Conv↑; Conv↓; seal; _↦↓_; `∀↓_; id↓)
import Conversion
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _↓_)
open import Imprecision

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.Phase3DeepDives as P3
import proof.DGG.Parked.ParkedD4CheckpointLemma as D4
import proof.DGG.StarRepChainProbe as SRC
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.TagBoundaryProbe as TBP
import proof.DGG.TerminusRebuildProbe as TRB
import proof.DGG.notes.InitialPairScratch as IP

open CTI2 using
  (World; CtxImp; TagRebaseAtᴸ; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; targetStoreʷ)

------------------------------------------------------------------------
-- Tightened source-seal partner predicate
------------------------------------------------------------------------

CenterAligned : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → TyVar Δᴸ
  → TyVar Δᴿ
  → Set
CenterAligned W X Y =
  toRenameᵗ (CTI2.ηᴸʷ W) X ≡ toRenameᵗ (CTI2.ηᴿʷ W) Y

aligned-from-tag-rebase : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → TagRebaseAtᴸ W′ W (just X) (just Y)
  → CenterAligned W X Y
aligned-from-tag-rebase (CTI2.tag-rebase-varᴸ rb) =
  CTI2.RebaseAt.pivotAligned rb

-- The stricter rep-★ condition.  Top-level untagged partners are accepted.
-- Top-level non-variable-ground injections are accepted.  Variable-ground
-- injections carry an explicit source/target center-alignment witness.
data Rep★PartnerOK {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  rep★-untagged : ∀ {Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------
    → Rep★PartnerOK W X Xᴿ? M′

  rep★-nonvar-tag : ∀ {Xᴿ? M A G μ}
      {Gᵍ : Ground G} {G∼★ : μ ⊢ G ∼★}
      {c : μ ⊢ A ∼ G} {Ans : NonStar A}
    → NonVar G
      ------------------------------------------------------------
    → Rep★PartnerOK W X Xᴿ?
        (M ⟨ _! {G = G} ⦃ Gᵍ = Gᵍ ⦄ ⦃ G∼★ = G∼★ ⦄
              c ⦃ Ans = Ans ⦄ ⟩)

  rep★-var-tag : ∀ {M A Y μ}
      {Y∼★ : μ ⊢ (＇ Y) ∼★}
      {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    → CenterAligned W X Y
      ------------------------------------------------------------
    → Rep★PartnerOK W X (just Y)
        (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
              ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)

data SealPartnerOKᵀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (X : TyVar Δᴸ) :
    Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-targetᵀ : ∀ {Xᴿ? M′}
    → Rep★PartnerOK W X Xᴿ? M′
      --------------------------------
    → SealPartnerOKᵀ W X ★ Xᴿ? M′

  plain-targetᵀ : ∀ {R Xᴿ? M′}
    → CTI2.NotTopTag M′
      --------------------------------
    → SealPartnerOKᵀ W X R Xᴿ? M′

  name-protected-targetᵀ : ∀ {R Y S M μ}
      {c : μ ⊢ (＇ Y) ∼ ★}
      -----------------------------------------------
    → SealPartnerOKᵀ W X R (just Y) ((M ↓ seal Y S) ⟨ c ⟩)

data SourceConcealPartnerOKᵀ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) :
    {A A′ : Ty Δᴸ} → Conv↓ Δᴸ A A′
    → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  seal-partner-okᵀ : ∀ {X R Xᴿ? M′}
    → SealPartnerOKᵀ W X R Xᴿ? M′
      ------------------------------------------------
    → SourceConcealPartnerOKᵀ W (seal X R) Xᴿ? M′

  fun-conceal-targetᵀ : ∀ {A A′ B B′ Xᴿ? M′}
      {c : Conv↑ Δᴸ A′ A} {d : Conv↓ Δᴸ B B′}
      ------------------------------------------------
    → SourceConcealPartnerOKᵀ W (c ↦↓ d) Xᴿ? M′

  all-conceal-targetᵀ : ∀ {A B Xᴿ? M′}
      {c : Conv↓ (Nat.suc Δᴸ) A B}
      ------------------------------------------------
    → SourceConcealPartnerOKᵀ W (`∀↓ c) Xᴿ? M′

  id-conceal-targetᵀ : ∀ {A Xᴿ? M′}
      ------------------------------------------------
    → SourceConcealPartnerOKᵀ W (id↓ A) Xᴿ? M′

forgetRep★ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Xᴿ? M′}
  → Rep★PartnerOK W X Xᴿ? M′
  → CTI2.SealPartnerOK {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ★ Xᴿ? M′
forgetRep★ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} _ =
  CTI2.star-rep-target {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}

forgetSealPartnerOKᵀ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {R Xᴿ? M′}
  → SealPartnerOKᵀ W X R Xᴿ? M′
  → CTI2.SealPartnerOK {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} R Xᴿ? M′
forgetSealPartnerOKᵀ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ}
    (star-rep-targetᵀ ok) =
  forgetRep★ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} ok
forgetSealPartnerOKᵀ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} (plain-targetᵀ nt) =
  CTI2.plain-target {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} nt
forgetSealPartnerOKᵀ {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} name-protected-targetᵀ =
  CTI2.name-protected-target

forgetSourceConcealPartnerOKᵀ : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {A A′ : Ty Δᴸ}
    {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
  → SourceConcealPartnerOKᵀ W c Xᴿ? M′
  → CTI2.SourceConcealPartnerOK c Xᴿ? M′
forgetSourceConcealPartnerOKᵀ (seal-partner-okᵀ ok) =
  CTI2.seal-partner-ok (forgetSealPartnerOKᵀ ok)
forgetSourceConcealPartnerOKᵀ fun-conceal-targetᵀ =
  CTI2.fun-conceal-target
forgetSourceConcealPartnerOKᵀ all-conceal-targetᵀ =
  CTI2.all-conceal-target
forgetSourceConcealPartnerOKᵀ id-conceal-targetᵀ =
  CTI2.id-conceal-target

conceal⊑²ᵀ : ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {Xᴸ? : Maybe (TyVar Δᴸ)} {Xᴿ? : Maybe (TyVar Δᴿ)}
    {p : A ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ A A′}
  → SourceConcealPartnerOKᵀ W c Xᴿ? M′
  → CTI2.ImpEnvMono W W′
  → TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W CTI2.⊢↓[ Xᴸ? ] c
  → W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
  → (q : A′ ⊑ᵂ⟨ W ⟩ B)
  → W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q
conceal⊑²ᵀ ok mono rb sc c⊢ D q =
  CTI2.conceal⊑² (forgetSourceConcealPartnerOKᵀ ok)
    mono rb sc c⊢ D q

------------------------------------------------------------------------
-- Concrete tightened star-rep replays
------------------------------------------------------------------------

terminus-B-inner-okᵀ :
  SourceConcealPartnerOKᵀ TRB.InstanceB.Wᵖ
    (seal TRB.InstanceB.X ★) (just TRB.InstanceB.Y₂)
    TRB.InstanceB.U₀
terminus-B-inner-okᵀ =
  seal-partner-okᵀ (star-rep-targetᵀ
    (rep★-nonvar-tag nonvar-fun))

terminus-B-inner-source-seal²ᵀ :
  TRB.InstanceB.Wᵖ ∣ [] ⊢²
    TRB.InstanceB.V ⊑ TRB.InstanceB.U₀ ∶
      TRB.InstanceB.X⊑★-Wᵖ
terminus-B-inner-source-seal²ᵀ =
  conceal⊑²ᵀ terminus-B-inner-okᵀ
    (TRB.mono-refl {W = TRB.InstanceB.Wᵖ})
    (CTI2.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y₂)
    CTI2.same-[] TRB.InstanceB.source-seal-⊢
    TRB.InstanceB.base² TRB.InstanceB.X⊑★-Wᵖ

terminus-B-payload²ᵀ :
  TRB.InstanceB.Wᵖ ∣ [] ⊢²
    TRB.InstanceB.source-payload ⊑ TRB.InstanceB.U₀ ∶ ★⊑★
terminus-B-payload²ᵀ =
  CTI2.cast⊑² TRB.InstanceB.X!
    terminus-B-inner-source-seal²ᵀ ★⊑★

terminus-B-terminus-pair²ᵀ :
  TRB.InstanceB.Wᵖ ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.U ∶
      TRB.InstanceB.X⊑Y₂
terminus-B-terminus-pair²ᵀ =
  CTI2.conceal⊑conceal² (TRB.mono-refl {W = TRB.InstanceB.Wᵖ})
    TRB.InstanceB.rb-X-Y₂ CTI2.same-[]
    TRB.InstanceB.source-seal-⊢ TRB.InstanceB.target-Y₂-seal-⊢
    terminus-B-payload²ᵀ TRB.InstanceB.X⊑Y₂

terminus-B-outputᵀ :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-chain ∶
      TRB.InstanceB.X⊑Y
terminus-B-outputᵀ =
  CTI2.⊑conceal² TRB.InstanceB.mono-W-Wᵖ
    (CTI2.rebase-varᴿ TRB.InstanceB.rb-chain) CTI2.same-[]
    TRB.InstanceB.target-Y-seal-⊢
    terminus-B-terminus-pair²ᵀ TRB.InstanceB.X⊑Y

terminus-B-premise-chain²ᵀ :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.V ⊑ TRB.InstanceB.target-chain ∶
      TRB.InstanceB.X⊑Y
terminus-B-premise-chain²ᵀ =
  CTI2.⊑conceal² TRB.InstanceB.mono-W-Wᵖ
    (CTI2.rebase-varᴿ TRB.InstanceB.rb-chain) CTI2.same-[]
    TRB.InstanceB.target-Y-seal-⊢
    (CTI2.conceal⊑conceal² (TRB.mono-refl {W = TRB.InstanceB.Wᵖ})
      TRB.InstanceB.rb-X-Y₂ CTI2.same-[]
      TRB.InstanceB.source-seal-⊢ TRB.InstanceB.target-Y₂-seal-⊢
      TRB.InstanceB.base² TRB.InstanceB.X⊑Y₂)
    TRB.InstanceB.X⊑Y

terminus-B-premise-casts²ᵀ :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source-payload ⊑ TRB.InstanceB.target-tagged ∶ ★⊑★
terminus-B-premise-casts²ᵀ =
  CTI2.cast⊑cast² TRB.InstanceB.X! TRB.InstanceB.Y!
    terminus-B-premise-chain²ᵀ ★⊑★

terminus-B-X/Y-aligned :
  CenterAligned TRB.InstanceB.W TRB.InstanceB.X TRB.InstanceB.Y
terminus-B-X/Y-aligned =
  aligned-from-tag-rebase
    (CTI2.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y)

terminus-B-tagged-okᵀ :
  SourceConcealPartnerOKᵀ TRB.InstanceB.W
    (seal TRB.InstanceB.X ★) (just TRB.InstanceB.Y)
    TRB.InstanceB.target-tagged
terminus-B-tagged-okᵀ =
  seal-partner-okᵀ (star-rep-targetᵀ
    (rep★-var-tag terminus-B-X/Y-aligned))

terminus-B-tagged-inputᵀ :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
terminus-B-tagged-inputᵀ =
  conceal⊑²ᵀ terminus-B-tagged-okᵀ
    (TRB.mono-refl {W = TRB.InstanceB.W})
    (CTI2.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y)
    CTI2.same-[] TRB.InstanceB.source-seal-⊢
    terminus-B-premise-casts²ᵀ TRB.InstanceB.X⊑★-W

terminus-A-output-gate = TRB.InstanceA.output
terminus-A-tagged-input-gate = TRB.InstanceA.tagged-input

SRC-Xᴸ : TyVar 2
SRC-Xᴸ = Fin.zero

SRC-X : TyVar 2
SRC-X = Fin.suc Fin.zero

SRC-Y : TyVar 1
SRC-Y = Fin.zero

star-rep-chain-inner-okᵀ :
  SourceConcealPartnerOKᵀ SRC.W
    (seal SRC-X ★) nothing SRC.target-core
star-rep-chain-inner-okᵀ =
  seal-partner-okᵀ (star-rep-targetᵀ
    (rep★-nonvar-tag nonvar-base))

star-rep-chain-inner-source²ᵀ :
  SRC.W ∣ [] ⊢² SRC.source-inner ⊑ SRC.target-core ∶ SRC.inner-type
star-rep-chain-inner-source²ᵀ =
  conceal⊑²ᵀ star-rep-chain-inner-okᵀ
    (λ Z eq → eq) SRC.inner-source-only-rebase CTI2.same-[]
    SRC.source-X-seal-⊢ SRC.base² SRC.inner-type

star-rep-chain-outputᵀ :
  SRC.W ∣ [] ⊢² SRC.M ⊑ SRC.target-sealed ∶ SRC.q
star-rep-chain-outputᵀ =
  CTI2.conceal⊑conceal² (λ Z eq → eq) SRC.outer-rebase
    CTI2.same-[] SRC.source-Xᴸ-seal-⊢ SRC.target-Y-seal-⊢
    star-rep-chain-inner-source²ᵀ SRC.q

CRP-Z₃ : TyVar 2
CRP-Z₃ = Fin.suc Fin.zero

CRP-Y : TyVar 1
CRP-Y = Fin.zero

chain-ride-premise-okᵀ :
  SourceConcealPartnerOKᵀ CRP.W₂
    (seal CRP-Z₃ ★) (just CRP-Y) CRP.U
chain-ride-premise-okᵀ =
  seal-partner-okᵀ (star-rep-targetᵀ
    (rep★-nonvar-tag nonvar-base))

chain-ride-premiseᵀ :
  CRP.W₂ ∣ [] ⊢² CRP.V ⊑ CRP.U ∶ CRP.q₂
chain-ride-premiseᵀ =
  conceal⊑²ᵀ chain-ride-premise-okᵀ
    (λ X eq → eq) (CTI2.tag-rebase-varᴸ CRP.probe-premise-rebase)
    CTI2.same-[] CRP.probe-Z₃-seal-⊢ CRP.probe-base² CRP.q₂

TBP-X : TyVar 1
TBP-X = Fin.zero

TBP-Y′ : TyVar 2
TBP-Y′ = Fin.suc Fin.zero

tag-boundary-source-okᵀ :
  SourceConcealPartnerOKᵀ TBP.probe-W₅
    (seal TBP-X ★) (just TBP-Y′) TBP.probe-M₅
tag-boundary-source-okᵀ =
  seal-partner-okᵀ (star-rep-targetᵀ
    (rep★-nonvar-tag nonvar-base))

tag-boundary-source-seal²ᵀ :
  TBP.probe-W₅ ∣ [] ⊢² TBP.probe-V ⊑ TBP.probe-M₅ ∶ TBP.p₅
tag-boundary-source-seal²ᵀ =
  conceal⊑²ᵀ tag-boundary-source-okᵀ
    (λ _ eq → eq) (CTI2.tag-rebase-varᴸ TBP.probe-inner-source-rebase)
    CTI2.same-[] TBP.probe-X-seal-⊢ TBP.probe-base² TBP.p₅

------------------------------------------------------------------------
-- Examples2 and catalog/import gates
------------------------------------------------------------------------

examples2-star-rep-target-rg-empty : ⊤
examples2-star-rep-target-rg-empty = tt

example12-checkpoint₀-gate = Ex2.example12-checkpoint₀
example12-function-checkpoint₁-gate = Ex2.example12-function-checkpoint₁
example12-checkpoint₁-gate = Ex2.example12-checkpoint₁
example12-application-checkpoint₂-gate =
  Ex2.example12-application-checkpoint₂
example12-checkpoint₂-gate = Ex2.example12-checkpoint₂
example12-target-X!-checkpoint₃-gate =
  Ex2.example12-target-X!-checkpoint₃
example12-target-Z-seal-checkpoint₃-gate =
  Ex2.example12-target-Z-seal-checkpoint₃
example12-target-Y-seal-checkpoint₃-gate =
  Ex2.example12-target-Y-seal-checkpoint₃
example12-target-Y-unseal-checkpoint₃-gate =
  Ex2.example12-target-Y-unseal-checkpoint₃
example12-target-Z-unseal-checkpoint₃-gate =
  Ex2.example12-target-Z-unseal-checkpoint₃
example12-target-id★-checkpoint₃-gate =
  Ex2.example12-target-id★-checkpoint₃
example12-target-★?X-checkpoint₃-gate =
  Ex2.example12-target-★?X-checkpoint₃
example12-checkpoint₃-gate = Ex2.example12-checkpoint₃
example12-checkpoint₄-gate = Ex2.example12-checkpoint₄

nat-chain-checkpoint₀-gate = Ex2.nat-chain-checkpoint₀
nat-chain-function-checkpoint₁-gate =
  Ex2.nat-chain-function-checkpoint₁
nat-chain-checkpoint₁-gate = Ex2.nat-chain-checkpoint₁
nat-chain-application-checkpoint₂-gate =
  Ex2.nat-chain-application-checkpoint₂
nat-chain-checkpoint₂-gate = Ex2.nat-chain-checkpoint₂
nat-chain-checkpoint₃-gate = Ex2.nat-chain-checkpoint₃
nat-chain-checkpoint₄-gate = Ex2.nat-chain-checkpoint₄

left-path-checkpoint₀-gate = Ex2.left-path-checkpoint₀
left-path-checkpoint₁-gate = Ex2.left-path-checkpoint₁
left-path-checkpoint₂-gate = Ex2.left-path-checkpoint₂
left-path-checkpoint₃-gate = Ex2.left-path-checkpoint₃
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

------------------------------------------------------------------------
-- InitialPair gates
------------------------------------------------------------------------

initialpair-mid-outputᵀ :
  SRC.W ∣ [] ⊢² SRC.M ⊑ SRC.target-sealed ∶ SRC.q
initialpair-mid-outputᵀ = star-rep-chain-outputᵀ

initialpair-mid-input-gate = IP.mid-input
initialpair-initial-Pᶜ⊑Qᶜ-gate = IP.initial-Pᶜ⊑Qᶜ

------------------------------------------------------------------------
-- Payoff: unaligned variable-ground target tags are not formable
------------------------------------------------------------------------

rep★-var-tag-no-target-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {M A Y μ} {Y∼★ : μ ⊢ (＇ Y) ∼★}
    {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
  → Rep★PartnerOK W X nothing
      (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
            ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)
  → ⊥
rep★-var-tag-no-target-empty (rep★-untagged ())
rep★-var-tag-no-target-empty (rep★-nonvar-tag ())

rep★-var-tag-alignment : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {M A Y μ} {Y∼★ : μ ⊢ (＇ Y) ∼★}
    {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
  → Rep★PartnerOK W X (just Y)
      (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
            ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)
  → CenterAligned W X Y
rep★-var-tag-alignment (rep★-untagged ())
rep★-var-tag-alignment (rep★-nonvar-tag ())
rep★-var-tag-alignment (rep★-var-tag aligned) = aligned

rep★-var-tag-misaligned-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {M A Y μ} {Y∼★ : μ ⊢ (＇ Y) ∼★}
    {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
  → (CenterAligned W X Y → ⊥)
  → Rep★PartnerOK W X (just Y)
      (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
            ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)
  → ⊥
rep★-var-tag-misaligned-empty not-aligned ok =
  not-aligned (rep★-var-tag-alignment ok)

tag-rebase-var-misaligned-empty : ∀ {Δᴸ Δᴿ Δ}
    {W′ W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
  → (CenterAligned W X Y → ⊥)
  → TagRebaseAtᴸ W′ W (just X) (just Y)
  → ⊥
tag-rebase-var-misaligned-empty not-aligned rb =
  not-aligned (aligned-from-tag-rebase rb)

plain-star-rep-head-no-target-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {M A Y μ} {Y∼★ : μ ⊢ (＇ Y) ∼★}
    {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
  → SourceConcealPartnerOKᵀ W (seal X ★) nothing
      (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
            ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)
  → ⊥
plain-star-rep-head-no-target-empty
    (seal-partner-okᵀ (star-rep-targetᵀ ok)) =
  rep★-var-tag-no-target-empty ok
plain-star-rep-head-no-target-empty
    (seal-partner-okᵀ (plain-targetᵀ ()))

injected-star-rep-head-no-target-empty : ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {X : TyVar Δᴸ}
    {M A Y μ} {Y∼★ : μ ⊢ (＇ Y) ∼★}
    {c : μ ⊢ A ∼ ＇ Y} {Ans : NonStar A}
    {ν : Env∼ Δᴸ} {cX : ν ⊢ (＇ X) ∼ ★}
  → Inert cX
  → SourceConcealPartnerOKᵀ W (seal X ★) nothing
      (M ⟨ _! {G = ＇ Y} ⦃ Gᵍ = ＇ Y ⦄
            ⦃ G∼★ = Y∼★ ⦄ c ⦃ Ans = Ans ⦄ ⟩)
  → ⊥
injected-star-rep-head-no-target-empty inert ok =
  plain-star-rep-head-no-target-empty ok
