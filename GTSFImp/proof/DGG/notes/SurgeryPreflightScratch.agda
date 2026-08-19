module SurgeryPreflightScratch where

-- Root-level scratch for the tag-discipline surgery pre-flight.
-- It checks the refined source-seal partner discipline keyed by the seal
-- representation, then replays the M3/source-strip gates against it.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import Conversion using (Conv↓; seal)
open import Consistency using (Env∼; _⊢_∼_)
open import CastTerms using (Term; _⟨_⟩; _↓_; $)
open import Primitives using (κℕ)
open import Imprecision
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.Example12Worlds as Ex12
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.CompilePreservesImprecision2 as CPI2
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2
import proof.DGG.TerminusRebuildProbe as TRB
import proof.DGG.Inversion.TargetDescentDef as TDD
import proof.DGG.Inversion.TargetDescentProof as TDP
import TagDisciplineScratch as TD

open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)

------------------------------------------------------------------------
-- Refined source-seal partner discipline
------------------------------------------------------------------------

data SealPartnerOK {Δᴸ Δᴿ : TyCtx} :
    Ty Δᴸ → Maybe (TyVar Δᴿ) → Term Δᴿ → Set where
  star-rep-target : ∀ {Xᴿ? M′}
      -----------------------------------------------------------
    → SealPartnerOK ★ Xᴿ? M′

  plain-target : ∀ {R Xᴿ? M′}
    → TD.NotTopTag M′
      -----------------------------------------------------------
    → SealPartnerOK R Xᴿ? M′

  name-protected-target : ∀ {R X S M μ} {c : μ ⊢ ＇ X ∼ ★}
      -----------------------------------------------------------
    → SealPartnerOK R (just X) ((M ↓ seal X S) ⟨ c ⟩)

infix 4 _∣_⊢ʳᵗᵈ_⊑_∶_

data _∣_⊢ʳᵗᵈ_⊑_∶_ {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ) (γ : CtxImp W) :
    Term Δᴸ → Term Δᴿ → {A : Ty Δᴸ} {B : Ty Δᴿ}
    → A ⊑ᵂ⟨ W ⟩ B → Set where

  κℕ⊑κℕʳᵗᵈ : ∀ n
    → (p : (‵ `ℕ) ⊑ᵂ⟨ W ⟩ (‵ `ℕ))
      ----------------------------------------------------
    → W ∣ γ ⊢ʳᵗᵈ $ (κℕ n) ⊑ $ (κℕ n) ∶ p

  ⊑castʳᵗᵈ : ∀ {M M′ A B B′}
      {p : A ⊑ᵂ⟨ W ⟩ B} {ν : Env∼ Δᴿ}
    → (c′ : ν ⊢ B ∼ B′)
    → W ∣ γ ⊢ʳᵗᵈ M ⊑ M′ ∶ p
    → (q : A ⊑ᵂ⟨ W ⟩ B′)
      -----------------------------
    → W ∣ γ ⊢ʳᵗᵈ M ⊑ M′ ⟨ c′ ⟩ ∶ q

  conceal⊑ʳᵗᵈ : ∀ {W′ : World Δᴸ Δᴿ Δ}
      {γ′ : CtxImp W′} {M M′ R A′ B Xᴸ? Xᴿ?}
      {p : R ⊑ᵂ⟨ W′ ⟩ B} {c : Conv↓ Δᴸ R A′}
    → SealPartnerOK R Xᴿ? M′
    → CTX.ImpEnvMono W W′
    → TD.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    → CTX.SameCtx γ γ′
    → CTX.sourceStoreʷ W Conv.⊢↓[ Xᴸ? ] c
    → W′ ∣ γ′ ⊢ʳᵗᵈ M ⊑ M′ ∶ p
    → (q : A′ ⊑ᵂ⟨ W ⟩ B)
      -----------------------------
    → W ∣ γ ⊢ʳᵗᵈ M ↓ c ⊑ M′ ∶ q

  conceal⊑concealʳᵗᵈ : ∀
      {Wᵖ : World Δᴸ Δᴿ Δ} {γᵖ : CtxImp Wᵖ}
      {M M′ A A′ B B′ Xᴸ Xᴿ}
      {p : A ⊑ᵂ⟨ Wᵖ ⟩ A′}
      {c : Conv↓ Δᴸ A B} {c′ : Conv↓ Δᴿ A′ B′}
    → CTX.ImpEnvMono W Wᵖ
    → CTX.RebaseAt Wᵖ W Xᴸ Xᴿ
    → CTX.SameCtx γ γᵖ
    → CTX.sourceStoreʷ W Conv.⊢↓[ just Xᴸ ] c
    → CTX.targetStoreʷ W Conv.⊢↓[ just Xᴿ ] c′
    → Wᵖ ∣ γᵖ ⊢ʳᵗᵈ M ⊑ M′ ∶ p
    → (q : B ⊑ᵂ⟨ W ⟩ B′)
      -------------------------------------
    → W ∣ γ ⊢ʳᵗᵈ M ↓ c ⊑ M′ ↓ c′ ∶ q

forgetʳᵗᵈ : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ} {γ}
    {M : Term Δᴸ} {M′ : Term Δᴿ} {A : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W ⟩ B}
  → W ∣ γ ⊢ʳᵗᵈ M ⊑ M′ ∶ p
    ---------------------
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
forgetʳᵗᵈ (κℕ⊑κℕʳᵗᵈ n p) = CTI2.κ⊑κ² (κℕ n) p
forgetʳᵗᵈ (⊑castʳᵗᵈ c′ D q) =
  CTI2.⊑cast² c′ (forgetʳᵗᵈ D) q
forgetʳᵗᵈ (conceal⊑ʳᵗᵈ ok mono rb sc c⊢ D q) =
  CTI2.conceal⊑² mono (TD.forgetTagRebaseᴸ rb) sc c⊢
    (forgetʳᵗᵈ D) q
forgetʳᵗᵈ (conceal⊑concealʳᵗᵈ mono rb sc c⊢ c′⊢ D q) =
  CTI2.conceal⊑conceal² mono rb sc c⊢ c′⊢ (forgetʳᵗᵈ D) q

------------------------------------------------------------------------
-- Generic restricted source-seal frame
------------------------------------------------------------------------

record RestrictedSourceSealFrame {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A A′ : Ty Δᴸ} {B : Ty Δᴿ}
    {p : A ⊑ᵂ⟨ W′ ⟩ B} {q : A′ ⊑ᵂ⟨ W ⟩ B}
    {Xᴸ?} {Xᴿ?} {c : Conv↓ Δᴸ A A′} : Set where
  field
    target-ok : SealPartnerOK A Xᴿ? M′
    rebaseᴸ : TD.TagRebaseAtᴸ W′ W Xᴸ? Xᴿ?
    premise² : W′ ∣ γ′ ⊢² M ⊑ M′ ∶ p
    live² : W ∣ γ ⊢² M ↓ c ⊑ M′ ∶ q

top-tag-not-plain : ∀ {Δ M A B} {μ : Env∼ Δ}
    {c : μ ⊢ A ∼ B}
  → TD.NotTopTag (M ⟨ c ⟩)
  → ⊥
top-tag-not-plain ()

mismatch-target-not-ok-refined-nat :
  ∀ {Xᴿ? : Maybe (TyVar 1)}
  → SealPartnerOK {Δᴸ = 2} {Δᴿ = 1} (‵ `ℕ) Xᴿ?
      (($ (κℕ 0)) ⟨ TD.ℕ! ⟩)
  → ⊥
mismatch-target-not-ok-refined-nat (plain-target ())

U-not-ℕ-refined :
  ＇ Fin.suc Fin.zero ⊑ᵂ⟨ TD.probe-world ⟩ ‵ `ℕ
  → ⊥
U-not-ℕ-refined ()

refined-restricted-mismatch-premise-empty :
  _∣_⊢ʳᵗᵈ_⊑_∶_ TD.probe-world [] TD.source-term TD.target-tagged
    {A = ＇ Fin.suc Fin.zero} {B = ★} TD.probe-p
  → ⊥
refined-restricted-mismatch-premise-empty
    (⊑castʳᵗᵈ {p = p} c′ D q) =
  U-not-ℕ-refined p
refined-restricted-mismatch-premise-empty
    (conceal⊑ʳᵗᵈ ok mono rb sc c⊢ D q) =
  mismatch-target-not-ok-refined-nat ok

name-tag-target-ok-refined :
  SealPartnerOK {Δᴸ = 2} {Δᴿ = 1} (‵ `ℕ) (just Fin.zero)
    TD.target-name-tagged
name-tag-target-ok-refined = name-protected-target

baseʳᵗᵈ : TD.probe-world ∣ [] ⊢ʳᵗᵈ
    $ (κℕ 0) ⊑ $ (κℕ 0) ∶ ι⊑ι
baseʳᵗᵈ = κℕ⊑κℕʳᵗᵈ 0 ι⊑ι

target-rep-tagʳᵗᵈ : TD.probe-world ∣ [] ⊢ʳᵗᵈ
    $ (κℕ 0) ⊑ TD.target-tagged ∶ ι⊑★
target-rep-tagʳᵗᵈ = ⊑castʳᵗᵈ TD.ℕ! baseʳᵗᵈ ι⊑★

paired-name-sealʳᵗᵈ : TD.probe-world ∣ [] ⊢ʳᵗᵈ
    TD.source-term ⊑ TD.target-tagged ↓ seal Fin.zero ★ ∶ TD.probe-q
paired-name-sealʳᵗᵈ =
  conceal⊑concealʳᵗᵈ (λ _ eq → eq) TD.U-Y-rebase CTX.same-[]
    TD.source-U-seal-typed TD.target-Y-seal-typed
    target-rep-tagʳᵗᵈ TD.probe-q

sealed-source-name-tag-positiveʳᵗᵈ : TD.probe-world ∣ [] ⊢ʳᵗᵈ
    TD.source-term ⊑ TD.target-name-tagged ∶ TD.probe-p
sealed-source-name-tag-positiveʳᵗᵈ =
  ⊑castʳᵗᵈ TD.Y! paired-name-sealʳᵗᵈ TD.probe-p

chain-variable-rep-direct-tag-empty :
  SealPartnerOK {Δᴸ = 2} {Δᴿ = 1}
    (＇ Fin.suc Fin.zero) (just Fin.zero) CRP.U
  → ⊥
chain-variable-rep-direct-tag-empty (plain-target ())

------------------------------------------------------------------------
-- Q1. M3 stuck input-shape gates
------------------------------------------------------------------------

-- The `cast⊑cast²` premise case is still legal: the outer source seal's
-- target partner is exactly `(U ↓ seal Y S) ⟨ Y! ⟩`.
m3-cast⊑cast²-input :
  RestrictedSourceSealFrame
    {W = TRB.InstanceB.W}
    {W′ = TRB.InstanceB.W}
    {γ = []}
    {γ′ = []}
    {M = TRB.InstanceB.source-payload}
    {M′ = TRB.InstanceB.target-tagged}
    {A = ★}
    {A′ = ＇ TRB.InstanceB.X}
    {B = ★}
    {p = ★⊑★}
    {q = TRB.InstanceB.X⊑★-W}
    {Xᴸ? = just TRB.InstanceB.X}
    {Xᴿ? = just TRB.InstanceB.Y}
    {c = seal TRB.InstanceB.X ★}
m3-cast⊑cast²-input = record
  { target-ok = star-rep-target
  ; rebaseᴸ = TD.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y
  ; premise² = TRB.InstanceB.premise-casts²
  ; live² = TRB.InstanceB.tagged-input
  }

-- The `cast⊑²` premise case is also still legal.  This is the same
-- name-tagged target, but with the source inert cast folded before the
-- outer source seal.
m3-cast⊑²-source-to-tag :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.V ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
m3-cast⊑²-source-to-tag =
  CTI2.⊑cast² TRB.InstanceB.Y! TRB.InstanceB.premise-chain²
    TRB.InstanceB.X⊑★-W

m3-cast⊑²-premise :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source-payload ⊑ TRB.InstanceB.target-tagged ∶
      ★⊑★
m3-cast⊑²-premise =
  CTI2.cast⊑² TRB.InstanceB.X! m3-cast⊑²-source-to-tag ★⊑★

m3-cast⊑²-live :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
m3-cast⊑²-live =
  CTI2.conceal⊑² (TRB.mono-refl {W = TRB.InstanceB.W})
    (CTX.rebase-varᴸ TRB.InstanceB.rb-X-Y)
    CTX.same-[] TRB.InstanceB.source-seal-⊢
    m3-cast⊑²-premise TRB.InstanceB.X⊑★-W

m3-cast⊑²-input :
  RestrictedSourceSealFrame
    {W = TRB.InstanceB.W}
    {W′ = TRB.InstanceB.W}
    {γ = []}
    {γ′ = []}
    {M = TRB.InstanceB.source-payload}
    {M′ = TRB.InstanceB.target-tagged}
    {A = ★}
    {A′ = ＇ TRB.InstanceB.X}
    {B = ★}
    {p = ★⊑★}
    {q = TRB.InstanceB.X⊑★-W}
    {Xᴸ? = just TRB.InstanceB.X}
    {Xᴿ? = just TRB.InstanceB.Y}
    {c = seal TRB.InstanceB.X ★}
m3-cast⊑²-input = record
  { target-ok = star-rep-target
  ; rebaseᴸ = TD.tag-rebase-varᴸ TRB.InstanceB.rb-X-Y
  ; premise² = m3-cast⊑²-premise
  ; live² = m3-cast⊑²-live
  }

-- The nested source-conceal premise is not killed by the target-shape
-- restriction when its inner source-seal descent is also name-protected at
-- the same target name.  The full recursive worker still has to prove the
-- structural impossibility/recursive descent facts, but the new gate does
-- not make the shape empty.
m3-nested-conceal-target-ok :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 2} ★
    (just TRB.InstanceB.Y) TRB.InstanceB.target-tagged
m3-nested-conceal-target-ok = star-rep-target

-- The `rebase-onlyᴸ` premise has no target name available, but the source
-- seal representation is `★`, so the refined predicate deliberately permits
-- arbitrary target tags in this case.
m3-rebase-only-input-ok :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 2} ★ nothing
    TRB.InstanceB.target-tagged
m3-rebase-only-input-ok = star-rep-target

------------------------------------------------------------------------
-- Q2. Proven re-emission construction gates
------------------------------------------------------------------------

terminus-instanceA-tagged-partner-ok :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 1} TRB.InstanceA.∀X⇒X
    (just TRB.InstanceA.Y) TRB.InstanceA.target-tagged
terminus-instanceA-tagged-partner-ok = name-protected-target

terminus-instanceA-live-tagged-input :
  TRB.InstanceA.W ∣ [] ⊢²
    TRB.InstanceA.source ⊑ TRB.InstanceA.target-tagged ∶
      TRB.InstanceA.X⊑★-W
terminus-instanceA-live-tagged-input = TRB.InstanceA.tagged-input

terminus-instanceA-direct-dyn-id-empty :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 1} TRB.InstanceA.∀X⇒X
    (just TRB.InstanceA.Y) TRB.InstanceA.U
  → ⊥
terminus-instanceA-direct-dyn-id-empty (plain-target ())

terminus-instanceB-tagged-partner-ok :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 2} ★
    (just TRB.InstanceB.Y) TRB.InstanceB.target-tagged
terminus-instanceB-tagged-partner-ok = star-rep-target

terminus-instanceB-live-tagged-input :
  TRB.InstanceB.W ∣ [] ⊢²
    TRB.InstanceB.source ⊑ TRB.InstanceB.target-tagged ∶
      TRB.InstanceB.X⊑★-W
terminus-instanceB-live-tagged-input = TRB.InstanceB.tagged-input

terminus-instanceB-inner-dyn-id-ok :
  SealPartnerOK {Δᴸ = 1} {Δᴿ = 2} ★
    (just TRB.InstanceB.Y₂) TRB.InstanceB.U₀
terminus-instanceB-inner-dyn-id-ok = star-rep-target

terminus-instanceB-inner-dyn-id-live :
  TRB.InstanceB.Wᵖ ∣ [] ⊢²
    TRB.InstanceB.V ⊑ TRB.InstanceB.U₀ ∶
      TRB.InstanceB.X⊑★-Wᵖ
terminus-instanceB-inner-dyn-id-live =
  TRB.InstanceB.inner-source-seal²

seal-descent-at-var-＇-reemit-instance :
  TDD.TargetSealReemit TRB.InstanceB.W [] TRB.InstanceB.source-payload
    TRB.InstanceB.U TRB.InstanceB.X TRB.InstanceB.Y TRB.InstanceB.Y₂
    TRB.InstanceB.X⊑Y
seal-descent-at-var-＇-reemit-instance =
  TDP.target-seal＇-reemit TRB.InstanceB.mono-W-Wᵖ
    TRB.InstanceB.rb-chain CTX.same-[] TRB.InstanceB.Y∈
    TRB.InstanceB.X⊑Y TRB.InstanceB.X⊑Y₂

------------------------------------------------------------------------
-- Q3. `left-path-argument₄`
------------------------------------------------------------------------

left-path-argument₄-old-wrapper-empty :
  SealPartnerOK {Δᴸ = 3} {Δᴿ = 2} (‵ `ℕ) nothing
    (($ (κℕ 7)) ⟨ Ex2.left-path-ℕ!₂ ⟩)
  → ⊥
left-path-argument₄-old-wrapper-empty (plain-target ())

left-path-argument₄-payload-survives :
  Ex2.left-path-world₄-YZ ∣ [] ⊢² $ (κℕ 7)
    ⊑ $ (κℕ 7) ⟨ Ex2.left-path-ℕ!₂ ⟩ ∶
      Ex2.left-path-ℕ⊑★₄-YZ
left-path-argument₄-payload-survives =
  Ex2.left-path-argument₄-base

------------------------------------------------------------------------
-- Q4. Dossier-level gates unchanged by the refined predicate
------------------------------------------------------------------------

example12-checkpoint₁-gate-refined :
  Ex12.example12-world-X ∣ [] ⊢² Ex.left₁ ⊑ Ex.right₃ ∶
    Ex2.example12-ℕ⊑ℕ-X
example12-checkpoint₁-gate-refined = TD.example12-checkpoint₁-gate

example12-paired-seal-gate-refined :
  Ex12.example12-world-X ∣ [] ⊢²
    ($ (κℕ 7)) ↓ Ex2.example12-source-X-seal
    ⊑ ($ (κℕ 7)) ↓ Ex2.example12-target-X-seal ∶
      Ex2.example12-X-var⊑
example12-paired-seal-gate-refined = TD.example12-paired-seal-gate

compile-preserves-imprecision²-gate-refined :
  CPI2.compile-preserves-imprecision²-statement
compile-preserves-imprecision²-gate-refined =
  TD.compile-preserves-imprecision²-gate
