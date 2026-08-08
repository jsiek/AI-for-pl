module proof.DGG.Inversion.SourceStripDef where

-- File Charter:
--   * States the source-spine strip surface used to derive the target
--     tag/seal walk.
--   * Packages core rebuilds with the boundary rebases needed by source
--     re-emission and an existential target-chain terminus.
--   * Keeps the statement independent of the proof script and exposes only
--     the small source-atom surface consumed by the core rebuild proof.

open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_)
open import Conversion using (seal)
open import CastTerms
open import Imprecision
import proof.DGG.CastTermImprecision2 as CTI2
open import proof.DGG.Inversion.SpineValueDef using (SpineValue)
open CTI2 using
  (World; CtxImp; RebaseAt; RebaseAtᴸ; _⊑ᵂ⟨_⟩_;
   _∣_⊢²_⊑_∶_; sourceStoreʷ; targetStoreʷ)

------------------------------------------------------------------------
-- Core atoms
------------------------------------------------------------------------

data SourceAtom {Δ : TyCtx} : Term Δ → Set where
  atom-ƛ : ∀ N → SourceAtom (ƛ N)

  atom-Λ : ∀ {V}
    → SpineValue V
    → SourceAtom (Λ V)

  atom-$ : ∀ κ → SourceAtom ($ κ)

------------------------------------------------------------------------
-- Rebuild packages
------------------------------------------------------------------------

record TargetChainData {Δᴸ Δᴿ Δ}
    (Wᶜ : World Δᴸ Δᴿ Δ) (γᶜ : CtxImp Wᶜ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ) : Set where
  constructor target-chain-data
  field
    Y★ : TyVar Δᴿ
    S★ : Ty Δᴿ
    S★≡★ : S★ ≡ ★
    W★ : World Δᴸ Δᴿ Δ
    γ★ : CtxImp W★
    mono★ : CTI2.ImpEnvMono Wᶜ W★
    same★ : CTI2.SameCtx γᶜ γ★
    boundary★ : RebaseAt W★ Wᶜ Xᴸ Y★
    target∈★ : targetStoreʷ W★ ∋ Y★ ⦂ S★
    q★ : A ⊑ᵂ⟨ W★ ⟩ S★
    premise★ : W★ ∣ γ★ ⊢² P ⊑ U ∶ q★

data CoreRebuild {Δᴸ Δᴿ Δ}
    (Wᶜ : World Δᴸ Δᴿ Δ) (γᶜ : CtxImp Wᶜ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Xᴸ : TyVar Δᴸ)
    (Y : TyVar Δᴿ) (S : Ty Δᴿ) : Set where
  core-sealed :
      (Wʳ : World Δᴸ Δᴿ Δ)
      (γʳ : CtxImp Wʳ)
    → CTI2.ImpEnvMono Wᶜ Wʳ
    → CTI2.SameCtx γᶜ γʳ
    → RebaseAtᴸ Wʳ Wᶜ (just Xᴸ)
    → targetStoreʷ Wʳ ∋ Y ⦂ S
    → (qʳ : A ⊑ᵂ⟨ Wʳ ⟩ (＇ Y))
    → Wʳ ∣ γʳ ⊢² P ⊑ U ↓ seal Y S ∶ qʳ
    → CoreRebuild Wᶜ γᶜ P A U Xᴸ Y S

  core-terminus :
    TargetChainData Wᶜ γᶜ P A U Xᴸ Y S
    → CoreRebuild Wᶜ γᶜ P A U Xᴸ Y S

data SourceCorePremise {Δᴸ Δᴿ Δ}
    (Wᶜ : World Δᴸ Δᴿ Δ) (γᶜ : CtxImp Wᶜ)
    (P : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (Y : TyVar Δᴿ) (S : Ty Δᴿ)
    (pᶜ : A ⊑ᵂ⟨ Wᶜ ⟩ ★)
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★) : Set where
  core-tagged :
    Wᶜ ∣ γᶜ ⊢² P ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ pᶜ
    → SourceCorePremise Wᶜ γᶜ P A U Y S pᶜ cY

  core-untagged :
      (rᶜ : A ⊑ᵂ⟨ Wᶜ ⟩ (＇ Y))
    → Wᶜ ∣ γᶜ ⊢² P ⊑ U ↓ seal Y S ∶ rᶜ
    → SourceCorePremise Wᶜ γᶜ P A U Y S pᶜ cY

------------------------------------------------------------------------
-- Source strip surfaces
------------------------------------------------------------------------

record SourceSpineStripResult {Δᴸ Δᴿ Δ}
    (W₀ : World Δᴸ Δᴿ Δ) (γ₀ : CtxImp W₀)
    (V : Term Δᴸ) (U : Term Δᴿ)
    (R : Ty Δᴸ) (S : Ty Δᴿ)
    (X₀ : TyVar Δᴸ) (Y : TyVar Δᴿ)
    (q₀ : (＇ X₀) ⊑ᵂ⟨ W₀ ⟩ (＇ Y))
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★) : Set where
  constructor source-strip
  field
    Core : Term Δᴸ
    CoreTy : Ty Δᴸ
    Wᵒ : World Δᴸ Δᴿ Δ
    γᵒ : CtxImp Wᵒ
    qᵒ : (＇ X₀) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)
    Wᵖ : World Δᴸ Δᴿ Δ
    γᵖ : CtxImp Wᵖ
    pᵖ : CoreTy ⊑ᵂ⟨ Wᵖ ⟩ ★
    monoᵒᵖ : CTI2.ImpEnvMono Wᵒ Wᵖ
    sameᵒᵖ : CTI2.SameCtx γᵒ γᵖ
    boundaryᵖᵒ : RebaseAt Wᵖ Wᵒ X₀ Y
    atomᶜ : SourceAtom Core
    target∈ᵒ : targetStoreʷ Wᵒ ∋ Y ⦂ S
    premiseᶜ :
      SourceCorePremise Wᵖ γᵖ Core CoreTy U Y S pᵖ cY
    resume :
      CoreRebuild Wᵒ γᵒ Core CoreTy U X₀ Y S
      → W₀ ∣ γ₀ ⊢² V ↓ seal X₀ R ⊑ U ↓ seal Y S ∶ q₀

SourceSpineStrip : Set
SourceSpineStrip =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {R : Ty Δᴸ} {S : Ty Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p₀ : R ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ R
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p₀
  → SourceSpineStripResult W γ V U R S Xᴸ Y q cY

record SourceColumnStripResult {Δᴸ Δᴿ Δ}
    (W₀ : World Δᴸ Δᴿ Δ) (γ₀ : CtxImp W₀)
    (V : Term Δᴸ) (A : Ty Δᴸ)
    (U : Term Δᴿ) (S : Ty Δᴿ) (Y : TyVar Δᴿ)
    (X₀ : TyVar Δᴸ)
    (q₀ : (＇ X₀) ⊑ᵂ⟨ W₀ ⟩ (＇ Y))
    {ν : Env∼ Δᴿ} (cY : ν ⊢ (＇ Y) ∼ ★) : Set where
  constructor source-column-strip
  field
    Core : Term Δᴸ
    CoreTy : Ty Δᴸ
    Wᵒ : World Δᴸ Δᴿ Δ
    γᵒ : CtxImp Wᵒ
    qᵒ : (＇ X₀) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)
    Wᵖ : World Δᴸ Δᴿ Δ
    γᵖ : CtxImp Wᵖ
    pᵖ : CoreTy ⊑ᵂ⟨ Wᵖ ⟩ ★
    monoᵒᵖ : CTI2.ImpEnvMono Wᵒ Wᵖ
    sameᵒᵖ : CTI2.SameCtx γᵒ γᵖ
    boundaryᵖᵒ : RebaseAt Wᵖ Wᵒ X₀ Y
    atomᶜ : SourceAtom Core
    target∈ᵒ : targetStoreʷ Wᵒ ∋ Y ⦂ S
    premiseᶜ :
      SourceCorePremise Wᵖ γᵖ Core CoreTy U Y S pᵖ cY
    resume :
      CoreRebuild Wᵒ γᵒ Core CoreTy U X₀ Y S
      → W₀ ∣ γ₀ ⊢² V ⊑ U ↓ seal Y S ∶ q₀

SourceColumnStrip : Set
SourceColumnStrip =
  ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : (＇ Xᴸ) ⊑ᵂ⟨ W′ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → targetStoreʷ W ∋ Y ⦂ S
  → W′ ∣ γ′ ⊢² V ⊑ (U ↓ seal Y S) ⟨ cY ⟩ ∶ p
  → SourceColumnStripResult W γ V (＇ Xᴸ) U S Y Xᴸ q cY

SourceTagSealCore : Set
SourceTagSealCore =
  ∀ {Δᴸ Δᴿ Δ}
    {Wᵒ Wᵖ : World Δᴸ Δᴿ Δ}
    {γᵒ : CtxImp Wᵒ} {γᵖ : CtxImp Wᵖ}
    {P : Term Δᴸ} {U : Term Δᴿ}
    {A : Ty Δᴸ} {S : Ty Δᴿ} {Xᴸ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴿ} {cY : ν ⊢ (＇ Y) ∼ ★}
    {p : A ⊑ᵂ⟨ Wᵖ ⟩ ★}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y)}
  → SourceAtom P
  → Value U
  → CTI2.ImpEnvMono Wᵒ Wᵖ
  → RebaseAt Wᵖ Wᵒ Xᴸ Y
  → CTI2.SameCtx γᵒ γᵖ
  → targetStoreʷ Wᵒ ∋ Y ⦂ S
  → SourceCorePremise Wᵖ γᵖ P A U Y S p cY
  → CoreRebuild Wᵒ γᵒ P A U Xᴸ Y S
