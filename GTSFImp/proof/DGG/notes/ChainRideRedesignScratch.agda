module ChainRideRedesignScratch where

-- Pre-M2 design record.  This scratch depends on old source-star and
-- chain-ride exploration modules that exercised target-moving freedom.
-- It is intentionally excluded from the M2 check set after RebaseAt
-- froze old target centers.

-- File Charter:
--   * Records the consumer-driven chain-ride interface for the
--     extra-cast-right seal/tag boundary.
--   * Deliberately has no source-star branch producing
--     (＇ X) ⊑ᵂ (＇ Y′) for a foreign target variable.
--   * Re-derives the live OpenStrata exports and probe gates from the
--     corrected consumer statements only.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; X∼★; _⊢_∼_; toRenameᵗ; id; _!)
open import Conversion using (seal)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _↓_)
import CastTerms as CTerms
open import Primitives using (κℕ)

import SourceStarCounterScratch as SSC
import SourceStarRideCounterScratch as SSRC
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.MovedLinkProbe as MLP
import proof.DGG.SealTransfer as ST
import proof.DGG.TagBoundaryProbe as TBP
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; sourceStoreʷ;
   targetStoreʷ; ηᴸʷ; _∣_⊢²_⊑_∶_)
open ECR using (SpineValue)

------------------------------------------------------------------------
-- Corrected consumer-facing branch packages
------------------------------------------------------------------------

data TargetSealRide {Δᴸ Δᴿ Δ}
    {W₀ : World Δᴸ Δᴿ Δ} {γ₀ : CtxImp W₀}
    {P : Term Δᴸ} {U : Term Δᴿ}
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ)
    : Ty Δᴿ → Set where
  target-seal★ :
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W₀ Xᵒ Yᵒ
      × CTI2.ImpEnvMono W₀ Wᵒ
      × CTI2.SameCtx γ₀ γᵒ
      × Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢² P ↓ seal Xᵒ ★ ⊑ U ∶ qᵒ) )
    → TargetSealRide Xᵒ Yᵒ ★

  target-seal＇ : ∀ {Y′}
    → Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ W₀ ⟩ (＇ Yᵒ) ]
        (W₀ ∣ γ₀ ⊢²
          P ↓ seal Xᵒ ★ ⊑ U ↓ seal Yᵒ (＇ Y′) ∶ qᵒ)
    → TargetSealRide Xᵒ Yᵒ (＇ Y′)

record ChainRideRedesign : Set where
  field
    H-walk : ∀ {Δᴸ Δᴿ Δ}
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
      → W ∣ γ ⊢² V ↓ seal Xᴸ R
          ⊑ U ↓ seal Y S ∶ q

    source-chain : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → RebaseAt W′ W Xᴸ Y
      → RebaseAt W₂ W′ X₂ Y
      → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
      → CTI2.ImpEnvMono W W′
      → CTI2.ImpEnvMono W′ W₂
      → CTI2.SameCtx γ γ′
      → CTI2.SameCtx γ′ γ₂
      → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
          ( RebaseAt Wᵒ W Xᴸ Y
          × CTI2.ImpEnvMono W Wᵒ
          × CTI2.SameCtx γ γᵒ
          × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
              (Wᵒ ∣ γᵒ ⊢²
                V ↓ seal Xᴸ (＇ X₂) ⊑ U ∶ qᵒ) )

    source-chain-transfer : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → RebaseAt W′ W Xᴸ Y
      → RebaseAt W₂ W′ X₂ Y
      → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W) X₂
      → CTI2.ImpEnvMono W W′
      → CTI2.ImpEnvMono W′ W₂
      → CTI2.SameCtx γ γ′
      → CTI2.SameCtx γ′ γ₂
      → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
          ( RebaseAt Wᵒ W Xᴸ Y
          × CTI2.ImpEnvMono W Wᵒ
          × CTI2.SameCtx γ γᵒ
          × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
              (Wᵒ ∣ γᵒ ⊢²
                V ↓ seal Xᴸ (＇ X₂) ⊑ U ∶ qᵒ) )

    source-star★ : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → SpineValue V
      → Inert c
      → Value U
      → RebaseAt W′ W Xᴸ Y
      → RebaseAt W₂ W′ X₂ Y₂
      → CTI2.ImpEnvMono W W′
      → CTI2.ImpEnvMono W′ W₂
      → CTI2.SameCtx γ γ′
      → CTI2.SameCtx γ′ γ₂
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
          ( RebaseAt Wᵒ W Xᴸ Y
          × CTI2.ImpEnvMono W Wᵒ
          × CTI2.SameCtx γ γᵒ
          × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
              (Wᵒ ∣ γᵒ ⊢²
                (V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U ∶ qᵒ) )

    target-seal : ∀ {Δᴸ Δᴿ Δ}
        {W W′ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      → SpineValue V
      → Inert c
      → Value U
      → CTI2.ImpEnvMono W W′
      → RebaseAt W′ W Xᴸ Y
      → CTI2.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → targetStoreʷ W ∋ Y ⦂ S
      → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
      → TargetSealRide {W₀ = W} {γ₀ = γ} {P = V ⟨ c ⟩} {U}
          Xᴸ Y S

------------------------------------------------------------------------
-- Exports consumed by SealTransfer and ExtraCastRight2
------------------------------------------------------------------------

seal-transfer-assumption : ChainRideRedesign
  → ST.SealTransferAssumption
seal-transfer-assumption core = record
  { H-multi = λ ra link moved mono mono₂ sc sc₂ X∈ D →
      ChainRideRedesign.source-chain-transfer core
        ra link moved mono mono₂ sc sc₂ X∈ D
  }

tag-transfer-from-redesign : ChainRideRedesign
  → ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {V : Term Δᴸ} {U : Term Δᴿ}
    {X : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {p : (＇ X) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Value U
  → W ∣ γ ⊢² V ⊑ U ↓ seal Y ★ ∶ p
  → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W X Y
      × CTI2.ImpEnvMono W Wᵒ
      × CTI2.SameCtx γ γᵒ
      × Σ[ qᵒ ∈ (＇ X) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢² V ⊑ U ∶ qᵒ) )
tag-transfer-from-redesign core =
  ST.seal-transfer (seal-transfer-assumption core)

H-Schain-from-redesign : ChainRideRedesign
  → ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
    {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
  → SpineValue V
  → Inert c
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y (＇ Y₂) ∶ p₂
  → W ∣ γ ⊢²
      (V ⟨ c ⟩) ↓ seal Xᴸ ★
      ⊑ U ↓ seal Y (＇ Y₂) ∶ q
H-Schain-from-redesign core sv inert vU mono rb sc X∈ Y∈ D
    with ChainRideRedesign.target-seal core
      sv inert vU mono rb sc X∈ Y∈ D
H-Schain-from-redesign core sv inert vU mono rb sc X∈ Y∈ D
    | target-seal＇ (qᵒ , out) =
  CR.⊢²-retarget out

H-absorb-from-redesign : ChainRideRedesign
  → ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
    {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
    {q : (＇ Xᴸ) ⊑ᵂ⟨ W ⟩ (＇ Y)}
    {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
  → SpineValue V
  → Inert c
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y ★ ∶ p₂
  → RebaseAt W₂ W′ X₂ Y
  → CTI2.ImpEnvMono W′ W₂
  → CTI2.SameCtx γ′ γ₂
  → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
  → W ∣ γ ⊢²
      (V ⟨ c ⟩) ↓ seal Xᴸ ★
      ⊑ U ↓ seal Y ★ ∶ q
H-absorb-from-redesign core {q = q} sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    with ChainRideRedesign.source-star★ core
      sv inert vU rb link mono mono₂ sc sc₂ X∈ D₂
H-absorb-from-redesign core {q = q} sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    | Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , rᵒ , Dᵒ =
  CTI2.⊑conceal² monoᵒ (CTI2.rebase-varᴿ rbᵒ) scᵒ
    (Conv.⊢↓-sealˣ Y∈) Dᵒ q

H-multi-from-redesign : ChainRideRedesign
  → ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
  → SpineValue V
  → Value U
  → RebaseAt W′ W Xᴸ Y
  → RebaseAt W₂ W′ X₂ Y
  → CTI2.ImpEnvMono W W′
  → CTI2.ImpEnvMono W′ W₂
  → CTI2.SameCtx γ γ′
  → CTI2.SameCtx γ′ γ₂
  → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
  → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
  → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W Xᴸ Y
      × CTI2.ImpEnvMono W Wᵒ
      × CTI2.SameCtx γ γᵒ
      × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            V ↓ seal Xᴸ (＇ X₂) ⊑ U ∶ qᵒ) )
H-multi-from-redesign core sv vU rb link mono mono₂ sc sc₂ X∈ D moved =
  ChainRideRedesign.source-chain core
    rb link moved mono mono₂ sc sc₂ X∈ D

open-strata-from-redesign : ChainRideRedesign → ECR.OpenStrata
open-strata-from-redesign core = record
  { seal-transfer = tag-transfer-from-redesign core
  ; H-walk = ChainRideRedesign.H-walk core
  ; H-Schain = H-Schain-from-redesign core
  ; H-absorb = H-absorb-from-redesign core
  }

------------------------------------------------------------------------
-- Probe gates
------------------------------------------------------------------------

ChainRideProbe-from-redesign : ChainRideRedesign
  → Σ[ Wᵒ ∈ World 2 1 3 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ CRP.W₁ Fin.zero Fin.zero
      × CTI2.ImpEnvMono CRP.W₁ Wᵒ
      × CTI2.SameCtx {W = CRP.W₁} [] γᵒ
      × Σ[ qᵒ ∈ (＇ Fin.zero) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            CRP.V ↓ seal Fin.zero (＇ Fin.suc Fin.zero)
            ⊑ CRP.U ∶ qᵒ) )
ChainRideProbe-from-redesign core =
  ChainRideRedesign.source-chain core
    CRP.raₗ CRP.link₂ CRP.probe-moved
    CRP.probe-mono₁ₗ CRP.probe-monoₗ₂
    CRP.probe-same₁ₗ CRP.probe-sameₗ₂
    CRP.probe-Z∋ CRP.probe-premise

private
  tag-source-env : Env∼ 1
  tag-source-env Fin.zero = X∼★

  tag-X! : tag-source-env ⊢ (＇ Fin.zero) ∼ ★
  tag-X! = id (＇ Fin.zero) !

  tag-source-value : SpineValue TBP.probe-V
  tag-source-value =
    ECR.sv-seal (ECR.sv-cast (ECR.sv-$ (κℕ 0)) CTerms.inj)

  tag-inner-target-value : Value TBP.probe-M₅
  tag-inner-target-value =
    CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》

  tag-target-value : Value TBP.probe-M′
  tag-target-value =
    tag-inner-target-value
      CTerms.↓ (CTerms.seal {X = Fin.suc Fin.zero} {R = ★})

TagBoundaryProbe-target-only-node :
  TBP.probe-W₄ ∣ [] ⊢² TBP.probe-V ⊑ TBP.probe-M′ ∶ TBP.pTag
TagBoundaryProbe-target-only-node = TBP.probe-inner-seal²

TagBoundaryProbe-transfer-from-redesign : ChainRideRedesign
  → Σ[ Wᵒ ∈ World 1 2 2 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ TBP.probe-W₄ Fin.zero (Fin.suc Fin.zero)
      × CTI2.ImpEnvMono TBP.probe-W₄ Wᵒ
      × CTI2.SameCtx {W = TBP.probe-W₄} [] γᵒ
      × Σ[ qᵒ ∈ (＇ Fin.zero) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            TBP.probe-V ⊑ TBP.probe-M₅ ∶ qᵒ) )
TagBoundaryProbe-transfer-from-redesign core =
  tag-transfer-from-redesign core
    tag-source-value tag-inner-target-value TBP.probe-inner-seal²

TagBoundaryProbe-outer-output-refuted :
  ¬ (TBP.probe-W₁ ∣ [] ⊢² TBP.probe-V ⊑ TBP.probe-U ∶ TBP.qOut)
TagBoundaryProbe-outer-output-refuted = TBP.probe-no-output

TagBoundaryProbe-old-ride-shape-refuted :
  ChainRideRedesign → ¬ SSRC.source-star-branch-output
TagBoundaryProbe-old-ride-shape-refuted core =
  SSRC.no-source-star-branch-output

SourceStar-old-naked-shape-refuted :
  ChainRideRedesign → ¬ SSC.source-star-var-output
SourceStar-old-naked-shape-refuted core =
  SSC.no-source-star-var-output

MovedLinkProbe-excluded :
  ¬ (RebaseAt MLP.probe-W₅ MLP.probe-W₄
      Fin.zero (Fin.suc Fin.zero))
MovedLinkProbe-excluded = MLP.probe-link-ill-formed

example12-target-Z-never-moves :
  toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-world-X)
    (Fin.suc (Fin.suc Fin.zero))
  ≡ toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-world-Z)
    (Fin.suc (Fin.suc Fin.zero))
example12-target-Z-never-moves = refl

example12-nat-chain-target-Y-never-moves :
  toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-nat-chain-world-X) Fin.zero
  ≡ toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-nat-chain-world-Y) Fin.zero
example12-nat-chain-target-Y-never-moves = refl

example12-left-path-first-park :
  toRenameᵗ (CTI2.ηᴸʷ CTI2.example12-left-path-world-X) Fin.zero
  ≡ toRenameᵗ (CTI2.ηᴿʷ CTI2.example12-left-path-world-X) Fin.zero
example12-left-path-first-park = refl
