module proof.DGG.SealChain where

-- File Charter:
--   * Records the consumer-facing ChainRideRedesign interface for the
--     extra-cast-right seal/tag boundary while the requested implementation is
--     blocked by TargetSealVariableCounterScratch.
--   * Exports the corrected target-seal packages and abstract corollaries
--     consumed by SealTransferCore and ExtraCastRight2.
--   * Deliberately has no variable-target source-star branch; the root
--     SourceStarCounterScratch and SourceStarRideCounterScratch files are the
--     checked design record for that refuted shape.

import Data.Fin as Fin
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import Imprecision
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _↓_)
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.SealTransferCore as STC
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; targetStoreʷ; ηᴸʷ)
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
-- Exports consumed by SealTransferCore and ExtraCastRight2
------------------------------------------------------------------------

seal-transfer-assumption : ChainRideRedesign
  → STC.SealTransferAssumption
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
  STC.seal-transfer (seal-transfer-assumption core)

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
    (CTI2.⊢↓-sealˣ Y∈) Dᵒ q

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
