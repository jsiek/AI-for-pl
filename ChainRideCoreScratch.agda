module ChainRideCoreScratch where

-- Pre-M2 design record.  This scratch depends on the old chain-ride
-- exploration surface and the removed SourceStarCounterScratch module.
-- It is intentionally excluded from the M2 check set after target
-- centers were frozen by RebaseAt.

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
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CenterRename as CR
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.ChainRideProbe as CRP
import proof.DGG.MovedLinkProbe as MLP
import proof.DGG.SealChainView as SCV
import proof.DGG.TagBoundaryProbe as TBP
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; sourceStoreʷ;
   targetStoreʷ; ηᴸʷ; _∣_⊢²_⊑_∶_)
open ECR using (SpineValue)

------------------------------------------------------------------------
-- Branch-dependent terminal rides
------------------------------------------------------------------------

-- The terminal source-star ride deliberately splits on the right type.
-- The ★ branch returns the old source-only package, including the
-- accumulator link to the original outer pivot.  The variable branch returns
-- a paired-seal derivation directly and does not return a RebaseAt package
-- pivoted at the original target variable.  This is why the statement below
-- does not imply SourceStarCounterScratch.source-star-var-output.
--
-- The variable branch is intentionally opaque at the statement boundary.
-- Its witness is not one immediate paired conceal node, because that would
-- need ★ ⊑ ＇ Y at the paired premise.  The proof descends the target store
-- telescope instead: each variable entry exposes the target value's next seal
-- by canonical forms, emits a target-only seal node, and recurses on the next
-- target membership.  Store representations force the chain to terminate at
-- ★, where the source ★ seal pairs with the target ★ seal by
-- conceal⊑conceal²; the target-only nodes are then re-emitted outward.

data SourceStarRide {Δᴸ Δᴿ Δ}
    {W₀ : World Δᴸ Δᴿ Δ} {γ₀ : CtxImp W₀}
    {P : Term Δᴸ} {U : Term Δᴿ}
    (Xᵒ : TyVar Δᴸ) (Yᵒ : TyVar Δᴿ)
    : Ty Δᴿ → Set where
  source-star★ :
    Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W₀ Xᵒ Yᵒ
      × CTI2.ImpEnvMono W₀ Wᵒ
      × CTI2.SameCtx γ₀ γᵒ
      × Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢² P ↓ seal Xᵒ ★ ⊑ U ∶ qᵒ) )
    → SourceStarRide Xᵒ Yᵒ ★

  source-star＇ : ∀ {Y′ S′ U₀}
    → U ≡ U₀ ↓ seal Y′ S′
    → Value U₀
    → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
        ( CTI2.ImpEnvMono W₀ Wᵒ
        × CTI2.SameCtx γ₀ γᵒ
        × sourceStoreʷ Wᵒ ∋ Xᵒ ⦂ ★
        × targetStoreʷ Wᵒ ∋ Y′ ⦂ S′
        × Σ[ qᵒ ∈ (＇ Xᵒ) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Y′) ]
            (Wᵒ ∣ γᵒ ⊢²
              P ↓ seal Xᵒ ★ ⊑ U₀ ↓ seal Y′ S′ ∶ qᵒ) )
    → SourceStarRide Xᵒ Yᵒ (＇ Y′)

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

record ChainRideBranchInterface : Set where
  field
    source-var : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → SpineValue V
      → Value U
      → RebaseAt W′ W Xᴸ Y
      → RebaseAt W₂ W′ X₂ Y₂
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

    source-star : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
        {B : Ty Δᴿ} {ν : Env∼ Δᴸ}
        {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ B}
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
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ p₂
      → SourceStarRide {W₀ = W} {γ₀ = γ} {P = V ⟨ c ⟩} {U}
          Xᴸ Y B

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

source-chain-from-branch : ChainRideBranchInterface
  → ∀ {Δᴸ Δᴿ Δ}
    {W W′ W₂ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
    {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
  → SpineValue V
  → Value U
  → RebaseAt W′ W Xᴸ Y
  → RebaseAt W₂ W′ X₂ Y₂
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
source-chain-from-branch core =
  ChainRideBranchInterface.source-var core

source-star★-from-branch : ChainRideBranchInterface
  → ∀ {Δᴸ Δᴿ Δ}
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
source-star★-from-branch core sv inert vU rb link mono mono₂
    sc sc₂ X∈ D
    with ChainRideBranchInterface.source-star core
      sv inert vU rb link mono mono₂ sc sc₂ X∈ D
source-star★-from-branch core sv inert vU rb link mono mono₂
    sc sc₂ X∈ D
    | source-star★ out =
  out

target-seal★-from-branch : ChainRideBranchInterface
  → ∀ {Δᴸ Δᴿ Δ}
    {W W′ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {γ′ : CtxImp W′}
    {V : Term Δᴸ} {U : Term Δᴿ}
    {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ}
    {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
    {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
  → SpineValue V
  → Inert c
  → Value U
  → CTI2.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTI2.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y ★ ∶ p₂
  → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W Xᴸ Y
      × CTI2.ImpEnvMono W Wᵒ
      × CTI2.SameCtx γ γᵒ
      × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            (V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U ∶ qᵒ) )
target-seal★-from-branch core sv inert vU mono rb sc X∈ Y∈ D
    with ChainRideBranchInterface.target-seal core
      sv inert vU mono rb sc X∈ Y∈ D
target-seal★-from-branch core sv inert vU mono rb sc X∈ Y∈ D
    | target-seal★ out =
  out

H-Schain-from-branch : ChainRideBranchInterface
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
H-Schain-from-branch core sv inert vU mono rb sc X∈ Y∈ D
    with ChainRideBranchInterface.target-seal core
      sv inert vU mono rb sc X∈ Y∈ D
H-Schain-from-branch core sv inert vU mono rb sc X∈ Y∈ D
    | target-seal＇ (qᵒ , out) =
  CR.⊢²-retarget out

H-absorb-from-branch : ChainRideBranchInterface
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
H-absorb-from-branch core {q = q} sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    with source-star★-from-branch core
      sv inert vU rb link mono mono₂ sc sc₂ X∈ D₂
H-absorb-from-branch core {q = q} sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    | Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , rᵒ , Dᵒ =
  CTI2.⊑conceal² monoᵒ (CTI2.rebase-varᴿ rbᵒ) scᵒ
    (CTI2.⊢↓-sealˣ Y∈) Dᵒ q

H-multi-from-branch = source-chain-from-branch

------------------------------------------------------------------------
-- Probe and example gates
------------------------------------------------------------------------

ChainRideProbe-from-branch : ChainRideBranchInterface
  → Σ[ Wᵒ ∈ World 2 1 3 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ CRP.W₁ Fin.zero Fin.zero
      × CTI2.ImpEnvMono CRP.W₁ Wᵒ
      × CTI2.SameCtx {W = CRP.W₁} [] γᵒ
      × Σ[ qᵒ ∈ (＇ Fin.zero) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            CRP.V ↓ seal Fin.zero (＇ Fin.suc Fin.zero)
            ⊑ CRP.U ∶ qᵒ) )
ChainRideProbe-from-branch core =
  source-chain-from-branch core
    (ECR.sv-seal (ECR.sv-cast (ECR.sv-$ (κℕ 0)) CTerms.inj))
    (CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》)
    CRP.raₗ CRP.link₂ CRP.probe-mono₁ₗ CRP.probe-monoₗ₂
    CRP.probe-same₁ₗ CRP.probe-sameₗ₂ CRP.probe-Z∋
    CRP.probe-premise CRP.probe-moved

private
  tag-source-env : Env∼ 1
  tag-source-env Fin.zero = X∼★

  tag-X! : tag-source-env ⊢ (＇ Fin.zero) ∼ ★
  tag-X! = id (＇ Fin.zero) !

  tag-source-value : SpineValue TBP.probe-V
  tag-source-value =
    ECR.sv-seal (ECR.sv-cast (ECR.sv-$ (κℕ 0)) CTerms.inj)

  tag-target-value : Value TBP.probe-M′
  tag-target-value =
    (CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》)
      CTerms.↓ (CTerms.seal {X = Fin.suc Fin.zero} {R = ★})

  tag-id-rebase : RebaseAt TBP.probe-W₁ TBP.probe-W₁ Fin.zero Fin.zero
  tag-id-rebase =
    CTI2.sameWorldRebaseAt refl TBP.probe-X-Y-rep₁

  tag-id-mono : CTI2.ImpEnvMono TBP.probe-W₁ TBP.probe-W₁
  tag-id-mono Z eq = eq

  tag-outer-mono : CTI2.ImpEnvMono TBP.probe-W₁ TBP.probe-W₄
  tag-outer-mono Z eq = eq

TagBoundaryProbe-from-branch : ChainRideBranchInterface
  → Σ[ Wᵒ ∈ World 1 2 2 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( CTI2.ImpEnvMono TBP.probe-W₁ Wᵒ
      × CTI2.SameCtx {W = TBP.probe-W₁} [] γᵒ
      × sourceStoreʷ Wᵒ ∋ Fin.zero ⦂ ★
      × targetStoreʷ Wᵒ ∋ Fin.suc Fin.zero ⦂ ★
      × Σ[ qᵒ ∈
          (＇ Fin.zero) ⊑ᵂ⟨ Wᵒ ⟩ (＇ Fin.suc Fin.zero) ]
          (Wᵒ ∣ γᵒ ⊢²
            (TBP.probe-V ⟨ tag-X! ⟩) ↓ seal Fin.zero ★
            ⊑ TBP.probe-M′ ∶ qᵒ) )
TagBoundaryProbe-from-branch core
    with ChainRideBranchInterface.source-star core
      {ν = tag-source-env} {c = tag-X!}
      tag-source-value CTerms.inj tag-target-value
      tag-id-rebase TBP.probe-outer-target-rebase
      tag-id-mono tag-outer-mono CTI2.same-[] CTI2.same-[]
      TBP.probe-src-X∋ TBP.probe-inner-seal²
TagBoundaryProbe-from-branch core
    | source-star＇ refl vU₀ out =
  out

MovedLinkProbe-excluded = MLP.probe-link-ill-formed

source-star-counterexample-still-refuted :
  ¬ SSC.source-star-var-output
source-star-counterexample-still-refuted =
  SSC.no-source-star-var-output

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
