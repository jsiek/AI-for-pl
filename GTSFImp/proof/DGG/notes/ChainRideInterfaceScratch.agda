module ChainRideInterfaceScratch where

-- Pre-M2 design record.  This scratch refers to the old positive
-- ChainRideProbe links (`raₗ`/`link₂`), which M2 replaced with
-- emptiness records because old target centers are frozen by RebaseAt.
-- It is intentionally excluded from the M2 check set.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

open import Types
open import TyStore using (_∋_⦂_)
open import Consistency using (Env∼; _⊢_∼_; toRenameᵗ)
open import Conversion using (seal)
open import CastTerms using (Term; Value; Inert; _⟨_⟩; _↓_)
import CastTerms as CTerms
open import Primitives using (κℕ)
open import Imprecision
import Conversion as Conv
import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
import proof.DGG.ChainRideProbe as CRP
open CTX using
  (World;
   CtxImp;
   RebaseAt;
   _⊑ᵂ⟨_⟩_;
   sourceStoreʷ;
   targetStoreʷ;
   ηᴸʷ)
open CTI2 using (_∣_⊢²_⊑_∶_)
open ECR using (SpineValue)

record ChainRideInterface : Set where
  field
    target-chain-ride : ∀ {Δᴸ Δᴿ Δ}
        {W W′ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y : TyVar Δᴿ} {S : Ty Δᴿ}
        {ν : Env∼ Δᴸ} {c : ν ⊢ (＇ X₂) ∼ ★}
        {p₂ : (＇ X₂) ⊑ᵂ⟨ W′ ⟩ (＇ Y)}
      → SpineValue V
      → Inert c
      → Value U
      → CTX.ImpEnvMono W W′
      → RebaseAt W′ W Xᴸ Y
      → CTX.SameCtx γ γ′
      → sourceStoreʷ W ∋ Xᴸ ⦂ ★
      → targetStoreʷ W ∋ Y ⦂ S
      → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y S ∶ p₂
      → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
          ( RebaseAt Wᵒ W Xᴸ Y
          × CTX.ImpEnvMono W Wᵒ
          × CTX.SameCtx γ γᵒ
          × Σ[ r ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ S ]
              (Wᵒ ∣ γᵒ ⊢²
                (V ⟨ c ⟩) ↓ seal Xᴸ ★ ⊑ U ∶ r) )

    source-chain-ride : ∀ {Δᴸ Δᴿ Δ}
        {W W′ W₂ : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W} {γ′ : CtxImp W′} {γ₂ : CtxImp W₂}
        {V : Term Δᴸ} {U : Term Δᴿ}
        {Xᴸ X₂ : TyVar Δᴸ} {Y Y₂ : TyVar Δᴿ}
        {q₂ : (＇ X₂) ⊑ᵂ⟨ W₂ ⟩ ★}
      → SpineValue V
      → Value U
      → RebaseAt W′ W Xᴸ Y
      → RebaseAt W₂ W′ X₂ Y₂
      → CTX.ImpEnvMono W W′
      → CTX.ImpEnvMono W′ W₂
      → CTX.SameCtx γ γ′
      → CTX.SameCtx γ′ γ₂
      → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
      → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
      → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
      → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
          ( RebaseAt Wᵒ W Xᴸ Y
          × CTX.ImpEnvMono W Wᵒ
          × CTX.SameCtx γ γᵒ
          × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
              (Wᵒ ∣ γᵒ ⊢²
                V ↓ seal Xᴸ (＇ X₂) ⊑ U ∶ qᵒ) )

H-Schain-from-chain : ChainRideInterface
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
  → CTX.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTX.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ (＇ Y₂)
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y (＇ Y₂) ∶ p₂
  → W ∣ γ ⊢²
      (V ⟨ c ⟩) ↓ seal Xᴸ ★
      ⊑ U ↓ seal Y (＇ Y₂) ∶ q
H-Schain-from-chain chain sv inert vU mono rb sc X∈ Y∈ D
    with ChainRideInterface.target-chain-ride chain
      sv inert vU mono rb sc X∈ Y∈ D
H-Schain-from-chain chain sv inert vU mono rb sc X∈ Y∈ D
    | Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , rᵒ , Dᵒ =
  CTI2.⊑conceal² monoᵒ (CTX.rebase-varᴿ rbᵒ) scᵒ
    (Conv.⊢↓-sealˣ Y∈) Dᵒ _

H-absorb-from-chain : ChainRideInterface
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
  → CTX.ImpEnvMono W W′
  → RebaseAt W′ W Xᴸ Y
  → CTX.SameCtx γ γ′
  → sourceStoreʷ W ∋ Xᴸ ⦂ ★
  → targetStoreʷ W ∋ Y ⦂ ★
  → W′ ∣ γ′ ⊢² V ⊑ U ↓ seal Y ★ ∶ p₂
  → RebaseAt W₂ W′ X₂ Y
  → CTX.ImpEnvMono W′ W₂
  → CTX.SameCtx γ′ γ₂
  → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
  → W ∣ γ ⊢²
      (V ⟨ c ⟩) ↓ seal Xᴸ ★
      ⊑ U ↓ seal Y ★ ∶ q
H-absorb-from-chain chain sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    with ChainRideInterface.target-chain-ride chain
      sv inert vU mono rb sc X∈ Y∈ D
H-absorb-from-chain chain sv inert vU mono rb sc X∈ Y∈ D
    link mono₂ sc₂ D₂ moved
    | Wᵒ , γᵒ , rbᵒ , monoᵒ , scᵒ , rᵒ , Dᵒ =
  CTI2.⊑conceal² monoᵒ (CTX.rebase-varᴿ rbᵒ) scᵒ
    (Conv.⊢↓-sealˣ Y∈) Dᵒ _

H-multi-from-chain : ChainRideInterface
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
  → CTX.ImpEnvMono W W′
  → CTX.ImpEnvMono W′ W₂
  → CTX.SameCtx γ γ′
  → CTX.SameCtx γ′ γ₂
  → sourceStoreʷ W ∋ Xᴸ ⦂ (＇ X₂)
  → W₂ ∣ γ₂ ⊢² V ⊑ U ∶ q₂
  → toRenameᵗ (ηᴸʷ W₂) X₂ ≢ toRenameᵗ (ηᴸʷ W′) X₂
  → Σ[ Wᵒ ∈ World Δᴸ Δᴿ Δ ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ W Xᴸ Y
      × CTX.ImpEnvMono W Wᵒ
      × CTX.SameCtx γ γᵒ
      × Σ[ qᵒ ∈ (＇ Xᴸ) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            V ↓ seal Xᴸ (＇ X₂) ⊑ U ∶ qᵒ) )
H-multi-from-chain chain sv vU rb link mono mono₂ sc sc₂ X∈ D moved =
  ChainRideInterface.source-chain-ride chain
    sv vU rb link mono mono₂ sc sc₂ X∈ D moved

ChainRideProbe-from-chain : ChainRideInterface
  → Σ[ Wᵒ ∈ World 2 1 3 ] Σ[ γᵒ ∈ CtxImp Wᵒ ]
      ( RebaseAt Wᵒ CRP.W₁ Fin.zero Fin.zero
      × CTX.ImpEnvMono CRP.W₁ Wᵒ
      × CTX.SameCtx {W = CRP.W₁} [] γᵒ
      × Σ[ qᵒ ∈ (＇ Fin.zero) ⊑ᵂ⟨ Wᵒ ⟩ ★ ]
          (Wᵒ ∣ γᵒ ⊢²
            CRP.V ↓ seal Fin.zero (＇ Fin.suc Fin.zero)
            ⊑ CRP.U ∶ qᵒ) )
ChainRideProbe-from-chain chain =
  ChainRideInterface.source-chain-ride chain
    (ECR.sv-seal (ECR.sv-cast (ECR.sv-$ (κℕ 0)) CTerms.inj))
    (CTerms.$ (κℕ 0) CTerms.《 CTerms.inj 》)
    CRP.raₗ CRP.link₂ CRP.probe-mono₁ₗ CRP.probe-monoₗ₂
    CRP.probe-same₁ₗ CRP.probe-sameₗ₂ CRP.probe-Z∋
    CRP.probe-premise CRP.probe-moved
