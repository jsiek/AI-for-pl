module proof.DGG.SealChain where

-- File Charter:
--   * Names the checked branch-dependent seal-chain package shapes.
--   * The requested theorem bodies are intentionally not exported here:
--     SourceStarRideCounterScratch refutes the requested source-star
--     variable branch package at the exact scratch interface.
--   * Does not change the live imprecision relation or rebase invariants.

open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore using (_∋_⦂_)
open import Conversion using (seal)
open import CastTerms using (Term; Value; _↓_)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  (World; CtxImp; RebaseAt; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_;
   sourceStoreʷ; targetStoreʷ)

------------------------------------------------------------------------
-- Branch-dependent ride packages
------------------------------------------------------------------------

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
