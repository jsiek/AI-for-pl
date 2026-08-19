module M5RelContinuationScratch where

-- File Charter:
--   * Notes scratch for the M5 right-instantiation relational
--     continuations.
--   * Splits the intended `InstCatchupRightAt` proof into one continuation
--     obligation per `AllValueView` constructor.
--   * Checks that those per-view obligations dispatch back to the live
--     fuel-indexed inst catch-up surface.
--   * Tooling note: check with `AGDA_DIR=/tmp/agda-work/agda-home agda
--     -i GTSFImp -i GTSFImp/proof/DGG/notes -v0
--     GTSFImp/proof/DGG/notes/M5RelContinuationScratch.agda`.

import Data.Fin as Fin
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Product using (Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Types
open import Consistency using
  (Env∼; _⊢_∼_; ∀ᶜ_; inst_; gen_; extᵐ; instᵐ; genᵐ)
open import Conversion using (Conv↑; Conv↓; `∀↑_; `∀↓_)
open import CastTerms using
  (Term; Value; GenSafe; _⟨_⟩; _↑_; _↓_; Λ_)
open import Reduction using (StoreChanges; _—↠[_]_)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; InstCatchupRightAt; FuelStepSurface)
open import proof.DGG.Inversion.SpineValueDef using
  (AllValueView; allv-Λ; allv-∀; allv-gen; allv-reveal; allv-conceal)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


record InstRelContinuationSurface (fuel : ℕ) : Set₁ where
  field
    fuel-step : FuelStepSurface fuel

    Λ-cont : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {V′ : Term (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
        {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
      → W ∣ γ ⊢² M ⊑ M′ ∶ p
      → Value M
      → Value M′
      → Value V′
      → M′ ≡ Λ V′
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → castSize ((inst c′) B′≢★) < fuel
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
        Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
          (Value N′
            × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
            × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
                ECR.transport⊑ᵂ ext q))

    ∀-cont : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : extᵐ ν₀ ⊢ B₀ ∼ B₁}
      → W ∣ γ ⊢² M ⊑ M′ ∶ p
      → Value M
      → Value M′
      → Value V′
      → M′ ≡ V′ ⟨ ∀ᶜ d ⟩
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → castSize ((inst c′) B′≢★) < fuel
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
        Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
          (Value N′
            × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
            × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
                ECR.transport⊑ᵂ ext q))

    gen-cont : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B C : Ty (suc Δᴿ)}
        {B₀ B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : genᵐ ν₀ ⊢ ⇑ᵗ B₀ ∼ C}
      → W ∣ γ ⊢² M ⊑ M′ ∶ p
      → Value M
      → Value M′
      → Value V′
      → ⦃ Cnv : NonVar C ⦄
      → ⦃ zero∈C : Fin.zero ∈ᵗ C ⦄
      → (B₀≢★ : B₀ ≢ ★)
      → GenSafe d
      → M′ ≡ V′ ⟨ (gen d) B₀≢★ ⟩
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → castSize ((inst c′) B′≢★) < fuel
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
        Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
          (Value N′
            × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
            × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
                ECR.transport⊑ᵂ ext q))

    reveal-cont : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↑ (suc Δᴿ) B₀ B₁}
      → W ∣ γ ⊢² M ⊑ M′ ∶ p
      → Value M
      → Value M′
      → Value V′
      → M′ ≡ V′ ↑ `∀↑ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → castSize ((inst c′) B′≢★) < fuel
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
        Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
          (Value N′
            × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
            × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
                ECR.transport⊑ᵂ ext q))

    conceal-cont : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↓ (suc Δᴿ) B₀ B₁}
      → W ∣ γ ⊢² M ⊑ M′ ∶ p
      → Value M
      → Value M′
      → Value V′
      → M′ ≡ V′ ↓ `∀↓ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → castSize ((inst c′) B′≢★) < fuel
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
        Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
        Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
        Σ[ N′ ∈ Term Δᴿ′ ]
          (Value N′
            × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
            × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
                ECR.transport⊑ᵂ ext q))


inst-catchup-rel-scratch : ∀ {fuel}
  → InstRelContinuationSurface fuel
  → InstCatchupRightAt fuel
inst-catchup-rel-scratch rel M⊑M′ vM vM′
    (allv-Λ vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.Λ-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel-scratch rel M⊑M′ vM vM′
    (allv-∀ vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.∀-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel-scratch rel M⊑M′ vM vM′
    (allv-gen vV′ B₀≢★ safe eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.gen-cont rel
    M⊑M′ vM vM′ vV′ B₀≢★ safe eq c′ B′≢★ c<fuel q
inst-catchup-rel-scratch rel M⊑M′ vM vM′
    (allv-reveal vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.reveal-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
inst-catchup-rel-scratch rel M⊑M′ vM vM′
    (allv-conceal vV′ eq) c′ B′≢★ c<fuel q =
  InstRelContinuationSurface.conceal-cont rel
    M⊑M′ vM vM′ vV′ eq c′ B′≢★ c<fuel q
