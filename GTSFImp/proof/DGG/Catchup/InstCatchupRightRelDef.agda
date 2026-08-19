module proof.DGG.Catchup.InstCatchupRightRelDef where

-- File Charter:
--   * States the M5 right-instantiation relational continuation surface.
--   * Keeps the live proof file to a dispatcher over one continuation per
--     target polymorphic value view.
--   * Carries the M5 operational catalog and M6 fuel/support inputs that
--     each per-view continuation is expected to consume.
--   * Depends only on core syntax/reduction, the catch-up Def surfaces, and
--     the stage-1 DGG world-extension interface.

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

import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.InstCatchupRightDef using
  (InstCastAllocPrefixᵀ; AllValueViewStepCatalogᵀ)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (castSize; InstCatchupRightAt; FuelStepSurface;
   inst-alloc-decreaseᵀ; ResidualCastBuilderᵀ)
open CTX using
  (World;
   CtxImp;
   _⊑ᵂ⟨_⟩_)
open CTI2 using (_∣_⊢²_⊑_∶_)


-- These fields are deliberately not aliases for theorem conclusions:
-- they are the five missing relational continuations.  Each field owns the
-- full `InstCatchupRightAt` result for its view after using the common
-- allocation prefix, the view-step catalog, and the smaller fuel worker.

record InstRelContinuationSurface (fuel : ℕ) : Set₁ where
  field
    fuel-step : FuelStepSurface fuel
    inst-prefix : InstCastAllocPrefixᵀ
    all-value-step-catalog : AllValueViewStepCatalogᵀ
    inst-alloc-decrease : inst-alloc-decreaseᵀ
    residual-cast-builder : ResidualCastBuilderᵀ

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
