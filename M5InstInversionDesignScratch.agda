module M5InstInversionDesignScratch where

-- File Charter:
--   * Root-level scratch for the M5 target-instantiation inversion design.
--   * States the package a future polymorphic-target inversion theorem must
--     deliver for each `AllValueView` branch.
--   * Checks that such packages project mechanically to the live
--     `InstRelContinuationSurface`, without adding live proof code.

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
open import Reduction using (StoreChanges; _—↠[_]_; applyTys)

import proof.DGG.CastTermImprecision2 as CTI2
import proof.DGG.ExtraCastRight2 as ECR
open import proof.DGG.Catchup.InstCatchupRightDef using
  (InstCastAllocPrefixᵀ; AllValueViewStepCatalogᵀ)
open import proof.DGG.Catchup.InstCatchupRightRelDef using
  (InstRelContinuationSurface)
open import proof.DGG.Catchup.ValueCatchupRightDef using
  (CatchupCast⁻; Catchup⁻Embedᵀ; FuelStepSurface;
   inst-alloc-decreaseᵀ; castSize)
open CTI2 using (World; CtxImp; _⊑ᵂ⟨_⟩_; _∣_⊢²_⊑_∶_)


record InstSpineDescentPackage {Δᴸ Δᴿ Δ}
    (W : World Δᴸ Δᴿ Δ)
    (γ : CtxImp W)
    (M : Term Δᴸ)
    {A : Ty Δᴸ} {B : Ty Δᴿ}
    (post : Term Δᴿ)
    (p : A ⊑ᵂ⟨ W ⟩ B) : Set₁ where
  field
    Δᴿ′ : TyCtx
    χs : StoreChanges Δᴿ Δᴿ′
    Δ′ : TyCtx
    W′ : World Δᴸ Δᴿ′ Δ′
    ext : ECR.WorldExtendᴿ χs W W′
    final : Term Δᴿ′
    final-value : Value final
    post-reduction : post —↠[ χs ] final
    final-relation :
      W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ final ∶
        ECR.transport⊑ᵂ ext p


record InstPostCatalogPackage (fuel : ℕ)
    {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W}
    {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
    {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
    (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
    (vM : Value M)
    (vM′ : Value M′)
    (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
    ⦃ Bnv : NonVar B ⦄
    ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
    (B′≢★ : B′ ≢ ★)
    (c<fuel : castSize ((inst c′) B′≢★) < fuel)
    (q : A ⊑ᵂ⟨ W ⟩ B′) : Set₁ where
  field
    Δᴿ₂ : TyCtx
    χs₂ : StoreChanges Δᴿ Δᴿ₂
    Δ₂ : TyCtx
    W₂ : World Δᴸ Δᴿ₂ Δ₂
    ext₂ : ECR.WorldExtendᴿ χs₂ W W₂
    B₂ : Ty Δᴿ₂
    post : Term Δᴿ₂
    p₂ : A ⊑ᵂ⟨ W₂ ⟩ B₂
    post-relation :
      W₂ ∣ ECR.mapCtxᴿ ext₂ γ ⊢² M ⊑ post ∶ p₂
    ν₂ : Env∼ Δᴿ₂
    residual-cast : ν₂ ⊢ B₂ ∼ applyTys χs₂ B′
    residual-provenance :
      CatchupCast⁻ {W = W₂} {A = A} p₂ residual-cast
        (ECR.transport⊑ᵂ ext₂ q)
    spine-descent :
      InstSpineDescentPackage W₂ (ECR.mapCtxᴿ ext₂ γ) M post p₂
    finish :
      Σ[ Δᴿ′ ∈ TyCtx ] Σ[ χs ∈ StoreChanges Δᴿ Δᴿ′ ]
      Σ[ Δ′ ∈ TyCtx ] Σ[ W′ ∈ World Δᴸ Δᴿ′ Δ′ ]
      Σ[ ext ∈ ECR.WorldExtendᴿ χs W W′ ]
      Σ[ N′ ∈ Term Δᴿ′ ]
        (Value N′
          × (M′ ⟨ (inst c′) B′≢★ ⟩ —↠[ χs ] N′)
          × (W′ ∣ ECR.mapCtxᴿ ext γ ⊢² M ⊑ N′ ∶
              ECR.transport⊑ᵂ ext q))


record InstInversionPackage (fuel : ℕ) : Set₁ where
  field
    fuel-step : FuelStepSurface fuel
    inst-prefix : InstCastAllocPrefixᵀ
    all-value-step-catalog : AllValueViewStepCatalogᵀ
    inst-alloc-decrease : inst-alloc-decreaseᵀ
    catchup⁻-embed : Catchup⁻Embedᵀ

    Λ-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ : Term Δᴿ} {V′ : Term (suc Δᴿ)}
        {A : Ty Δᴸ} {B : Ty (suc Δᴿ)} {B′ : Ty Δᴿ}
        {ν : Env∼ Δᴿ} {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ Λ V′
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    ∀-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : extᵐ ν₀ ⊢ B₀ ∼ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ⟨ ∀ᶜ d ⟩
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    gen-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B C : Ty (suc Δᴿ)}
        {B₀ B′ : Ty Δᴿ} {ν ν₀ : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : genᵐ ν₀ ⊢ ⇑ᵗ B₀ ∼ C}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
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
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    reveal-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↑ (suc Δᴿ) B₀ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ↑ `∀↑ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q

    conceal-package : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
        {γ : CtxImp W}
        {M : Term Δᴸ} {M′ V′ : Term Δᴿ}
        {A : Ty Δᴸ} {B B₀ B₁ : Ty (suc Δᴿ)}
        {B′ : Ty Δᴿ} {ν : Env∼ Δᴿ}
        {p : A ⊑ᵂ⟨ W ⟩ `∀ B}
        {d : Conv↓ (suc Δᴿ) B₀ B₁}
      → (rel : W ∣ γ ⊢² M ⊑ M′ ∶ p)
      → (vM : Value M)
      → (vM′ : Value M′)
      → Value V′
      → M′ ≡ V′ ↓ `∀↓ d
      → (c′ : instᵐ ν ⊢ B ∼ ⇑ᵗ B′)
      → ⦃ Bnv : NonVar B ⦄
      → ⦃ zero∈B : Fin.zero ∈ᵗ B ⦄
      → (B′≢★ : B′ ≢ ★)
      → (c<fuel : castSize ((inst c′) B′≢★) < fuel)
      → (q : A ⊑ᵂ⟨ W ⟩ B′)
      → InstPostCatalogPackage fuel rel vM vM′ c′ B′≢★ c<fuel q


inst-inversion→rel-surface : ∀ {fuel}
  → InstInversionPackage fuel
  → InstRelContinuationSurface fuel
inst-inversion→rel-surface pkg = record
  { fuel-step = InstInversionPackage.fuel-step pkg
  ; inst-prefix = InstInversionPackage.inst-prefix pkg
  ; all-value-step-catalog =
      InstInversionPackage.all-value-step-catalog pkg
  ; inst-alloc-decrease = InstInversionPackage.inst-alloc-decrease pkg
  ; catchup⁻-embed = InstInversionPackage.catchup⁻-embed pkg
  ; Λ-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.Λ-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; ∀-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.∀-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; gen-cont = λ rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★
      c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.gen-package pkg
          rel vM vM′ vV′ B₀≢★ safe eq c′ B′≢★ c<fuel q)
  ; reveal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.reveal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  ; conceal-cont = λ rel vM vM′ vV′ eq c′ B′≢★ c<fuel q →
      InstPostCatalogPackage.finish
        (InstInversionPackage.conceal-package pkg
          rel vM vM′ vV′ eq c′ B′≢★ c<fuel q)
  }
