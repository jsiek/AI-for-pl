module proof.DGG.SimConcealRevealPeel where

-- File Charter:
--   * States the D2b two-sided conceal/reveal peel interfaces.
--   * Records the source-only variant's required evidence that the target
--     value was already opened by a target conceal/reveal keep step.
--   * Does not derive parked evidence or change CTI2.

open import Types using (Ty; TyCtx; TyVar)
open import Conversion using (seal; unseal)
open import CastTerms using (Term; Value; _↑_; _↓_)
open import Reduction using (keep; _—→[_]_)
import proof.DGG.CastTermImprecision2 as CTI2
open CTI2 using
  ( World
  ; CtxImp
  ; _⊑ᵂ⟨_⟩_
  ; _∣_⊢²_⊑_∶_
  )


PairedConcealRevealPeelᵀ : Set
PairedConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → Value V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → ((V₀′ ↓ seal Xᴿ R′) ↑ unseal Xᴿ R′) —→[ keep ] V₀′
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q


record TargetOpenedByConcealReveal {Δᴿ : TyCtx}
    (N : Term Δᴿ) (X : TyVar Δᴿ) (R′ : Ty Δᴿ)
    (V′ : Term Δᴿ) : Set where
  field
    opened-value : Value V′
    opened-step :
      ((N ↓ seal X R′) ↑ unseal X R′) —→[ keep ] V′


SourceOnlyConcealRevealPeelᵀ : Set
SourceOnlyConcealRevealPeelᵀ =
  ∀ {Δᴸ Δᴿ Δ}
    {W : World Δᴸ Δᴿ Δ} {γ : CtxImp W}
    {V₀ : Term Δᴸ} {N′ V₀′ : Term Δᴿ}
    {Xᴸ : TyVar Δᴸ} {Xᴿ : TyVar Δᴿ}
    {R : Ty Δᴸ} {R′ : Ty Δᴿ}
    {q : R ⊑ᵂ⟨ W ⟩ R′}
  → Value V₀
  → TargetOpenedByConcealReveal N′ Xᴿ R′ V₀′
  → W ∣ γ ⊢²
      ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R)
      ⊑ V₀′ ∶ q
  → ((V₀ ↓ seal Xᴸ R) ↑ unseal Xᴸ R) —→[ keep ] V₀
  → W ∣ γ ⊢² V₀ ⊑ V₀′ ∶ q
