module CompileTermImprecision where

-- File Charter:
--   * Exposes the compiler monotonicity theorem at the public GTSF boundary.
--   * Relates gradual-term imprecision to quotiented Nu-term imprecision.
--   * Delegates the proof to `proof.CompileTermImprecision`.

open import Data.List using ([])
open import Data.Product using (proj₁)

open import Types
open import Ctx using (CtxWf)
open import Compile using (compileᵀ)
open import GradualTerms using (GTerm)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
import NuTermImprecision as NTI
open import QuotientedTermImprecision using
  (_∣_∣_∣_∣_⊢ᴺ_⊑_⦂_⊑_∶_)
import proof.CompileTermImprecision as Proof

variable
  Φ : ImpCtx
  Δᴸ Δᴿ : TyCtx
  γ : GTI.CtxImp Φ Δᴸ Δᴿ
  A B : Ty
  p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ
  M M′ : GTerm

ctxImpToNu :
  GTI.CtxImp Φ Δᴸ Δᴿ →
  NTI.CtxImp Φ Δᴸ Δᴿ
ctxImpToNu = Proof.ctxImpToNu

compile-preserves-term-imprecision :
  (srcΓ-wf : CtxWf Δᴸ (GTI.srcCtxⁱ γ)) →
  (tgtΓ-wf : CtxWf Δᴿ (GTI.tgtCtxⁱ γ)) →
  (M⊑M′ : Φ ∣ Δᴸ ∣ Δᴿ ∣ γ
    ⊢ᴳ M ⊑ M′ ⦂ A ⊑ B ∶ p) →
  let
    M⊢ = GTI.gradual-term-imprecision-source-typing M⊑M′
    M′⊢ = GTI.gradual-term-imprecision-target-typing M⊑M′
    N = proj₁ (compileᵀ srcΓ-wf M⊢)
    N′ = proj₁ (compileᵀ tgtΓ-wf M′⊢)
  in
  Φ ∣ Δᴸ ∣ Δᴿ ∣ [] ∣ ctxImpToNu γ
    ⊢ᴺ N ⊑ N′ ⦂ A ⊑ B ∶ p
compile-preserves-term-imprecision =
  Proof.compile-preserves-term-imprecision
