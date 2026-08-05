module Narrowing.CompileInterpreterNarrowing where

-- File Charter:
--   * EXPERIMENTAL after the 2026-08-04 origin merge: its O11 certificate
--     still targets the retired compiler relation and is tracked by O35.
--   * Public compiler-image and compiler-monotonicity boundary for the direct
--     interpreter proof.
--   * States the direct target relation explicitly, including its intrinsic
--     shape/static alignment certificate.
--   * Delegates the sole source induction to GTSF compiler monotonicity.

open import Data.List using ([])
open import Data.Product using (proj₁)

open import Compile using (compileᵀ)
open import CompileTermImprecision using (ctxImpToNu)
open import Ctx using (CtxWf)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterTermNarrowing
open import Types
import proof.CompileInterpreterNarrowingProof as Proof

compile-preserves-interpreter-narrowing :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {γ : GTI.CtxImp Φ Δᴸ Δᴿ}
    {M M′ A B}
    {p : Φ ∣ Δᴸ ⊢ A ⊑ B ⊣ Δᴿ} →
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
  OpenInterpreterTermNarrowing
    RelatedWorlds.empty-world⊑
    Φ Δᴸ Δᴿ [] (ctxImpToNu γ)
    N N′ A B p
compile-preserves-interpreter-narrowing =
  Proof.compile-preserves-interpreter-narrowing
