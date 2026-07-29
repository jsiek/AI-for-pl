module CompileInterpreterNarrowing where

-- File Charter:
--   * Public compiler-image and compiler-monotonicity boundary for the direct
--     interpreter proof.
--   * States the direct target relation explicitly.
--   * Delegates source-structural proofs to focused private modules.

open import Data.List using ([])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Compile using (compileᵀ)
open import CompileTermImprecision using (ctxImpToNu)
open import Ctx using (CtxWf)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import GradualTerms using (_∣_⊢_⦂_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import InterpreterTermNarrowing
import NuTerms as N
open import Types
import proof.CompileInterpreterNarrowingProof as Proof

compileᵀ-interpreter-term :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) →
  InterpreterTerm (proj₁ (compileᵀ hΓ M⊢))
compileᵀ-interpreter-term =
  Proof.compileᵀ-interpreter-term

compileᵀ-no-runtime-bullet :
  ∀ {Δ Γ M A} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) →
  N.No• (proj₁ (compileᵀ hΓ M⊢))
compileᵀ-no-runtime-bullet =
  Proof.compileᵀ-no-runtime-bullet

compileᵀ-raw-type-abstraction-value :
  ∀ {Δ Γ M A V} →
  (hΓ : CtxWf Δ Γ) →
  (M⊢ : Δ ∣ Γ ⊢ M ⦂ A) →
  proj₁ (compileᵀ hΓ M⊢) ≡ N.Λ V →
  N.Value V
compileᵀ-raw-type-abstraction-value =
  Proof.compileᵀ-raw-type-abstraction-value

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
