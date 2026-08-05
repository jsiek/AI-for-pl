module proof.CompileInterpreterNarrowingProof where

-- File Charter:
--   * EXPERIMENTAL after the 2026-08-04 origin merge: O35 must rebuild this
--     packaging step from a live-QTI synchronized compiler certificate.
--   * Packages the intrinsically aligned compiler certificate as an open
--     interpreter-term narrowing.
--   * Delegates the sole source induction to compiler monotonicity.
--   * Contains no independent compiler-image or cast-plan computation.

open import Data.List using ([])
open import Data.Product using (proj₁)

open import Compile using (compileᵀ)
open import CompileTermImprecision using
  (compile-preserves-term-imprecision; ctxImpToNu)
open import Ctx using (CtxWf)
import GradualTermImprecision as GTI
open import GradualTermImprecision using
  (_∣_∣_∣_⊢ᴳ_⊑_⦂_⊑_∶_)
open import ImprecisionWf using
  (ImpCtx; _∣_⊢_⊑_⊣_)
open import Narrowing.InterpreterTermNarrowingCore
open import Types

open RelatedWorlds

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
    empty-world⊑ Φ Δᴸ Δᴿ [] (ctxImpToNu γ)
    N N′ A B p
compile-preserves-interpreter-narrowing
    srcΓ-wf tgtΓ-wf M⊑M′ =
  open-interpreter-narrowing
    (compile-preserves-term-imprecision
      srcΓ-wf tgtΓ-wf M⊑M′)
