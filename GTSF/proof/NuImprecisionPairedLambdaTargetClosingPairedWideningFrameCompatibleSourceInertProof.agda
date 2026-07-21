module
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertProof
  where

-- File Charter:
--   * Reduces the compatible-source-inert paired-widening branch to its exact
--     body-widening core by exhaustive inversion of source and target inert
--     widening evidence and final paired-conversion provenance.
--   * The source is forced to a structural universal body; target widenings
--     reduce to tag, function, or universal bodies, and paired conversions
--     reduce to source-universal reveal or conceal bodies.
--   * Contains no concrete core implementation, postulate, hole, permissive
--     option, recursive frame-closing dependency, or broad simulation import.

import Coercions as C
import Conversion as CV
import NarrowWiden as NW
import QuotientedTermImprecision as Q
open import Coercions using (Coercion; Inert; ModeEnv)
open import Data.Product using (_,_)
open import ImprecisionWf using
  ( ImpCtx
  ; _∣_⊢_⊑_⊣_
  )
open import NarrowWiden using (_∣_∣_⊢_∶_⊑_)
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Store; Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleCasesDef
  using
  (PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreDef
  using
  ( PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ
  ; PairedSourceAllConversionView
  ; PairedWideningTargetInertView
  ; inert-all
  ; inert-fun
  ; inert-tag
  ; source-all-conceal
  ; source-all-reveal
  )


paired-widening-target-inert-viewᵀ :
  ∀ {μ : ModeEnv} {Δ : TyCtx} {Σ : Store}
    {d : Coercion} {A B : Ty} →
  Inert d →
  μ ∣ Δ ∣ Σ ⊢ d ∶ A ⊑ B →
  PairedWideningTargetInertView μ Δ Σ d A B
paired-widening-target-inert-viewᵀ
    (G C.!) (C.cast-tag hG gG ok , NW.tag _) =
  inert-tag hG gG ok
paired-widening-target-inert-viewᵀ
    (C.seal A α) (_ , NW.cross ())
paired-widening-target-inert-viewᵀ
    (s C.↦ t)
    (C.cast-fun s⊢ t⊢ , NW.cross (sⁿ NW.↦ tʷ)) =
  inert-fun (s⊢ , sⁿ) (t⊢ , tʷ)
paired-widening-target-inert-viewᵀ
    (C.`∀ d) (C.cast-all d⊢ , NW.cross (NW.`∀ dʷ)) =
  inert-all (d⊢ , dʷ)
paired-widening-target-inert-viewᵀ
    (C.gen A d) (_ , NW.cross ())


paired-source-all-conversion-viewᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : Φ ∣ Δᴸ ⊢ `∀ A ⊑ A′ ⊣ Δᴿ}
    {q : Φ ∣ Δᴸ ⊢ `∀ B ⊑ B′ ⊣ Δᴿ} →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′ p q →
  PairedSourceAllConversionView Φ Δᴸ Δᴿ ρ c c′ p q
paired-source-all-conversion-viewᵀ
    (Q.paired-reveal corr (CV.reveal-all source) target) =
  source-all-reveal corr source target
paired-source-all-conversion-viewᵀ
    (Q.paired-conceal corr (CV.conceal-all source) target) =
  source-all-conceal corr source target


paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ :
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertCoreᵀ →
  PairedLambdaTargetClosingPairedWideningFrameCompatibleSourceInertᵀ
paired-lambda-target-closing-paired-widening-frame-compatible-source-inert-proofᵀ
    core inner view inert-d′ cast-mode seal
    (C.cast-all d⊢ , NW.cross (NW.`∀ dʷ))
    target-mode target-seal target-widening (C.`∀ ._) =
  λ prefix coherent exclusive wfL h⇑A reveal liftν lift∀ conversion →
    core inner view cast-mode seal (d⊢ , dʷ)
      target-mode target-seal
      (paired-widening-target-inert-viewᵀ inert-d′ target-widening)
      prefix coherent exclusive wfL h⇑A reveal liftν lift∀
      (paired-source-all-conversion-viewᵀ conversion)
