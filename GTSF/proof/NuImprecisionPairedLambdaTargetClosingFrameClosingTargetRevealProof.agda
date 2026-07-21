module
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealProof
  where

-- File Charter:
--   * Reduces target-only inert reveal-frame closing to its exact fused core.
--   * Exhaustively inverts reveal provenance and inertness, then inverts the
--     source-universal type-imprecision indices forced by function and
--     universal target endpoints.
--   * Identity and unseal reveals are excluded by inertness; function reveals
--     and universal reveals with a source-allocation result index contradict
--     the supplied fresh-path-cycle theorem.
--   * The fused core retains only the two universal cases whose result index
--     is structural, with the final paired all-to-all conversion reduced to
--     reveal/reveal or conceal/conceal body provenance.
--   * Contains no concrete core implementation, postulate, hole, permissive
--     option, catch-all case, recursive frame-closing dependency, or broad
--     simulation import.

import Coercions as C
import Conversion as CV
import QuotientedTermImprecision as Q
open import Coercions using (Coercion)
open import Data.Empty using (⊥-elim)
open import Data.List using (_∷_)
open import Data.Nat using (suc; zero)
open import ImprecisionWf using
  ( ImpCtx
  ; _ˣ⊑ˣ_
  ; ⇑ᵢ
  ; _∣_⊢_⊑_⊣_
  ; ∀ⁱ_
  ; ν
  )
open import NuTermImprecision using (StoreImp)
open import QuotientedTermImprecision using (PairedConversion)
open import Types using (Ty; TyCtx; `∀)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetFrameCasesDef
  using (PairedLambdaTargetClosingFrameClosingTargetRevealᵀ)
open import
  proof.NuImprecisionPairedLambdaTargetClosingFrameClosingTargetRevealCoreDef
  using
  ( PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ
  ; PairedLambdaTargetClosingPairedAllConversionView
  ; paired-all-conceal
  ; paired-all-reveal
  ; target-reveal-all-∀∀
  ; target-reveal-all-ν∀
  )
open import
  proof.NuImprecisionPairedUniversalConversionFreshPathCycleDef
  using (PairedUniversalConversionFreshPathCycleᵀ)


paired-lambda-target-closing-paired-all-conversion-viewᵀ :
  ∀ {Φ : ImpCtx} {Δᴸ Δᴿ : TyCtx}
    {ρ : StoreImp Φ Δᴸ Δᴿ} {c c′ : Coercion}
    {A A′ B B′ : Ty}
    {p : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ A ⊑ A′ ⊣ suc Δᴿ}
    {q : ((zero ˣ⊑ˣ zero) ∷ ⇑ᵢ Φ)
      ∣ suc Δᴸ ⊢ B ⊑ B′ ⊣ suc Δᴿ} →
  PairedConversion Φ Δᴸ Δᴿ ρ (C.`∀ c) c′
    {`∀ A} {`∀ A′} {`∀ B} {`∀ B′} (∀ⁱ p) (∀ⁱ q) →
  PairedLambdaTargetClosingPairedAllConversionView
    Φ Δᴸ Δᴿ ρ c c′ (∀ⁱ p) (∀ⁱ q)
paired-lambda-target-closing-paired-all-conversion-viewᵀ
    (Q.paired-reveal corr (CV.reveal-all source)
      (CV.reveal-all target)) =
  paired-all-reveal corr source target
paired-lambda-target-closing-paired-all-conversion-viewᵀ
    (Q.paired-conceal corr (CV.conceal-all source)
      (CV.conceal-all target)) =
  paired-all-conceal corr source target


paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ :
  PairedUniversalConversionFreshPathCycleᵀ →
  PairedLambdaTargetClosingFrameClosingTargetRevealCoreᵀ →
  PairedLambdaTargetClosingFrameClosingTargetRevealᵀ
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core inner view () (CV.reveal-id-var hY ok)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core inner view () CV.reveal-id-base
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core inner view () CV.reveal-id-★
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core inner view () (CV.reveal-unseal hX αX∈Σ ok)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core {q = ν occ-q q-body} {r = ν occ-r r-body}
    inner view (s C.↦ t) (CV.reveal-fun s↓ t↑)
    prefix h⇑A final-reveal liftν lift∀ conversion =
  ⊥-elim (cycle occ-r conversion)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core {q = ∀ⁱ q-body} {r = ∀ⁱ r-body}
    inner view (C.`∀ d) (CV.reveal-all reveal)
    prefix h⇑A final-reveal liftν lift∀ conversion =
  core inner view (target-reveal-all-∀∀ reveal)
    prefix h⇑A final-reveal liftν lift∀
    (paired-lambda-target-closing-paired-all-conversion-viewᵀ
      conversion)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core {q = ∀ⁱ q-body} {r = ν occ-r r-body}
    inner view (C.`∀ d) (CV.reveal-all reveal)
    prefix h⇑A final-reveal liftν lift∀ conversion =
  ⊥-elim (cycle occ-r conversion)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core {q = ν occ-q q-body} {r = ∀ⁱ r-body}
    inner view (C.`∀ d) (CV.reveal-all reveal)
    prefix h⇑A final-reveal liftν lift∀ conversion =
  core inner view (target-reveal-all-ν∀ reveal)
    prefix h⇑A final-reveal liftν lift∀
    (paired-lambda-target-closing-paired-all-conversion-viewᵀ
      conversion)
paired-lambda-target-closing-frame-closing-target-reveal-proofᵀ
    cycle core {q = ν occ-q q-body} {r = ν occ-r r-body}
    inner view (C.`∀ d) (CV.reveal-all reveal)
    prefix h⇑A final-reveal liftν lift∀ conversion =
  ⊥-elim (cycle occ-r conversion)
