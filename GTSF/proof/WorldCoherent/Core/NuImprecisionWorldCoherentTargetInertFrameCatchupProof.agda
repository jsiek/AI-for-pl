module proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetInertFrameCatchupProof where

-- File Charter:
--   * Proves target-inert-frame world-coherent catch-up by dispatching the
--     explicit target evidence alternatives from the statement.
--   * Delegates each reveal, conceal, narrowing, widening, and identity-mode
--     widening case to the strict focused prefix-frame theorem.
--   * Contains no recursive dispatcher, semantic leaf proof, or compatibility
--     shim.

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import proof.WorldCoherent.Core.NuImprecisionWorldCoherentCatchupPrefixFrames using
  ( world-coherent-left-catchup-prefix-target-conceal-castᵀ
  ; world-coherent-left-catchup-prefix-target-narrow-castᵀ
  ; world-coherent-left-catchup-prefix-target-reveal-castᵀ
  ; world-coherent-left-catchup-prefix-target-widen-castᵀ
  ; world-coherent-left-catchup-prefix-target-widen-id-castᵀ
  )
open import
  proof.WorldCoherent.Core.NuImprecisionWorldCoherentTargetInertFrameCatchupDef using
  (WorldCoherentTargetInertFrameCatchupᵀ)


world-coherent-target-inert-frame-catchup-proofᵀ :
  WorldCoherentTargetInertFrameCatchupᵀ
world-coherent-target-inert-frame-catchup-proofᵀ
    prefix _ (inj₁ (_ , _ , _ , c↑)) catchup =
  world-coherent-left-catchup-prefix-target-reveal-castᵀ prefix c↑ catchup
world-coherent-target-inert-frame-catchup-proofᵀ
    prefix _ (inj₂ (inj₁ (_ , _ , _ , c↓))) catchup =
  world-coherent-left-catchup-prefix-target-conceal-castᵀ prefix c↓ catchup
world-coherent-target-inert-frame-catchup-proofᵀ
    prefix _ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊒)))) catchup =
  world-coherent-left-catchup-prefix-target-narrow-castᵀ
    prefix mode seal★ c⊒ catchup
world-coherent-target-inert-frame-catchup-proofᵀ
    prefix _ (inj₂ (inj₂ (inj₂ (inj₁ (_ , mode , seal★ , c⊑))))) catchup =
  world-coherent-left-catchup-prefix-target-widen-castᵀ
    prefix mode seal★ c⊑ catchup
world-coherent-target-inert-frame-catchup-proofᵀ
    prefix _ (inj₂ (inj₂ (inj₂ (inj₂ (seal★ , c⊑))))) catchup =
  world-coherent-left-catchup-prefix-target-widen-id-castᵀ
    prefix seal★ c⊑ catchup
